#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
import logging
from multiprocessing import Process, Queue, Pipe

from pysmt.solvers.solver import IncrementalTrackingSolver, SolverOptions
from pysmt.decorators import clear_pending_pop


LOGGER = logging.getLogger(__name__)
_debug = LOGGER.debug


class PortfolioOptions(SolverOptions):

    def __init__(self, **base_options):
        SolverOptions.__init__(self, **base_options)
        self.exit_on_exception = False
        for k,v in self.solver_options.items():
            if k == "exit_on_exception":
                if v not in (True, False):
                    raise ValueError("Invalid value for %s: %s" % \
                                     (str(k),str(v)))
            else:
                raise ValueError("Unrecognized option '%s'." % k)
            # Store option
            setattr(self, k, v)

    def __call__(self, solver):
        pass

# EOC PortfolioOptions


class Portfolio(IncrementalTrackingSolver):
    """Create a portfolio instance of multiple Solvers."""
    OptionsClass = PortfolioOptions

    def __init__(self, solvers_set, environment, logic, **options):
        """Creates a portfolio using the specified solvers.

        Solver_set is an iterable. Elements of solver_set can be
         1) a name of a solver
         2) a tuple containing a name of a solver and dict of options

        E.g.,
           Portfolio(["msat", "z3"], incremental=True)
              or
           Porfolio([("msat", {"random_seed": 1}), ("msat", {"random_seed": 2})],
                     incremental=True)

        Options specified in the Portfolio are shared among all
        solvers, e.g., in the first example all solvers will receive
        the option 'incremental=True'.

        One process will be used for each of the solvers.
        """
        IncrementalTrackingSolver.__init__(self,
                                           environment=environment,
                                           logic=logic,
                                           **options)
        self.solvers = []
        self._process_solver_set(solvers_set)
        # Check that the names are valid ?
        all_solvers = set(self.environment.factory.all_solvers())
        not_found = set(s for s,_ in self.solvers) - all_solvers
        if len(not_found) != 0:
            raise ValueError("Cannot find solvers %s" % not_found)

        # After Solving, we only keep the solver that finished first.
        # We can extract models from the solver, unsat cores, etc
        self._ext_solver = None # Existing solver Process
        self._ctrl_pipe = None  # Ctrl Pipe to the existing solver

    def _process_solver_set(self, sset):
        """The sset can contain both solver names and pairs name options."""
        global_opts = self.options.as_kwargs()
        # Remove solver_options from global_opts. These are the
        # Portfolio specific options and might not make sense for the
        # solvers.
        del global_opts["solver_options"]
        for elem in sset:
            if type(elem) is str:
                sname = elem
                opts = global_opts
            else:
                sname, local_opts = elem
                opts = dict(global_opts)
                for k,v in local_opts.items():
                    # local_opts has priority over global_opts
                    opts[k] = v
            self.solvers.append((sname, opts))

    def _reset_assertions(self):
        pass

    @clear_pending_pop
    def _add_assertion(self, formula, named=None):
        return formula

    @clear_pending_pop
    def _push(self, levels=1):
        pass

    @clear_pending_pop
    def _pop(self, levels=1):
        pass

    @clear_pending_pop
    def _solve(self, assumptions=None):
        # We destroy the last solver before solving again. Note: We
        # might be able to do something smarter by keeping track of
        # the state of the solver. This, however, requires more
        # booking (e.g., we need to assert expressions incrementaly,
        # instead of in one shot!)
        self._close_existing()

        formula = self.environment.formula_manager.And(self.assertions)
        _debug("Creating Queue and Pipe")
        signaling_queue = Queue()
        child_ctrl_pipe, my_ctrl_pipe = Pipe()
        self._ctrl_pipe = my_ctrl_pipe

        processes = []
        for idx, (sname, opts) in enumerate(self.solvers):
            _debug("Creating instance of %s", sname)
            options = opts
            _p = Process(name="%d (%s)" % (idx, sname),
                         target=_run_solver,
                         args=("%d (%s)" % (idx, sname),
                               sname, options, formula,
                               signaling_queue, child_ctrl_pipe))
            processes.append(_p)
            _p.start()
            _debug("Started instance of %s", sname)

        while True:
            (sname, res) = signaling_queue.get(block=True)
            if isinstance(res, BaseException):
                if self.options.exit_on_exception:
                    # Close all solvers and raise exception
                    for p in processes:
                        p.terminate()
                    raise res
                else:
                    continue
            else:
                assert type(res) is bool, type(res)
                break
        _debug("Solver %s finished first saying %s", sname, res)
        # Kill all processes, except for the "winner"
        for p in processes:
            if p.name == sname:
                self._ext_solver = p
            else:
                p.terminate()

        return res

    def get_value(self, formula):
        if not self._ext_solver:
            raise ValueError("No SAT model")

        self._ctrl_pipe.send(("get_value", formula))
        res = self._ctrl_pipe.recv()
        return self.environment.formula_manager.normalize(res)

    def get_model(self):
        from pysmt.solvers.eager import EagerModel

        if not self._ext_solver:
            raise ValueError("No SAT model")

        self._ctrl_pipe.send("get_model")
        # Contextualize the result within the calling process
        _normalize = self.environment.formula_manager.normalize
        model_list = self._ctrl_pipe.recv()
        model = {}
        for k,v in model_list:
            _k, _v = _normalize(k), _normalize(v)
            model[_k] = _v

        return EagerModel(model)

    def _close_existing(self):
        _debug("Closing resources..")
        if self._ctrl_pipe :
            self._ctrl_pipe.send("exit")
            self._ctrl_pipe = None
        if self._ext_solver and self._ext_solver.is_alive():
            self._ext_solver.terminate()
            _debug("Previous solver killed")

    def _exit(self):
        self._close_existing()

# EOC Portfolio

# Function to pass to the solver
def _run_solver(idx, solver, options, formula, signaling_queue, ctrl_pipe):
    """Function used by the child Process to handle Portfolio requests.

    solver  : name of the solver
    options : options for the solver
    formula : formula to assert
    signaling_queue: queue in which to write to indicate completion of solve
    ctrl_pipe: Pipe to communicate with parent process *after* solve
    """
    from pysmt.environment import get_env

    Solver = get_env().factory.Solver
    with Solver(name=solver, **options) as s:
        s.add_assertion(formula)
        try:
            local_res = s.solve()
        except Exception as ex:
            signaling_queue.put((solver, ex))
            return

        signaling_queue.put((idx, local_res))
        _exit = False
        while not _exit:
            try:
                cmd = ctrl_pipe.recv()
            except EOFError:
                break
            if type(cmd) == tuple:
                cmd, args = cmd
            if cmd == "exit":
                _exit = True
            elif cmd == "get_model":
                # MG: Can we pickle the EagerModel directly?
                # Note: contextualization happens on the receiver side
                model = list(s.get_model())
                ctrl_pipe.send(model)
            elif cmd == "get_value":
                args = get_env().formula_manager.normalize(args)
                ctrl_pipe.send(s.get_value(args))
            else:
                raise ValueError("Unknown command '%s'" % cmd)
