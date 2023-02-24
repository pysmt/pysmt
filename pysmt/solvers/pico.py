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
from pysmt.exceptions import SolverAPINotFound

try:
    import picosat
except ImportError:
    raise SolverAPINotFound

import pysmt.logics
from pysmt import typing as types
from pysmt.solvers.solver import Solver, SolverOptions
from pysmt.solvers.eager import EagerModel
from pysmt.rewritings import CNFizer
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.exceptions import ConvertExpressionError, PysmtValueError
from pysmt.constants import is_python_integer


class PicosatOptions(SolverOptions):
    """Options for Picosat Solver.

    * preprocessing: True, False
      Enable pre-processing

    * enable_trace_generation: True, False
      Enable trace generations (needed for UNSAT-cores)

    * output: None, Filename
      Define where to print output (default: None = stdout)

    * global_default_phase: None, ALL_GLOBAL_DEFAULT_PHASE
      Default phase for new decision literals.

    * more_important_lit: None, list of Symbols
      Increase the priority of the literals on which to make decisions

    * less_important_lit: None, list of Symbols
      Decrease the priority of the literals on which to make decisions

    * propagation_limit: None, long
      Limit the search to at most this many propagations.

    * verbosity: Integer
      Verbosity level. Set to 1 if output is defined.
    """
    ALL_GLOBAL_DEFAULT_PHASE = range(4)
    GLOBAL_DEFAULT_PHASE_FALSE, \
    GLOBAL_DEFAULT_PHASE_TRUE, \
    GLOBAL_DEFAULT_PHASE_JEROSLOW_WANG, \
    GLOBAL_DEFAULT_PHASE_RANDOM = ALL_GLOBAL_DEFAULT_PHASE

    def __init__(self, **base_options):
        SolverOptions.__init__(self, **base_options)
        if self.unsat_cores_mode is not None:
            raise PysmtValueError("'unsat_cores_mode' option not supported.")

        # Set Defaults
        self.preprocessing = True
        self.propagation_limit = None
        self.more_important_lit = None
        self.less_important_lit = None
        self.global_default_phase = None
        self.enable_trace_generation = False
        self.output = None
        self.verbosity = 0

        for k,v in self.solver_options.items():
            if k == "enable_trace_generation":
                if v not in (True, False):
                    raise PysmtValueError("Invalid value for %s: %s" % \
                                     (str(k),str(v)))
            elif k == "output":
                if v is not None and not hasattr(v, "fileno"):
                    raise PysmtValueError("Invalid value for %s: %s" % \
                                     (str(k),str(v)))

            elif k == "global_default_phase":
                if v is not None and v not in PicosatOptions.ALL_GLOBAL_DEFAULT_PHASE:
                    raise PysmtValueError("Invalid value for %s: %s" % \
                                     (str(k),str(v)))
            elif k == "preprocessing":
                if v not in (True, False):
                    raise PysmtValueError("Invalid value for %s: %s" % \
                                     (str(k),str(v)))
            elif k == "verbosity":
                if not is_python_integer(v):
                    raise PysmtValueError("Invalid value for %s: %s" % \
                                     (str(k),str(v)))
            elif k == "propagation_limit":
                if not is_python_integer(v):
                    raise PysmtValueError("Invalid value for %s: %s" % \
                                     (str(k),str(v)))
            elif k in ("more_important_lit", "less_important_lit"):
                if v is not None:
                    try:
                        valid = all(x.is_symbol(types.BOOL) for x in v)
                    except:
                        valid = False
                    if not valid:
                        raise PysmtValueError("'more_important_lit' and "
                                              "'less_important_lit' require a "
                                              "list of Boolean variables")
            else:
                raise PysmtValueError("Unrecognized option '%s'." % k)
            # Store option
            setattr(self, k, v)

        # Consistency
        if self.output is not None and self.verbosity == 0:
            self.verbosity = 1

    def __call__(self, solver):
        """Handle Options"""
        pico = solver.pico
        if self.random_seed is not None:
            picosat.picosat_set_seed(pico, self.random_seed)

        if self.preprocessing is True:
            picosat.picosat_set_plain(pico, 0)
        else:
            picosat.picosat_set_plain(pico, 1)

        if self.propagation_limit is not None:
            picosat.picosat_set_propagation_limit(pico,
                                                  self.propagation_limit)

        if self.more_important_lit is not None:
            for x in self.more_important_lit:
                lit = solver._get_var_id(x) #pylint: disable=protected-access
                picosat.picosat_set_more_important_lit(pico, lit)

        if self.less_important_lit is not None:
            for x in self.less_important_lit:
                lit = solver._get_var_id(x) #pylint: disable=protected-access
                picosat.picosat_set_less_important_lit(pico, lit)

        if self.global_default_phase is not None:
            picosat.picosat_set_global_default_phase(pico,
                                                     self.global_default_phase)

        if self.output is not None:
            self._log_file_handler = picosat.picosat_set_output(pico, self.output)

        if self.enable_trace_generation:
            rv = picosat.picosat_enable_trace_generation(pico)
            if rv == 0: raise PysmtValueError("Picosat: Cannot enable Trace"
                                              " Generation")

        if self.verbosity > 0:
            picosat.picosat_set_verbosity(pico, self.verbosity)

# EOC PicosatOptions


class PicosatSolver(Solver):
    """PicoSAT solver"""

    LOGICS = [ pysmt.logics.QF_BOOL ]
    OptionsClass = PicosatOptions

    def __init__(self, environment, logic, **options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        **options)

        self.mgr = environment.formula_manager
        self.pico = picosat.picosat_init()
        self.converter = None
        self.cnfizer = CNFizer(environment=environment)
        self.latest_model = None
        self._var_ids = {}
        self._log_file_handler = None
        # Initialize
        self.options(self)

    def _get_var_id(self, symbol):
        if not symbol.is_symbol(types.BOOL):
            raise ConvertExpressionError("No theory terms are supported in PicoSAT")

        if symbol in self._var_ids:
            return self._var_ids[symbol]
        else:
            vid = picosat.picosat_inc_max_var(self.pico)
            self._var_ids[symbol] = vid
            return vid

    @clear_pending_pop
    def reset_assertions(self):
        picosat.picosat_flushout(self._log_file_handler)
        picosat.picosat_reset(self.pico)
        self.pico = picosat.picosat_init()
        self._var_ids = {}
        self.options(self)

    @clear_pending_pop
    def declare_variable(self, var):
        raise NotImplementedError

    def _get_pico_lit(self, lit):
        mult = 1
        var = lit
        if lit.is_not():
            mult = -1
            var = lit.arg(0)

        vid = self._get_var_id(var)
        return vid * mult

    @clear_pending_pop
    @catch_conversion_error
    def add_assertion(self, formula, named=None):
        # First, we get rid of True/False constants
        formula = formula.simplify()
        if formula.is_false():
            picosat.picosat_add(self.pico, 0)
        elif not formula.is_true():
            cnf = self.cnfizer.convert(formula)
            self._add_cnf_assertion(cnf)

    def _add_cnf_assertion(self, cnf):
        for clause in cnf:
            for lit in clause:
                v = self._get_pico_lit(lit)
                picosat.picosat_add(self.pico, v)
            picosat.picosat_add(self.pico, 0)

    @clear_pending_pop
    @catch_conversion_error
    def solve(self, assumptions=None):
        if assumptions is not None:
            cnf = []
            for a in assumptions:
                cnf += self.cnfizer.convert(a)

            missing = []
            for clause in cnf:
                if len(clause) == 1:
                    v = self._get_pico_lit(next(iter(clause)))
                    picosat.picosat_assume(self.pico, v)
                else:
                    missing.append(clause)

            if len(missing) > 0:
                self.push()
                self._add_cnf_assertion(missing)
                self.pending_pop = True

        res = picosat.picosat_sat(self.pico, -1)
        if res == picosat.PICOSAT_SATISFIABLE:
            self.latest_model = self.get_model()
            return True
        else:
            self.latest_model = None
            return False


    def get_value(self, item):
        if self.latest_model is None:
            self.get_model()
        return self.latest_model.get_value(item)


    def get_model(self):
        assignment = {}
        for var, vid in self._var_ids.items():
            v = picosat.picosat_deref(self.pico, vid)
            assert v!=0, "Error when translating variable."

            value = self.mgr.Bool(v == 1)
            assignment[var] = value

        return EagerModel(assignment=assignment,
                          environment=self.environment)

    @clear_pending_pop
    def push(self, levels=1):
        for _ in range(levels):
            picosat.picosat_push(self.pico)

    @clear_pending_pop
    def pop(self, levels=1):
        for _ in range(levels):
            picosat.picosat_pop(self.pico)

    def _exit(self):
        picosat.picosat_flushout(self._log_file_handler)
        picosat.picosat_reset(self.pico)
