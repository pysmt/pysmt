# Copyright 2014 Andrea Micheli and Marco Gario
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import time
from io import TextIOWrapper
from subprocess import Popen, PIPE

import pysmt.smtlib.commands as smtcmd
from pysmt.solvers.eager import EagerModel
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibCommand
from pysmt.solvers.solver import Solver, SolverOptions
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              UnknownSolverAnswerError, PysmtValueError)
from pysmt.decorators import clear_pending_pop

class SmtLibOptions(SolverOptions):
    """Options for the SmtLib Solver.

    * debug_interaction: True, False
      Print the communication between pySMT and the wrapped executable
    """
    def __init__(self, **base_options):
        SolverOptions.__init__(self, **base_options)
        if self.unsat_cores_mode is not None:
            raise PysmtValueError("'unsat_cores_mode' option not supported.")
        self.debug_interaction = False

        if 'debug_interaction' in self.solver_options:
            self.debug_interaction = self.solver_options['debug_interaction']
            del self.solver_options['debug_interaction']

    def __call__(self, solver):
        # These options are needed for the wrapper to work
        solver.set_option(":print-success", "true")
        solver.set_option(":diagnostic-output-channel", '"stdout"')

        if self.generate_models:
            solver.set_option(":produce-models", "true")
        else:
            solver.set_option(":produce-models", "false")

        if self.random_seed is not None:
            solver.set_option(":random-seed", str(self.random_seed))

        for k,v in self.solver_options.items():
            if k in (':print-success', 'diagnostic-output-channel'):
                raise PysmtValueError("Cannot override %s." % k)
            solver.set_option(k, str(v))

# EOC SmtLibOptions


class SmtLibSolver(Solver):
    """Wrapper for using a solver via textual SMT-LIB interface.

    The solver is launched in a subprocess using args as arguments of
    the executable. Interaction with the solver occurs via pipe.
    """

    OptionsClass = SmtLibOptions

    def __init__(self, args, environment, logic, LOGICS=None, **options):
        Solver.__init__(self,
                        environment,
                        logic=logic,
                        **options)
        self.to = self.environment.typeso
        if LOGICS is not None: self.LOGICS = LOGICS
        self.args = args
        self.declared_vars = [set()]
        self.declared_sorts = [set()]
        self.solver = Popen(args, stdout=PIPE, stderr=PIPE, stdin=PIPE,
                            bufsize=-1)
        # Give time to the process to start-up
        time.sleep(0.01)
        self.parser = SmtLibParser(interactive=True)
        self.solver_stdin = TextIOWrapper(self.solver.stdin)
        self.solver_stdout = TextIOWrapper(self.solver.stdout)

        # Initialize solver
        self.options(self)
        self.set_logic(logic)

    def set_option(self, name, value):
        self._send_silent_command(SmtLibCommand(smtcmd.SET_OPTION,
                                                [name, value]))

    def set_logic(self, logic):
        self._send_silent_command(SmtLibCommand(smtcmd.SET_LOGIC, [logic]))

    def _debug(self, msg, *format_args):
        if self.options.debug_interaction:
            print(msg % format_args)

    def _send_command(self, cmd):
        """Sends a command to the STDIN pipe."""
        self._debug("Sending: %s", cmd.serialize_to_string())
        cmd.serialize(self.solver_stdin, daggify=True)
        self.solver_stdin.write("\n")
        self.solver_stdin.flush()

    def _send_silent_command(self, cmd):
        """Sends a command to the STDIN pipe and awaits for acknowledgment."""
        self._send_command(cmd)
        self._check_success()

    def _get_answer(self):
        """Reads a line from STDOUT pipe"""
        res = self.solver_stdout.readline().strip()
        self._debug("Read: %s", res)
        return res

    def _get_value_answer(self):
        """Reads and parses an assignment from the STDOUT pipe"""
        lst = self.parser.get_assignment_list(self.solver_stdout)
        self._debug("Read: %s", lst)
        return lst

    def _declare_sort(self, sort):
        cmd = SmtLibCommand(smtcmd.DECLARE_SORT, [sort])
        self._send_silent_command(cmd)
        self.declared_sorts[-1].add(sort)

    def _declare_variable(self, symbol):
        cmd = SmtLibCommand(smtcmd.DECLARE_FUN, [symbol])
        self._send_silent_command(cmd)
        self.declared_vars[-1].add(symbol)

    def _check_success(self):
        res = self._get_answer()
        if res != "success":
            raise UnknownSolverAnswerError("Solver returned: '%s'" % res)

    @clear_pending_pop
    def solve(self, assumptions=None):
        assert assumptions is None
        self._send_command(SmtLibCommand(smtcmd.CHECK_SAT, []))
        ans = self._get_answer()
        if ans == "sat":
            return True
        elif ans == "unsat":
            return False
        elif ans == "unknown":
            raise SolverReturnedUnknownResultError
        else:
            raise UnknownSolverAnswerError("Solver returned: " + ans)

    @clear_pending_pop
    def reset_assertions(self):
        self._send_silent_command(SmtLibCommand(smtcmd.RESET_ASSERTIONS, []))
        return

    @clear_pending_pop
    def add_assertion(self, formula, named=None):
        # This is needed because Z3 (and possibly other solvers) incorrectly
        # recognize N * M * x as a non-linear term
        formula = formula.simplify()
        sorts = self.to.get_types(formula, custom_only=True)
        for s in sorts:
            if all(s not in ds for ds in self.declared_sorts):
                self._declare_sort(s)
        deps = formula.get_free_variables()
        for d in deps:
            if all(d not in dv for dv in self.declared_vars):
                self._declare_variable(d)
        self._send_silent_command(SmtLibCommand(smtcmd.ASSERT, [formula]))

    @clear_pending_pop
    def push(self, levels=1):
        self.declared_vars.append(set())
        self.declared_sorts.append(set())
        self._send_silent_command(SmtLibCommand(smtcmd.PUSH, [levels]))

    @clear_pending_pop
    def pop(self, levels=1):
        self.declared_vars.pop()
        self.declared_sorts.pop()
        self._send_silent_command(SmtLibCommand(smtcmd.POP, [levels]))

    def get_value(self, item):
        self._send_command(SmtLibCommand(smtcmd.GET_VALUE, [item]))
        lst = self._get_value_answer()
        assert len(lst) == 1
        assert len(lst[0]) == 2
        return lst[0][1]

    def print_model(self, name_filter=None):
        if name_filter is not None:
            raise NotImplementedError
        for v in self.declared_vars:
            print("%s = %s" % (v, self.get_value(v)))

    def get_model(self):
        assignment = {}
        for s in self.declared_vars[-1]:
            if s.is_term():
                v = self.get_value(s)
                assignment[s] = v
        return EagerModel(assignment=assignment, environment=self.environment)

    def _exit(self):
        self._send_command(SmtLibCommand(smtcmd.EXIT, []))
        self.solver_stdin.close()
        self.solver_stdout.close()
        self.solver.stderr.close()
        self.solver.terminate()
        return
