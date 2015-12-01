from io import TextIOWrapper
from subprocess import Popen, PIPE

from six import iteritems, PY2

import pysmt.smtlib.commands as smtcmd
from pysmt.solvers.eager import EagerModel
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import SmtLibCommand
from pysmt.solvers.solver import Solver
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              UnknownSolverAnswerError)

class SmtLibSolver(Solver):
    """Wrapper for using a solver via textual SMT-LIB interface.

    The solver is launched in a subprocess using args as arguments of
    the executable. Interaction with the solver occurs via pipe.
    """

    def __init__(self, args, environment, logic, user_options=None,
                 LOGICS=None):
        Solver.__init__(self,
                        environment,
                        logic=logic,
                        user_options=user_options)
        # Flag used to debug interaction with the solver
        self.dbg = False

        if LOGICS is not None: self.LOGICS = LOGICS
        self.args = args
        self.declared_vars = set()
        self.solver = Popen(args, stdout=PIPE, stderr=PIPE, stdin=PIPE)
        self.parser = SmtLibParser(interactive=True)
        if PY2:
            self.solver_stdin = self.solver.stdin
            self.solver_stdout = self.solver.stdout
        else:
            self.solver_stdin = TextIOWrapper(self.solver.stdin)
            self.solver_stdout = TextIOWrapper(self.solver.stdout)

        # Initialize solver
        self.set_option(":print-success", "true")
        self.set_option(":produce-models", "true")
        # Redirect diagnostic output to stdout
        self.set_option(":diagnostic-output-channel", '"stdout"')
        if self.options is not None:
            for o,v in iteritems(self.options):
                self.set_option(o,v)
        self.set_logic(logic)

    def get_default_options(self, logic=None, user_options=None):
        res = {}
        for o,v in iteritems(user_options):
            if o not in ["generate_models", "unsat_cores_mode"]:
                res[o] = v
        return res

    def set_option(self, name, value):
        self._send_silent_command(SmtLibCommand(smtcmd.SET_OPTION,
                                                [name, value]))

    def set_logic(self, logic):
        self._send_silent_command(SmtLibCommand(smtcmd.SET_LOGIC, [logic]))

    def _send_command(self, cmd):
        """Sends a command to the STDIN pipe."""
        if self.dbg: print("Sending: " + cmd.serialize_to_string())
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
        if self.dbg: print("Read: " + str(res))
        return res

    def _get_value_answer(self):
        """Reads and parses an assignment from the STDOUT pipe"""
        lst = self.parser.get_assignment_list(self.solver_stdout)
        if self.dbg: print("Read: " + str(lst))
        return lst

    def _declare_variable(self, symbol):
        cmd = SmtLibCommand(smtcmd.DECLARE_FUN, [symbol])
        self._send_silent_command(cmd)
        self.declared_vars.add(symbol)

    def _check_success(self):
        res = self._get_answer()
        if res != "success":
            raise UnknownSolverAnswerError("Solver returned: '%s'" % res)

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

    def reset_assertions(self):
        self._send_silent_command(SmtLibCommand(smtcmd.RESET_ASSERTIONS, []))
        return

    def add_assertion(self, formula, named=None):
        deps = formula.get_free_variables()
        for d in deps:
            if d not in self.declared_vars:
                self._declare_variable(d)
        self._send_silent_command(SmtLibCommand(smtcmd.ASSERT, [formula]))

    def push(self, levels=1):
        self._send_silent_command(SmtLibCommand(smtcmd.PUSH, [levels]))

    def pop(self, levels=1):
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
        for s in self.environment.formula_manager.get_all_symbols():
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
