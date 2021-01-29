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

import pysmt.smtlib.commands as smtcmd
from pysmt.exceptions import SolverReturnedUnknownResultError, UnknownSolverAnswerError
from pysmt.smtlib.script import SmtLibCommand
from pysmt.smtlib.solver import SmtLibSolver
from pysmt.solvers.interpolation import Interpolator


class SmtLibInterpolator(Interpolator):

    def __init__(self, args, environment, logic, LOGICS=None, **options):
        Interpolator.__init__(self)
        options["produce_interpolants"] = True
        self.options = (args, environment, logic, LOGICS, options)

    def binary_interpolant(self, a, b):
        """Returns a binary interpolant for the pair (a, b), if And(a, b) is
        unsatisfaiable, or None if And(a, b) is satisfiable.

        """
        res = self.sequence_interpolant([a, b])
        if res is None:
            return res
        return res[0]

    def sequence_interpolant(self, formulas):
        """Returns a sequence interpolant for the conjunction of formulas, or
        None if the problem is satisfiable.

        """
        solver = SmtLibSolver(self.options[0], self.options[1], self.options[2], self.options[3], **self.options[4])
        for f in formulas:
            sorts = solver.to.get_types(f, custom_only=True)
            for s in sorts:
                if all(s not in ds for ds in solver.declared_sorts):
                    solver._declare_sort(s)
            deps = f.get_free_variables()
            for d in deps:
                if all(d not in dv for dv in solver.declared_vars):
                    solver._declare_variable(d)

        names = []
        i = 0
        for f in formulas:
            self._send_named_assert_command(f, "IP_%d" % i, solver)
            names.append("IP_%d" % i)
            i += 1

        solver._send_command(SmtLibCommand(smtcmd.CHECK_SAT, []))
        ans = solver._get_answer()
        if ans == "sat":
            return None
        elif ans == "unsat":
            pass
        elif ans == "unknown":
            raise SolverReturnedUnknownResultError
        else:
            raise UnknownSolverAnswerError("Solver returned: " + ans)
        solver._send_command(SmtLibCommand(smtcmd.GET_INTERPOLANTS, names))
        res = solver.parser.get_interpolant_list(solver.solver_stdout)
        solver._exit()
        return res

    def _send_named_assert_command(self, f, assert_name, solver):
        cmd = SmtLibCommand(smtcmd.ASSERT, [f])
        cmd.assert_name = assert_name
        solver._send_silent_command(cmd)

    def _exit(self):
        pass
