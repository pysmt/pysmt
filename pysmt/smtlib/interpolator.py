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
        self._solver = SmtLibSolver(args, environment, logic, LOGICS, **options)

    def binary_interpolant(self, a, b):
        res = self.sequence_interpolant([a, b])
        if res is None:
            return res
        return res[0]

    def sequence_interpolant(self, formulas):
        for f in formulas:
            sorts = self._solver.to.get_types(f, custom_only=True)
            for s in sorts:
                if all(s not in ds for ds in self._solver.declared_sorts):
                    self._solver._declare_sort(s)
            deps = f.get_free_variables()
            for d in deps:
                if all(d not in dv for dv in self._solver.declared_vars):
                    self._solver._declare_variable(d)

        names = []
        i = 0
        for f in formulas:
            self._send_named_assert_command(f, "IP_%d" % i)
            names.append("IP_%d" %i)
            i += 1

        self._solver._send_command(SmtLibCommand(smtcmd.CHECK_SAT, []))
        ans = self._solver._get_answer()
        if ans == "sat":
            return None
        elif ans == "unsat":
            pass
        elif ans == "unknown":
            raise SolverReturnedUnknownResultError
        else:
            raise UnknownSolverAnswerError("Solver returned: " + ans)
        self._solver._send_command(SmtLibCommand(smtcmd.GET_INTERPOLANTS, names))
        return self._solver.parser.get_interpolant_list(self._solver.solver_stdout)

    def _send_named_assert_command(self, f, assert_name):
        cmd = SmtLibCommand(smtcmd.ASSERT, [f])
        cmd.assert_name = assert_name
        self._solver._send_silent_command(cmd)

    def _exit(self):
        self._solver.exit()
