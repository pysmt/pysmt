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
from pysmt.shortcuts import Solver, Symbol, And, Real, GT, LT, Implies, FALSE
from pysmt.shortcuts import get_env
from pysmt.typing import BOOL, REAL
from pysmt.test import TestCase, skipIfNoSolverAvailable
from pysmt.logics import QF_UFLIRA


class TestModels(TestCase):

    @skipIfNoSolverAvailable
    def test_get_model(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", REAL)

        zero = Real(0)

        f1 = Implies(varA, And(GT(varB, zero), LT(varB, zero)))

        model = None
        for solver_name in get_env().factory.all_solvers(logic=QF_UFLIRA):
            with Solver(name=solver_name) as s:
                s.add_assertion(f1)
                check = s.solve()
                self.assertTrue(check)
                model = s.get_model()

            # Here the solver is gone
            self.assertEquals(model[varA], FALSE())

    @skipIfNoSolverAvailable
    def test_get_py_value_model(self):
        varA = Symbol("A", BOOL)

        with Solver() as s:
            s.add_assertion(varA)
            s.solve()
            model = s.get_model()
            self.assertTrue(model.get_py_value(varA))


if __name__ == '__main__':
    import unittest
    unittest.main()
