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
from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.logics import QF_UFLIRA, QF_LRA, QF_BOOL
from pysmt.solvers.eager import EagerModel

class TestModels(TestCase):

    @skipIfNoSolverForLogic(QF_LRA)
    def test_get_model(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", REAL)

        zero = Real(0)

        f1 = Implies(varA, And(GT(varB, zero), LT(varB, zero)))

        model = None
        for solver_name in get_env().factory.all_solvers(logic=QF_UFLIRA):
            with Solver(name=solver_name, logic=QF_LRA) as s:
                s.add_assertion(f1)
                check = s.solve()
                self.assertTrue(check)
                model = s.get_model()

            # Here the solver is gone
            self.assertEqual(model[varA], FALSE())

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_get_py_value_model(self):
        varA = Symbol("A", BOOL)

        with Solver(logic=QF_BOOL) as s:
            s.add_assertion(varA)
            s.solve()
            model = s.get_model()
            self.assertTrue(model.get_py_value(varA))


    @skipIfNoSolverForLogic(QF_BOOL)
    def test_eager_model_iterator(self):
        x, y, z = [Symbol(s) for s in "xyz"]
        with Solver(logic=QF_BOOL) as s:
            s.add_assertion(And(x,y))
            assert s.solve()
            d = {}
            d[x] = s.get_value(x)
            d[y] = s.get_value(y)
        m = EagerModel(assignment=d)

        # The model does not talk about 'z'
        for (k,_) in m:
            self.assertFalse(k == z)

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_pickle_eager_model(self):
        import pickle

        x, y = Symbol("x"), Symbol("y")
        with Solver(logic=QF_BOOL) as s:
            s.add_assertion(And(x,y))
            assert s.solve()
            model = list(s.get_model())
            self.assertIsNotNone(pickle.dumps(model, -1))

if __name__ == '__main__':
    main()
