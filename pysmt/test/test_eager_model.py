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
from pysmt.test import TestCase, main
from pysmt.shortcuts import And, Or, FALSE, TRUE, FreshSymbol, Solver
from pysmt.solvers.eager import EagerModel
from pysmt.typing import REAL, INT
from pysmt.test import skipIfSolverNotAvailable
from pysmt.exceptions import PysmtTypeError


class TestEagerModel(TestCase):

    def test_construction(self):
        """Build an eager model out of a dictionary"""

        x, y = FreshSymbol(), FreshSymbol()

        d = {x: TRUE(), y: FALSE()}

        model = EagerModel(assignment=d)

        self.assertEqual(model.get_value(x), TRUE())
        self.assertEqual(model.get_value(y), FALSE())
        self.assertEqual(model.get_value(And(x,y)), FALSE())

    def test_env_default_arguments(self):
        """Test use global env"""
        x = FreshSymbol()
        d = {x: TRUE()}

        model = EagerModel(d)
        self.assertEqual(model.get_value(x), TRUE())

    def test_result_is_const(self):
        """The result of get_value is a constant"""

        x, y = FreshSymbol(), FreshSymbol()
        d = {x:TRUE()}

        model = EagerModel(assignment=d)
        with self.assertRaises(PysmtTypeError):
            model.get_value(And(x,y), model_completion=False)

        d2 = {x:TRUE(), y:x}
        model = EagerModel(assignment=d2)
        with self.assertRaises(PysmtTypeError):
            model.get_value(And(x,y))

    def test_complete_model(self):
        """Given a partial assignment, we can make a total model."""
        x, y = FreshSymbol(), FreshSymbol()
        r = FreshSymbol(REAL)
        p = FreshSymbol(INT)
        d = {x:TRUE()}

        model = EagerModel(assignment=d)

        self.assertEqual(model.get_value(x), TRUE())
        self.assertEqual(model.get_value(Or(x,y)), TRUE())
        self.assertTrue(model.get_value(p).is_constant(INT))
        self.assertTrue(model.get_value(r).is_constant(REAL))

        self.assertEqual(model.get_value(x, model_completion=False), TRUE())
        with self.assertRaises(PysmtTypeError):
            model.get_value(And(x,y), model_completion=False)
        with self.assertRaises(PysmtTypeError):
            model.get_value(p, model_completion=False)
        with self.assertRaises(PysmtTypeError):
            model.get_value(r, model_completion=False)


    def test_contains(self):
        x, y, z = [FreshSymbol() for _ in range(3)]
        d = {x: TRUE(), y: FALSE()}
        model = EagerModel(assignment=d)
        self.assertTrue(x in model)
        self.assertFalse(z in model)

    @skipIfSolverNotAvailable("z3")
    def test_warp_solvermodel(self):
        x, y, z = [FreshSymbol() for _ in range(3)]
        with Solver(name='z3') as solver:
            solver.add_assertion(And(x,y,z))
            solver.solve()
            z3_model = solver.get_model()
            eager_model = EagerModel(z3_model)
            for var, value  in eager_model:
                self.assertIn(var, [x,y,z])
                self.assertEqual(value, TRUE())

if __name__ == '__main__':
    main()
