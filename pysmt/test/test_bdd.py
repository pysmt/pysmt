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
import unittest

import pysmt
from pysmt.shortcuts import And, Not, Symbol, Bool, Exists, Solver
from pysmt.shortcuts import get_env
from pysmt.test import TestCase, skipIfSolverNotAvailable
from pysmt.test.examples import EXAMPLE_FORMULAS


class TestBdd(TestCase):

    @skipIfSolverNotAvailable("bdd")
    def setUp(self):
        self.x, self.y = Symbol("x"), Symbol("y")

        self.bdd_solver = Solver(logic=pysmt.logics.BOOL,
                                 name='bdd')
        self.bdd_converter = self.bdd_solver.converter

    @skipIfSolverNotAvailable("bdd")
    def test_basic_bdd_variables(self):
        convert = self.bdd_converter.convert
        bdd_x = convert(self.x)
        bdd_x_2 = convert(self.x)
        bdd_y = convert(self.y)

        self.assertIsNotNone(bdd_x)
        self.assertEquals(bdd_x, bdd_x_2)
        self.assertNotEquals(bdd_x, bdd_y)

    @skipIfSolverNotAvailable("bdd")
    def test_basic_expr(self):
        convert = self.bdd_converter.convert

        bdd_x = convert(self.x)
        bdd_y = convert(self.y)
        bdd_x_and_y = bdd_x.And(bdd_y)

        x_and_y = And(self.x, self.y)
        converted_expr = convert(x_and_y)

        self.assertEquals(bdd_x_and_y, converted_expr)

    @skipIfSolverNotAvailable("bdd")
    def test_examples_conversion(self):
        convert = self.bdd_converter.convert
        for example in EXAMPLE_FORMULAS:
            if example.logic != pysmt.logics.BOOL:
                continue
            expr = convert(example.expr)
            self.assertIsNotNone(expr)

    @skipIfSolverNotAvailable("bdd")
    def test_examples_solving(self):
        for example in EXAMPLE_FORMULAS:
            if example.logic != pysmt.logics.BOOL:
                continue
            solver = Solver(logic=pysmt.logics.BOOL,
                            name='bdd')
            solver.add_assertion(example.expr)
            if example.is_sat:
                self.assertTrue(solver.solve())
            else:
                self.assertFalse(solver.solve())

    @skipIfSolverNotAvailable("bdd")
    def test_basic_solving(self):
        solver = self.bdd_solver
        f = And(self.x, Not(self.y))

        solver.add_assertion(f)
        self.assertTrue(solver.solve())
        model = solver.get_model()
        self.assertEquals(model[self.x], Bool(True))
        self.assertEquals(model[self.y], Bool(False))
        self.assertFalse(solver.get_py_value(self.y))

        solver.push()
        solver.add_assertion(Not(self.x))
        self.assertFalse(solver.solve())

        solver.pop()
        self.assertTrue(solver.solve())

    @skipIfSolverNotAvailable("bdd")
    def test_quantifier_elimination(self):
        convert = self.bdd_converter.convert
        f = Exists([self.x], And(self.x, self.y))
        bdd_g = convert(f)
        g = self.bdd_converter.back(bdd_g)
        self.assertEquals(g, self.y)

if __name__ == '__main__':
    unittest.main()
