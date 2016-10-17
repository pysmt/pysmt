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
from pysmt.shortcuts import And, Not, Symbol, Bool, Exists, Solver
from pysmt.shortcuts import get_env, qelim, Or
from pysmt.test import TestCase, skipIfSolverNotAvailable, main
from pysmt.test.examples import get_example_formulae
from pysmt.logics import BOOL
from pysmt.exceptions import PysmtValueError

class TestBdd(TestCase):

    @skipIfSolverNotAvailable("bdd")
    def setUp(self):
        self.x, self.y = Symbol("x"), Symbol("y")

        self.bdd_solver = Solver(logic=BOOL,
                                 name='bdd')
        self.bdd_converter = self.bdd_solver.converter


        trail = [And, Or, And, Or]
        f = And(self.x, self.y)
        for op in trail:
            f = op(f, f)
        self.big_tree = f

    @skipIfSolverNotAvailable("bdd")
    def test_basic_bdd_variables(self):
        convert = self.bdd_converter.convert
        bdd_x = convert(self.x)
        bdd_x_2 = convert(self.x)
        bdd_y = convert(self.y)

        self.assertIsNotNone(bdd_x)
        self.assertEqual(bdd_x, bdd_x_2)
        self.assertNotEqual(bdd_x, bdd_y)

    @skipIfSolverNotAvailable("bdd")
    def test_basic_expr(self):
        convert = self.bdd_converter.convert

        bdd_x = convert(self.x)
        bdd_y = convert(self.y)
        bdd_x_and_y = self.bdd_converter.ddmanager.And(bdd_x, bdd_y)

        x_and_y = And(self.x, self.y)
        converted_expr = convert(x_and_y)

        self.assertEqual(bdd_x_and_y, converted_expr)

    @skipIfSolverNotAvailable("bdd")
    def test_examples_conversion(self):
        convert = self.bdd_converter.convert
        for example in get_example_formulae():
            if example.logic != BOOL:
                continue
            expr = convert(example.expr)
            self.assertIsNotNone(expr)

    @skipIfSolverNotAvailable("bdd")
    def test_examples_solving(self):
        for example in get_example_formulae():
            if example.logic != BOOL:
                continue
            solver = Solver(logic=BOOL,
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
        self.assertEqual(model[self.x], Bool(True))
        self.assertEqual(model[self.y], Bool(False))
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
        self.assertEqual(g, self.y)

    @skipIfSolverNotAvailable("bdd")
    def test_quantifier_eliminator(self):
        f = Exists([self.x], And(self.x, self.y))
        g = qelim(f, solver_name="bdd")
        self.assertEqual(g, self.y)

    @skipIfSolverNotAvailable("bdd")
    def test_reordering(self):
        with Solver(name="bdd", logic=BOOL,
                    solver_options={'dynamic_reordering': True}) as s:
            s.add_assertion(self.big_tree)
            self.assertTrue(s.solve())

    @skipIfSolverNotAvailable("bdd")
    def test_reordering_algorithms(self):
        from pysmt.solvers.bdd import BddOptions
        for algo in BddOptions.CUDD_ALL_REORDERING_ALGORITHMS:
            with Solver(name="bdd", logic=BOOL,
                        solver_options={'dynamic_reordering': True,
                                        'reordering_algorithm': algo}) as s:
                s.add_assertion(self.big_tree)
                self.assertTrue(s.solve())
                self.assertEqual(algo, s.ddmanager.ReorderingStatus()[1])

    @skipIfSolverNotAvailable("bdd")
    def test_fixed_ordering(self):
        f_order = [self.x, self.y]
        r_order = list(reversed(f_order))

        for order in [f_order, r_order]:
            with Solver(name="bdd", logic=BOOL,
                        solver_options={'static_ordering': order}) as s:
                s.add_assertion(self.big_tree)
                self.assertTrue(s.solve())

                # Check that the ordering is understood by CUDD
                for pos, var in enumerate(order):
                    var_idx = s.converter.var2node[var].NodeReadIndex()
                    perm = s.ddmanager.ReadPerm(var_idx)
                    self.assertEqual(pos, perm)

    @skipIfSolverNotAvailable("bdd")
    def test_invalid_ordering(self):
        with self.assertRaises(PysmtValueError):
            Solver(name="bdd", logic=BOOL,
                   solver_options={'static_ordering':
                                   [And(self.x, self.y), self.y]})

    @skipIfSolverNotAvailable("bdd")
    def test_initial_ordering(self):
        with Solver(name="bdd", logic=BOOL,
                    solver_options={'static_ordering':[self.x, self.y],
                                    'dynamic_reordering':True}) as s:
            s.add_assertion(self.big_tree)
            self.assertTrue(s.solve())
            self.assertNotEquals(s.ddmanager.ReorderingStatus()[1], 0)


if __name__ == '__main__':
    main()
