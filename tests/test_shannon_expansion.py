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

import pysmt.logics
from pysmt.shortcuts import And, Symbol, Exists, FALSE, ForAll, Or, TRUE
from pysmt.shortcuts import qelim
from pysmt.exceptions import InternalSolverError, NoSolverAvailableError
from pysmt.test import TestCase, main
from pysmt.test.examples import get_example_formulae


class TestShannon(TestCase):

    def setUp(self):
        TestCase.setUp(self)
        self.x, self.y = Symbol("x"), Symbol("y")

    def test_exists(self):
        f = Exists([self.x], And(self.x, self.y))
        g = qelim(f, solver_name="shannon")
        g = g.simplify()
        self.assertEqual(g, self.y)

    def test_forall(self):
        f = ForAll([self.x], And(self.x, self.y))
        g = qelim(f, solver_name="shannon")
        g = g.simplify()
        self.assertEqual(g, FALSE())

    def test_multiple(self):
        f = ForAll([self.x, self.y], Or(self.x, self.y))
        g = qelim(f, solver_name="shannon")
        g = g.simplify()
        self.assertEqual(g, FALSE())

    def test_nested(self):
        f = Exists([self.x], ForAll([self.y], Or(self.x, self.y)))
        g = qelim(f, solver_name="shannon")
        g = g.simplify()
        self.assertEqual(g, TRUE())

    def test_examples_solving(self):
        for example in get_example_formulae():
            if example.logic != pysmt.logics.BOOL:
                continue

            fv = example.expr.get_free_variables()
            f = Exists(fv, example.expr)
            g = qelim(f, solver_name="shannon").simplify()
            if example.is_sat:
                self.assertTrue(g.is_true())
            else:
                self.assertTrue(g.is_false())

            f = ForAll(fv, example.expr)
            g = qelim(f, solver_name="shannon").simplify()
            if example.is_valid:
                self.assertTrue(g.is_true())
            else:
                self.assertTrue(g.is_false())

    def test_w_theory(self):
        for example in get_example_formulae():
            f = example.expr
            if example.logic.quantifier_free: continue
            try:
                res = qelim(f, solver_name="shannon")
                self.assertIsNotNone(res, f)
            except NoSolverAvailableError:
                self.assertTrue(example.logic > pysmt.logics.BOOL, example)
            except InternalSolverError:
                self.assertTrue(example.logic > pysmt.logics.BOOL, example)


if __name__ == '__main__':
    main()
