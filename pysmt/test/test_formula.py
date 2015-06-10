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
from fractions import Fraction

from six.moves import xrange

import pysmt
from pysmt.typing import BOOL, REAL, INT, FunctionType
from pysmt.shortcuts import Symbol, is_sat, Not, Implies, GT, Plus, Int, Real
from pysmt.shortcuts import Minus, Times, Xor, And, Or, TRUE
from pysmt.shortcuts import get_env
from pysmt.environment import Environment
from pysmt.test import TestCase, skipIfNoSolverForLogic
from pysmt.logics import QF_BOOL
from pysmt.exceptions import NonLinearError
from pysmt.formula import FormulaManager


class TestFormulaManager(TestCase):

    def setUp(self):
        super(TestFormulaManager, self).setUp()

        self.env = get_env()
        self.mgr = self.env.formula_manager

        self.x = self.mgr.Symbol("x")
        self.y = self.mgr.Symbol("y")

        self.p = self.mgr.Symbol("p", INT)
        self.q = self.mgr.Symbol("q", INT)
        self.r = self.mgr.Symbol("r", REAL)
        self.s = self.mgr.Symbol("s", REAL)
        self.rconst = self.mgr.Real(10)
        self.iconst = self.mgr.Int(10)

        self.ftype = FunctionType(REAL, [REAL, REAL])
        self.f = self.mgr.Symbol("f", self.ftype)

        self.real_expr = self.mgr.Plus(self.s, self.r)

    def test_new_fresh_symbol(self):
        fv1 = self.mgr.new_fresh_symbol(BOOL)
        self.assertIsNotNone(fv1, "New symbol was not created.")

        fv2 = self.mgr.new_fresh_symbol(BOOL)
        self.assertNotEqual(fv1, fv2, "Fresh symbol is not new.")

        fv3 = self.mgr.new_fresh_symbol(BOOL, "abc_%d")
        self.assertEqual(fv3.symbol_name()[:3], "abc",
                          "Fresh variable doesn't have the desired prefix")

    def test_get_symbol(self):
        a = self.mgr.get_symbol("a")
        self.assertIsNone(a,
            "Symbol returned from an empty symboltable")

        self.mgr.get_or_create_symbol("a", BOOL)
        a = self.mgr.get_symbol("a")
        self.assertIsNotNone(a, "Symbol was not found in symbol table")

    def test_get_or_create_symbol(self):
        a = self.mgr.get_or_create_symbol("a", REAL)
        self.assertIsNotNone(a, "Symbol was not created")
        a2 = self.mgr.get_or_create_symbol("a", REAL)
        self.assertEqual(a, a2, "Symbol was not memoized")
        with self.assertRaises(TypeError):
            self.mgr.get_or_create_symbol("a", BOOL)

    def test_symbol(self):
        a1 = self.mgr.Symbol("a", BOOL)
        self.assertIsNotNone(a1, "Symbol was not created.")
        a2 = self.mgr.Symbol("a", BOOL)
        self.assertEqual(a1, a2, "Symbol is not memoized")

        c = self.mgr.Symbol("c")
        self.assertEqual(c.symbol_type(), BOOL, "Default Symbol Type is not BOOL")

    def test_and_node(self):
        n = self.mgr.And(self.x, self.y)
        self.assertIsNotNone(n)
        self.assertTrue(n.is_and())
        self.assertEqual(n.get_free_variables(), set([self.x, self.y]))

        m = self.mgr.And([self.x, self.y])
        self.assertEqual(m, n, "And(1,2) != And([1,2]")

        sons = m.get_sons()
        self.assertTrue(self.x in sons and self.y in sons)
        self.assertTrue(len(sons) == 2)

        zero = self.mgr.And()
        self.assertEqual(zero, self.mgr.TRUE())

        one = self.mgr.And(self.x)
        self.assertEqual(one, self.x)


    def test_or_node(self):
        n = self.mgr.Or(self.x, self.y)
        self.assertIsNotNone(n)
        self.assertTrue(n.is_or())
        self.assertEqual(n.get_free_variables(), set([self.x, self.y]))

        m = self.mgr.Or([self.x, self.y])
        self.assertEqual(m, n, "Or(1,2) != Or([1,2]")

        sons = m.get_sons()
        self.assertIn(self.x, sons)
        self.assertIn(self.y, sons)
        self.assertEqual(len(sons), 2)

        zero = self.mgr.Or()
        self.assertEqual(zero, self.mgr.FALSE())

        one = self.mgr.Or(self.x)
        self.assertEqual(one, self.x)


    def test_not_node(self):
        n = self.mgr.Not(self.x)
        self.assertIsNotNone(n)

        self.assertTrue(n.is_not())
        self.assertEqual(n.get_free_variables(), set([self.x]))

        sons = n.get_sons()
        self.assertIn(self.x, sons)
        self.assertEqual(len(sons), 1)

        self.assertEqual(self.mgr.Not(n), self.x)

    def test_implies_node(self):
        n = self.mgr.Implies(self.x, self.y)
        self.assertIsNotNone(n)

        self.assertTrue(n.is_implies())
        self.assertEqual(n.get_free_variables(), set([self.x, self.y]))

        sons = n.get_sons()
        self.assertEqual(self.x, sons[0])
        self.assertEqual(self.y, sons[1])
        self.assertEqual(len(sons), 2)

    def test_iff_node(self):
        n = self.mgr.Iff(self.x, self.y)
        self.assertIsNotNone(n)

        self.assertTrue(n.is_iff())
        self.assertEqual(n.get_free_variables(), set([self.x, self.y]))

        sons = n.get_sons()
        self.assertIn(self.x, sons)
        self.assertIn(self.y, sons)
        self.assertEqual(len(sons), 2)


    def test_ge_node_type(self):
        with self.assertRaises(TypeError):
            self.mgr.GE(self.x, self.r)

        with self.assertRaises(TypeError):
            self.mgr.GE(self.r, self.x)

        with self.assertRaises(TypeError):
            self.mgr.GE(self.p, self.r)

    def test_ge_node(self):
        n = self.mgr.GE(self.real_expr, self.real_expr)
        self.assertIsNotNone(n)
        n = self.mgr.GE(self.r, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.GE(self.rconst, self.s)
        self.assertIsNotNone(n)
        n = self.mgr.GE(self.rconst, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.GE(self.r, self.s)
        self.assertIsNotNone(n)

        sons = n.get_sons()
        self.assertIn(self.r, sons)
        self.assertIn(self.s, sons)
        self.assertEqual(len(sons), 2)

        n = self.mgr.GE(self.p, self.q)
        self.assertIsNotNone(n)

    def test_minus_node(self):
        n = self.mgr.Minus(self.real_expr, self.real_expr)
        self.assertIsNotNone(n)

        n = self.mgr.Minus(self.r, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.Minus(self.rconst, self.s)
        self.assertIsNotNone(n)
        n = self.mgr.Minus(self.rconst, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.Minus(self.r, self.s)
        self.assertIsNotNone(n)

        sons = n.get_sons()
        self.assertIn(self.r, sons)
        self.assertIn(self.s, sons)
        self.assertEqual(len(sons), 2)

        n = self.mgr.Minus(self.p, self.q)
        self.assertIsNotNone(n)

        self.assertTrue(n.is_minus())
        self.assertEqual(n.get_free_variables(), set([self.p, self.q]))

        with self.assertRaises(TypeError):
            n = self.mgr.Minus(self.r, self.q)


    def test_times_node(self):
        n = self.mgr.Times(self.real_expr, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.Times(self.r, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.Times(self.rconst, self.rconst)
        self.assertIsNotNone(n)

        n = self.mgr.Times(self.rconst, self.s)
        self.assertIsNotNone(n)
        sons = n.get_sons()
        self.assertIn(self.rconst, sons)
        self.assertIn(self.s, sons)
        self.assertEqual(len(sons), 2)

        n = self.mgr.Times(self.r, self.s)
        self.assertIsNotNone(n)
        self.assertTrue(n.is_times())
        self.assertEqual(n.get_free_variables(), set([self.r, self.s]))

        n = self.mgr.Times(self.iconst, self.q)
        self.assertIsNotNone(n)


    def test_div_non_linear(self):
        with self.assertRaises(NonLinearError):
            self.mgr.Div(self.r, self.s)

        with self.assertRaises(NonLinearError):
            self.mgr.Div(self.rconst, self.s)

    def test_div_node(self):
        n = self.mgr.Div(self.real_expr, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.Div(self.r, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.Div(self.rconst, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.Div(self.s, self.rconst)
        self.assertIsNotNone(n)

        inv = self.mgr.Real((1, self.rconst.constant_value()))
        self.assertEqual(n, self.mgr.Times(self.s, inv))

    def test_equals(self):
        n = self.mgr.Equals(self.real_expr, self.real_expr)
        self.assertIsNotNone(n)
        n = self.mgr.Equals(self.r, self.s)
        self.assertIsNotNone(n)

        sons = n.get_sons()
        self.assertIn(self.r, sons)
        self.assertIn(self.s, sons)
        self.assertEqual(len(sons), 2)

        n = self.mgr.Equals(self.p, self.q)
        self.assertIsNotNone(n)

        self.assertTrue(n.is_equals())
        self.assertEqual(n.get_free_variables(), set([self.p, self.q]))

        with self.assertRaises(TypeError):
            n = self.mgr.Equals(self.p, self.r)

    def test_gt_node_type(self):
        with self.assertRaises(TypeError):
            self.mgr.GT(self.x, self.r)

        with self.assertRaises(TypeError):
            self.mgr.GT(self.r, self.x)

        with self.assertRaises(TypeError):
            self.mgr.GT(self.r, self.p)

    def test_gt_node(self):
        n = self.mgr.GT(self.real_expr, self.real_expr)
        self.assertIsNotNone(n)
        n = self.mgr.GT(self.r, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.GT(self.rconst, self.s)
        self.assertIsNotNone(n)
        n = self.mgr.GT(self.rconst, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.GT(self.r, self.s)
        self.assertIsNotNone(n)

        sons = n.get_sons()
        self.assertIn(self.r, sons)
        self.assertIn(self.s, sons)
        self.assertEqual(len(sons), 2)

        n = self.mgr.GT(self.p, self.q)
        self.assertIsNotNone(n)

    def test_le_node_type(self):
        with self.assertRaises(TypeError):
            self.mgr.LE(self.x, self.r)

        with self.assertRaises(TypeError):
            self.mgr.LE(self.r, self.x)

    def test_le_node(self):
        n = self.mgr.LE(self.real_expr, self.real_expr)
        self.assertIsNotNone(n)
        n = self.mgr.LE(self.r, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.LE(self.rconst, self.s)
        self.assertIsNotNone(n)
        n = self.mgr.LE(self.rconst, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.LE(self.r, self.s)
        self.assertIsNotNone(n)

        self.assertTrue(n.is_le())
        self.assertEqual(n.get_free_variables(), set([self.r, self.s]))

        sons = n.get_sons()
        self.assertIn(self.r, sons)
        self.assertIn(self.s, sons)
        self.assertEqual(len(sons), 2)

    def test_lt_node_type(self):
        with self.assertRaises(TypeError):
            self.mgr.LT(self.x, self.r)

        with self.assertRaises(TypeError):
            self.mgr.LT(self.r, self.x)

    def test_lt_node(self):
        n = self.mgr.LT(self.real_expr, self.real_expr)
        self.assertIsNotNone(n)
        n = self.mgr.LT(self.r, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.LT(self.rconst, self.s)
        self.assertIsNotNone(n)
        n = self.mgr.LT(self.rconst, self.rconst)
        self.assertIsNotNone(n)
        n = self.mgr.LT(self.r, self.s)
        self.assertIsNotNone(n)

        self.assertTrue(n.is_lt())
        self.assertEqual(n.get_free_variables(), set([self.r, self.s]))

        sons = n.get_sons()
        self.assertIn(self.r, sons)
        self.assertIn(self.s, sons)
        self.assertEqual(len(sons), 2)

    def test_ite(self):
        n = self.mgr.Ite(self.x, self.y, self.x)
        self.assertIsNotNone(n)

        sons = n.get_sons()
        self.assertIn(self.x, sons)
        self.assertIn(self.y, sons)
        self.assertEqual(len(sons), 3)

        n = self.mgr.Ite(self.x, self.s, self.r)
        self.assertIsNotNone(n)

        n = self.mgr.Ite(self.x, self.p, self.q)
        self.assertIsNotNone(n)

        self.assertTrue(n.is_ite())
        self.assertEqual(n.get_free_variables(), set([self.x, self.p, self.q]))

        with self.assertRaises(TypeError):
            self.mgr.Ite(self.x, self.p, self.r)


    def test_function(self):
        n = self.mgr.Function(self.f, [self.r, self.s])
        self.assertIsNotNone(n)

        sons = n.get_sons()
        self.assertIn(self.r, sons)
        self.assertIn(self.s, sons)
        self.assertEqual(len(sons), 2)

        self.assertTrue(n.is_function_application())
        self.assertEqual(n.get_free_variables(), set([self.f, self.r, self.s]))


    def test_constant(self):
        n1 = self.mgr.Real(Fraction(100, 10))
        self.assertIsNotNone(n1)
        self.assertTrue(n1.is_constant())
        self.assertTrue(n1.is_real_constant())

        n2 = self.mgr.Real((100, 10))
        self.assertEqual(n1, n2,
                "Generation of constant does not provide a consistent result.")
        n3 = self.mgr.Real(10)
        self.assertEqual(n1, n3,
                "Generation of constant does not provide a consistent result.")
        n4 = self.mgr.Real(10.0)
        self.assertEqual(n1, n4,
                "Generation of constant does not provide a consistent result.")

        nd = self.mgr.Real(Fraction(100,1))
        self.assertNotEqual(nd, n1)

        with self.assertRaises(TypeError):
            self.mgr.Real(True)

        nd = self.mgr.Int(10)
        self.assertIsNotNone(nd)
        self.assertTrue(nd.is_constant())
        self.assertTrue(nd.is_int_constant())

    def test_bconstant(self):
        n = self.mgr.Bool(True)
        m = self.mgr.Bool(False)
        self.assertIsNotNone(n)
        self.assertIsNotNone(m)
        self.assertNotEqual(n, m)

        self.assertTrue(n.is_constant())
        self.assertTrue(n.is_bool_constant())

        with self.assertRaises(TypeError):
            self.mgr.Bool(42)

    def test_plus_node(self):
        with self.assertRaises(TypeError):
            self.mgr.Plus([self.x, self.r])

        with self.assertRaises(TypeError):
            self.mgr.Plus([self.p, self.r])

        with self.assertRaises(TypeError):
            self.mgr.Plus()


        n1 = self.mgr.Plus([self.r, self.s])
        n2 = self.mgr.Plus(self.r, self.s)
        self.assertIsNotNone(n1)
        self.assertIsNotNone(n2)
        self.assertEqual(n1, n2, "Constructed Plus expression do not match")

        self.assertTrue(n1.is_plus())
        self.assertEqual(set([self.r, self.s]), n1.get_free_variables())

        one = self.mgr.Plus([self.p])
        self.assertEqual(one, self.p)

    def test_exactly_one(self):
        symbols = [ self.mgr.Symbol("s%d"%i, BOOL) for i in range(5) ]
        c = self.mgr.ExactlyOne(symbols)

        self.assertTrue(len(c.get_sons()) > 1)

        t = self.mgr.Bool(True)
        c = c.substitute({symbols[0]: t,
                          symbols[1]: t}).simplify()
        self.assertEqual(c, self.mgr.Bool(False),
                         "ExactlyOne should not allow 2 symbols to be True")

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_exactly_one_is_sat(self):
        symbols = [ self.mgr.Symbol("s%d"%i, BOOL) for i in range(5) ]
        c = self.mgr.ExactlyOne(symbols)
        all_zero = self.mgr.And([self.mgr.Iff(s, self.mgr.Bool(False))
                                  for s in symbols])
        test_zero = self.mgr.And(c, all_zero)
        self.assertFalse(is_sat(test_zero, logic=QF_BOOL),
                         "ExactlyOne should not allow all symbols to be False")


    def test_at_most_one(self):
        symbols = [ self.mgr.Symbol("s%d"%i, BOOL) for i in range(5) ]
        c = self.mgr.AtMostOne(symbols)

        self.assertTrue(len(c.get_sons()) > 1)
        t = self.mgr.Bool(True)
        c = c.substitute({symbols[0]: t,
                          symbols[1]: t}).simplify()
        self.assertEqual(c, self.mgr.Bool(False),
                         "AtMostOne should not allow two symbols to be True")

    def test_xor(self):
        xor1 = self.mgr.Xor(self.x, self.y)
        self.assertIsNotNone(xor1)

        with self.assertRaises(TypeError):
            self.mgr.Xor(self.p, self.q)

        xor_false = self.mgr.Xor(self.mgr.TRUE(), self.mgr.TRUE()).simplify()
        self.assertEqual(xor_false, self.mgr.FALSE(),
                         "Xor should be False if both arguments are True")

        xor_true = self.mgr.Xor(self.mgr.TRUE(), self.mgr.FALSE()).simplify()
        self.assertEqual(xor_true, self.mgr.TRUE(),
                         "Xor should be True if both arguments are False")

    def test_all_different(self):
        many = 5
        symbols = [self.mgr.Symbol("s%d"%i, INT) for i in range(many) ]
        f = self.mgr.AllDifferent(symbols)

        one = self.mgr.Int(1)
        for i in xrange(many):
            for j in xrange(many):
                if i != j:
                    c = f.substitute({symbols[i]: one,
                                      symbols[j]: one}).simplify()
                    self.assertEqual(c, self.mgr.Bool(False),
                                     "AllDifferent should not allow 2 symbols "\
                                     "to be 1")


        c = f.substitute({symbols[i]: self.mgr.Int(i) for i in xrange(many)})
        self.assertEqual(c.simplify(), self.mgr.Bool(True),
                         "AllDifferent should be tautological for a set " \
                         "of different values")


    def test_min(self):
        min1 = self.mgr.Min(self.p, Plus(self.q, self.mgr.Int(1)))
        self.assertIsNotNone(min1)

        with self.assertRaises(TypeError):
            self.mgr.Min(self.p, self.r)

        min_int = self.mgr.Min(self.mgr.Int(1), self.mgr.Int(2), self.mgr.Int(3))
        self.assertEqual(min_int.simplify(), self.mgr.Int(1),
                         "The minimum of 1, 2 and 3 should be 1")

        min_real = self.mgr.Min(self.mgr.Real(1), self.mgr.Real(2), self.mgr.Real(3))
        self.assertEqual(min_real.simplify(), self.mgr.Real(1),
                         "The minimum of 1.0, 2.0 and 3.0 should be 1.0")


    def test_max(self):
        max1 = self.mgr.Max(self.p, Plus(self.q, self.mgr.Int(1)))
        self.assertIsNotNone(max1)

        with self.assertRaises(TypeError):
            self.mgr.Max(self.p, self.r)

        max_int = self.mgr.Max(self.mgr.Int(1), self.mgr.Int(2), self.mgr.Int(3))
        self.assertEqual(max_int.simplify(), self.mgr.Int(3),
                         "The maximum of 1, 2 and 3 should be 3")

        max_real = self.mgr.Max(self.mgr.Real(1), self.mgr.Real(2), self.mgr.Real(3))
        self.assertEqual(max_real.simplify(), self.mgr.Real(3),
                         "The maximum of 1.0, 2.0 and 3.0 should be 3.0")



    def test_pickling(self):
        import pickle

        src_env = Environment()
        dst_env = Environment()
        src_mgr = src_env.formula_manager
        dst_mgr = dst_env.formula_manager

        a = src_mgr.Symbol("A")
        b = src_mgr.Symbol("B")
        f = src_mgr.And(a, src_mgr.Not(b))

        self.assertEqual(str(f), "(A & (! B))", str(f))

        serialized = pickle.dumps(f)

        f_new = pickle.loads(serialized)
        f_new = dst_mgr.normalize(f)

        args = f_new.get_sons()
        self.assertEqual(str(args[0]), "A",
                          "Expecting symbol A, " +
                          "symbol %s found instead" % str(args[0]))

        a = dst_mgr.Symbol("A")
        b = dst_mgr.Symbol("B")
        g = dst_mgr.And(a, dst_mgr.Not(b))

        # Contextualized formula is memoized
        self.assertEqual(f_new, g, "%s != %s" % (id(f_new), id(g)))
        # But it differs from the one in the other formula manager
        self.assertNotEqual(f_new, f)

        # Normalizing a formula in the same manager should not
        # be a problem
        f_new = src_mgr.normalize(f)
        self.assertEqual(f_new, f, "%s != %s" %(id(a),id(b)))

    def test_infix(self):
        x, y, p = self.x, self.y, self.p

        with self.assertRaises(Exception):
            x.Implies(y)
        get_env().enable_infix_notation = True
        self.assertEqual(Implies(x,y), x.Implies(y))

        self.assertEqual(p + p, Plus(p,p))
        self.assertEqual(p > p, GT(p,p))
        get_env().enable_infix_notation = False

    def test_infix_extended(self):
        p, r, x, y = self.p, self.r, self.x, self.y
        get_env().enable_infix_notation = True

        self.assertEqual(Plus(p, Int(1)), p + 1)
        self.assertEqual(Plus(r, Real(1)), r + 1)
        self.assertEqual(Times(r, Real(1)), r * 1)

        self.assertEqual(Minus(p, Int(1)), p - 1)
        self.assertEqual(Minus(r, Real(1)), r - 1)
        self.assertEqual(Times(r, Real(1)), r * 1)

        self.assertEqual(Plus(r, Real(1.5)), r + 1.5)
        self.assertEqual(Minus(r, Real(1.5)), r - 1.5)
        self.assertEqual(Times(r, Real(1.5)), r * 1.5)

        self.assertEqual(Plus(r, Real(1.5)), 1.5 + r)
        self.assertEqual(Times(r, Real(1.5)), 1.5 * r)

        with self.assertRaises(TypeError):
            foo = p + 1.5

        self.assertEqual(Not(x), ~x)

        self.assertEqual(Times(r, Real(-1)), -r)
        self.assertEqual(Times(p, Int(-1)), -p)

        self.assertEqual(Xor(x, y), x ^ y)
        self.assertEqual(And(x, y), x & y)
        self.assertEqual(Or(x, y), x | y)

        self.assertEqual(Or(x, TRUE()), x | True)
        self.assertEqual(Or(x, TRUE()), True | x)

        self.assertEqual(And(x, TRUE()), x & True)
        self.assertEqual(And(x, TRUE()), True & x)

        get_env().enable_infix_notation = False

    def test_toReal(self):
        f = self.mgr.Equals(self.rconst, self.mgr.ToReal(self.p))
        self.assertIsNotNone(f)

        with self.assertRaises(TypeError):
            self.mgr.ToReal(self.x)

        f1 = self.mgr.ToReal(self.p)
        f2 = self.mgr.ToReal(f1)
        self.assertEqual(f1, f2)

        self.assertTrue(f1.is_toreal())
        self.assertEqual(set([self.p]), f1.get_free_variables())

        f3 = self.mgr.Equals(self.iconst, self.p)
        with self.assertRaises(TypeError):
            self.mgr.ToReal(f3)

        f4 = self.mgr.Plus(self.rconst, self.r)
        f5 = self.mgr.ToReal(f4)
        self.assertEqual(f5, f4)




    def test_is_term(self):
        and_x_x = self.mgr.And(self.x, self.x)
        apply_f = self.mgr.Function(self.f, [self.r, self.s])

        self.assertTrue(self.x.is_term())
        self.assertTrue(and_x_x.is_term())
        self.assertFalse(self.f.is_term())
        self.assertTrue(apply_f.is_term())

    def test_formula_in_formula_manager(self):
        x = self.mgr.FreshSymbol()
        and_x_x = self.mgr.And(x, x)
        new_mgr = FormulaManager(get_env())
        y = new_mgr.FreshSymbol()
        and_y_y = new_mgr.And(y, y)

        self.assertTrue(x in self.mgr)
        self.assertFalse(y in self.mgr)

        self.assertTrue(and_x_x in self.mgr)
        self.assertFalse(and_y_y in self.mgr)

    def test_typing(self):
        self.assertTrue(BOOL.is_bool_type())
        self.assertFalse(BOOL.is_function_type())

        self.assertTrue(REAL.is_real_type())
        self.assertFalse(REAL.is_bool_type())

        self.assertTrue(INT.is_int_type())
        self.assertFalse(INT.is_real_type())

        self.assertTrue(self.ftype.is_function_type())
        self.assertFalse(self.ftype.is_int_type())

class TestShortcuts(TestCase):

    def test_shortcut_is_using_global_env(self):
        global_mgr = get_env().formula_manager
        a1 = Symbol("z", BOOL)
        a2 = global_mgr.Symbol("z", BOOL)

        self.assertEqual(a1, a2,
                          "Symbols generated by env and Symbol are not the same")





if __name__ == '__main__':
    import unittest
    unittest.main()
