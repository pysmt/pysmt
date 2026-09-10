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
from pysmt.environment import Environment
from pysmt.formula import FormulaManager
from pysmt.fnode import FNode
from pysmt.typing import BOOL, REAL, INT, BVType
from pysmt.test import TestCase


class TestSortCommutative(TestCase):

    def setUp(self) -> None:
        self.env = Environment()
        # enable sorting of arguments for commutative operations.
        self.env.sort_commutative_args = True

    @property
    def mgr(self) -> FormulaManager:
        return self.env.formula_manager

    def test_setup(self):
        self.assertTrue(self.env.sort_commutative_args)

    def test_forall(self):
        b1: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        b2: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        b3: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        forall: FNode = self.mgr.ForAll([b3, b2, b1], self.mgr.TRUE())
        # ordered by creation time
        self.assertEqual(forall.quantifier_vars(), (b1, b2, b3))

    def test_exists(self):
        b1: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        b2: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        b3: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        exists: FNode = self.mgr.Exists([b3, b2, b1], self.mgr.TRUE())
        # ordered by creation time
        self.assertEqual(exists.quantifier_vars(), (b1, b2, b3))

    def test_implies(self):
        b1: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        b2: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        # not commutative
        for first, second in [(b1, b2), (b2, b1)]:
            impl: FNode = self.mgr.Implies(first, second)
            self.assertEqual(impl.args(), (first, second))

    def test_iff(self):
        b1: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        b2: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        iff: FNode = self.mgr.Iff(b2, b1)
        # ordered by creation time
        self.assertEqual(iff.args(), (b1, b2))

    def test_plus_real(self):
        s1: FNode = self.mgr.Real(1)
        s2: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        s3: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        add: FNode = self.mgr.Plus(s3, s2, s1)
        # ordered by creation time
        self.assertEqual(add.args(), (s1, s2, s3))

    def test_plus_int(self):
        s1: FNode = self.mgr.Int(1)
        s2: FNode = self.mgr.new_fresh_symbol(INT, "i%d")
        s3: FNode = self.mgr.new_fresh_symbol(INT, "i%d")
        add: FNode = self.mgr.Plus(s3, s2, s1)
        # ordered by creation time
        self.assertEqual(add.args(), (s1, s2, s3))

    def test_minus(self):
        arg1: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        arg2: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        # not commutative
        for first, second in [(arg1, arg2), (arg2, arg1)]:
            impl: FNode = self.mgr.Minus(first, second)
            self.assertEqual(impl.args(), (first, second))

    def test_times(self):
        arg1: FNode = self.mgr.new_fresh_symbol(INT, "i%d")
        arg2: FNode = self.mgr.new_fresh_symbol(INT, "i%d")
        arg3: FNode = self.mgr.new_fresh_symbol(INT, "i%d")
        times: FNode = self.mgr.Times(arg3, arg2, arg1)
        # ordered by creation time
        self.assertEqual(times.args(), (arg1, arg2, arg3))

    def test_pow(self):
        # create exponent first
        arg1: FNode = self.mgr.Real(len(self.mgr.real_constants) + 0.2)
        # use symbol as base to avoid this turning into a fract constant.
        arg2: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")

        # not commutative
        formula: FNode = self.mgr.Pow(arg2, arg1)
        self.assertEqual(formula.args(), (arg2, arg1))

    def test_div(self):
        arg1: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        arg2: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        # not commutative
        for first, second in [(arg1, arg2), (arg2, arg1)]:
            formula: FNode = self.mgr.Div(first, second)
            self.assertEqual(formula.args(), (first, second))

    def test_equals(self):
        arg1: FNode = self.mgr.new_fresh_symbol(INT, "i%d")
        arg2: FNode = self.mgr.new_fresh_symbol(INT, "i%d")
        formula: FNode = self.mgr.Equals(arg2, arg1)
        # ordered by creation time
        self.assertEqual(formula.args(), (arg1, arg2))

    def test_le(self):
        arg1: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        arg2: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        # not commutative
        for first, second in [(arg1, arg2), (arg2, arg1)]:
            formula: FNode = self.mgr.LE(first, second)
            self.assertEqual(formula.args(), (first, second))

    def test_lt(self):
        arg1: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        arg2: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        # not commutative
        for first, second in [(arg1, arg2), (arg2, arg1)]:
            formula: FNode = self.mgr.LT(first, second)
            self.assertEqual(formula.args(), (first, second))

    def test_ite(self):
        arg1: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        arg2: FNode = self.mgr.new_fresh_symbol(REAL, "r%d")
        cond: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        # not commutative
        for first, second in [(arg1, arg2), (arg2, arg1)]:
            formula: FNode = self.mgr.Ite(cond, first, second)
            self.assertEqual(formula.args(), (cond, first, second))

    def test_and(self):
        arg1: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        arg2: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        arg3: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        arg4: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        formula: FNode = self.mgr.And(arg4, arg3, arg2, arg1)
        # ordered by creation time
        self.assertEqual(formula.args(), (arg1, arg2, arg3, arg4))

    def test_or(self):
        arg1: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        arg2: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        arg3: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        arg4: FNode = self.mgr.new_fresh_symbol(BOOL, "b%d")
        formula: FNode = self.mgr.Or(arg4, arg3, arg2, arg1)
        # ordered by creation time
        self.assertEqual(formula.args(), (arg1, arg2, arg3, arg4))

    def test_bv_and(self):
        arg1: FNode = self.mgr.new_fresh_symbol(BVType(4), "b%d")
        arg2: FNode = self.mgr.new_fresh_symbol(BVType(4), "b%d")
        arg3: FNode = self.mgr.new_fresh_symbol(BVType(4), "b%d")
        arg4: FNode = self.mgr.new_fresh_symbol(BVType(4), "b%d")
        formula: FNode = self.mgr.BVAnd(arg4, arg3, arg2, arg1)
        # ordered by creation time
        self.assertEqual(formula.args(), (arg1, arg2, arg3, arg4))

    def test_bv_or(self):
        arg1: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg2: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg3: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg4: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        formula: FNode = self.mgr.BVOr(arg4, arg3, arg2, arg1)
        # ordered by creation time
        self.assertEqual(formula.args(), (arg1, arg2, arg3, arg4))

    def test_bv_xor(self):
        arg1: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg2: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg3: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg4: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        formula: FNode = self.mgr.BVXor(arg4, arg3, arg2, arg1)
        # ordered by creation time
        self.assertEqual(formula.args(), (arg1, arg2, arg3, arg4))

    def test_bv_add(self):
        arg1: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg2: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg3: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg4: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        formula: FNode = self.mgr.BVAdd(arg4, arg3, arg2, arg1)
        # ordered by creation time
        self.assertEqual(formula.args(), (arg1, arg2, arg3, arg4))

    def test_bv_mul(self):
        arg1: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg2: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg3: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg4: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        formula: FNode = self.mgr.BVMul(arg4, arg3, arg2, arg1)
        # ordered by creation time
        self.assertEqual(formula.args(), (arg1, arg2, arg3, arg4))

    def test_bv_concat(self):
        arg1: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        arg2: FNode = self.mgr.new_fresh_symbol(BVType(3), "b%d")
        # not commutative
        for first, second in [(arg1, arg2), (arg2, arg1)]:
            formula: FNode = self.mgr.BVConcat(first, second)
            self.assertEqual(formula.args(), (first, second))


if __name__ == "__main__":
    from pysmt.test import main
    main()
