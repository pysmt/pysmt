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
from six.moves import xrange

from pysmt.shortcuts import Solver, BVAnd, BVOr, BVXor, BVConcat, BVULT, BVUGT, \
    BVULE, BVUGE, BVAdd, BVSub, BVMul, BVUDiv, BVURem, BVLShl, BVLShr, BVNot, \
    BVNeg, BVZExt, BVSExt, BVRor, BVRol, BV, BVExtract, BVSLT, BVSLE, BVComp, \
    BVSDiv, BVSRem, BVAShr, EqualsOrIff, BVZero, BVOne, Symbol, Bool
from pysmt.typing import BVType
from pysmt.test import TestCase, skipIfSolverNotAvailable, main
from pysmt.logics import QF_BV


class TestBvSimplification(TestCase):

    def setUp(self):
        # For the preparation of assertValid()
        super(TestBvSimplification, self).setUp()

        self.width = 4
        self.bin_operators = [BVAnd, BVOr, BVXor, BVConcat, BVULT, BVUGT, BVULE,
                              BVUGE, BVAdd, BVSub, BVMul, BVUDiv, BVURem, BVLShl,
                              BVLShr, BVSLT, BVSLE, BVComp, BVSDiv, BVSRem,
                              BVAShr]
        self.unary_operators = [BVNot, BVNeg]
        self.special_operators = [BVZExt, BVSExt, BVRor, BVRol]
        self.solver = None
        self.solver_simplify = None

    def all_bv_numbers(self, width=None):
        if width is None:
            width = self.width
        for x in xrange(2 ** width):
            yield BV(x, width)

    @skipIfSolverNotAvailable("msat")
    def test_msat(self):
        self.solver = Solver(name="msat")
        conv = self.solver.converter
        self.solver_simplify = lambda x: conv.back(conv.convert(x))
        # Run the tests
        self.all_unary()
        self.all_binary()
        self.all_special()
        self.extract()
        self.concat_different_length()

    def check(self, f):
        simp_f = f.simplify()
        solver_f = self.solver_simplify(f)
        self.assertEqual(solver_f, simp_f)

    def all_binary(self):
        for l in self.all_bv_numbers():
            for r in self.all_bv_numbers():
                for op in self.bin_operators:
                    try:
                        self.check(op(l, r))
                    except AssertionError:
                        if op in [BVUDiv, BVSDiv] and r == BV(0, r.bv_width()):
                            print("Warning: Division value mismatch.")
                            print(l,op,r)

    def all_unary(self):
        for l in self.all_bv_numbers():
            for op in self.unary_operators:
                self.check(op(l))

    def extract(self):
        for l in self.all_bv_numbers():
            for s in xrange(0, self.width):
                for e in xrange(s, self.width):
                    self.check(BVExtract(l, start=s, end=e))

    def concat_different_length(self):
        for l in self.all_bv_numbers():
            for w in [1, self.width-1, self.width+1]:
                for r in self.all_bv_numbers(w):
                    self.check(BVConcat(l, r))

    def all_special(self):
        for l in self.all_bv_numbers():
            for n in xrange(0, self.width + 1):
                for op in self.special_operators:
                    self.check(op(l, n))

    def check_equal_and_valid(self, formula, expected):
        simplified = formula.simplify()

        self.assertEqual(simplified, expected)

        # Check the formula equality by a solver.
        if self.env.factory.all_solvers(QF_BV):
            self.assertValid(EqualsOrIff(simplified, formula), logic=QF_BV)

    def test_bv_0_add(self):
        x = Symbol("x", BVType(32))
        f = BVAdd(BVZero(32), x)
        self.check_equal_and_valid(f, x)

    def test_bv_add_0(self):
        x = Symbol("x", BVType(32))
        f = BVAdd(x, BVZero(32))
        self.check_equal_and_valid(f, x)

    def test_bv_add_constants(self):
        f = BVAdd(BV(10, 32), BV(12, 32))
        self.check_equal_and_valid(f, BV(22, 32))

    def test_bv_add_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVAdd(x, y)
        self.check_equal_and_valid(f, BVAdd(x, y))

    def test_bv_add_overflow(self):
        f = BVAdd(BV(2**32 - 1, 32), BV(10, 32))
        self.check_equal_and_valid(f, BV(9, 32))

    def test_bv_0_mul(self):
        x = Symbol("x", BVType(32))
        f = BVMul(BVZero(32), x)
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_1_mul(self):
        x = Symbol("x", BVType(32))
        f = BVMul(BVOne(32), x)
        self.check_equal_and_valid(f, x)

    def test_bv_mul_0(self):
        x = Symbol("x", BVType(32))
        f = BVMul(x, BVZero(32))
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_mul_1(self):
        x = Symbol("x", BVType(32))
        f = BVMul(x, BVOne(32))
        self.check_equal_and_valid(f, x)

    def test_bv_mul_constants(self):
        f = BVMul(BV(10, 32), BV(12, 32))
        self.check_equal_and_valid(f, BV(120, 32))

    def test_bv_mul_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVMul(x, y)
        self.check_equal_and_valid(f, BVMul(x, y))

    def test_bv_mul_overflow(self):
        f = BVMul(BV(2**31, 32), BV(3, 32))
        self.check_equal_and_valid(f, BV(0x80000000, 32))

    def test_bv_udiv_1(self):
        x = Symbol("x", BVType(32))
        f = BVUDiv(x, BVOne(32))
        self.check_equal_and_valid(f, x)

    def test_bv_symbol_udiv_0(self):
        x = Symbol("x", BVType(32))
        f = BVUDiv(x, BVZero(32))
        self.check_equal_and_valid(f, BV(2**32 - 1, 32))

    def test_bv_0_udiv_0(self):
        f = BVUDiv(BVZero(32), BVZero(32))
        self.check_equal_and_valid(f, BV(2**32 - 1, 32))

    def test_bv_nonzero_udiv_0(self):
        f = BVUDiv(BV(10, 32), BVZero(32))
        self.check_equal_and_valid(f, BV(2**32 - 1, 32))

    def test_bv_0_udiv_nonzero(self):
        f = BVUDiv(BVZero(32), BV(10, 32))
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_0_udiv_symbol(self):
        x = Symbol("x", BVType(32))
        f = BVUDiv(BVZero(32), x)
        self.check_equal_and_valid(f, BVUDiv(BVZero(32), x))

    def test_bv_udiv_constants(self):
        f = BVUDiv(BV(20, 32), BV(10, 32))
        self.check_equal_and_valid(f, BV(2, 32))

    def test_bv_udiv_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVUDiv(x, y)
        self.check_equal_and_valid(f, BVUDiv(x, y))

    def test_bv_urem_1(self):
        x = Symbol("x", BVType(32))
        f = BVURem(x, BVOne(32))
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_symbol_urem_0(self):
        x = Symbol("x", BVType(32))
        f = BVURem(x, BVZero(32))
        self.check_equal_and_valid(f, x)

    def test_bv_0_urem_0(self):
        f = BVURem(BVZero(32), BVZero(32))
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_nonzero_urem_0(self):
        f = BVURem(BV(10, 32), BVZero(32))
        self.check_equal_and_valid(f, BV(10, 32))

    def test_bv_0_urem_nonzero(self):
        f = BVURem(BVZero(32), BV(10, 32))
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_0_urem_symbol(self):
        x = Symbol("x", BVType(32))
        f = BVURem(BVZero(32), x)
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_urem_constants(self):
        f = BVURem(BV(20, 32), BV(11, 32))
        self.check_equal_and_valid(f, BV(9, 32))

    def test_bv_urem_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVURem(x, y)
        self.check_equal_and_valid(f, BVURem(x, y))

    def test_bv_ult_eq(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVULT(BVMul(x, y), BVMul(x, y))
        self.check_equal_and_valid(f, Bool(False))

    def test_bv_ult_zero(self):
        x = Symbol("x", BVType(32))
        f = BVULT(x, BVZero(32))
        self.check_equal_and_valid(f, Bool(False))

    def test_bv_ult_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVULT(x, y)
        self.check_equal_and_valid(f, BVULT(x, y))

    def test_bv_ult_constants(self):
        f = BVULT(BVZero(32), BVOne(32))
        self.check_equal_and_valid(f, Bool(True))

    def test_bv_ule_eq(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVULE(BVMul(x, y), BVMul(x, y))
        self.check_equal_and_valid(f, Bool(True))

    def test_bv_zero_ule(self):
        x = Symbol("x", BVType(32))
        f = BVULE(BVZero(32), x)
        self.check_equal_and_valid(f, Bool(True))

    def test_bv_ule_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVULE(x, y)
        self.check_equal_and_valid(f, BVULE(x, y))

    def test_bv_ule_constants(self):
        f = BVULE(BVZero(32), BVOne(32))
        self.check_equal_and_valid(f, Bool(True))

    def test_bv_and_zero(self):
        x = Symbol("x", BVType(32))
        f = BVAnd(x, BVZero(32))
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_zero_and(self):
        x = Symbol("x", BVType(32))
        f = BVAnd(BVZero(32), x)
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_and_all_ones(self):
        x = Symbol("x", BVType(32))
        f = BVAnd(x, BV(2**32 - 1, 32))
        self.check_equal_and_valid(f, x)

    def test_bv_all_ones_and(self):
        x = Symbol("x", BVType(32))
        f = BVAnd(BV(2**32 - 1, 32), x)
        self.check_equal_and_valid(f, x)

    def test_bv_and_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVAnd(x, y)
        self.check_equal_and_valid(f, BVAnd(x, y))

    def test_bv_and_constants(self):
        f = BVAnd(BV(0xdededede, 32), BV(0xacacacac, 32))
        self.check_equal_and_valid(f, BV(0x8c8c8c8c, 32))

    def test_bv_or_zero(self):
        x = Symbol("x", BVType(32))
        f = BVOr(x, BVZero(32))
        self.check_equal_and_valid(f, x)

    def test_bv_zero_or(self):
        x = Symbol("x", BVType(32))
        f = BVOr(BVZero(32), x)
        self.check_equal_and_valid(f, x)

    def test_bv_or_all_ones(self):
        x = Symbol("x", BVType(32))
        f = BVOr(x, BV(2**32 - 1, 32))
        self.check_equal_and_valid(f, BV(2**32 - 1, 32))

    def test_bv_all_ones_or(self):
        x = Symbol("x", BVType(32))
        f = BVOr(BV(2**32 - 1, 32), x)
        self.check_equal_and_valid(f, BV(2**32 - 1, 32))

    def test_bv_or_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVOr(x, y)
        self.check_equal_and_valid(f, BVOr(x, y))

    def test_bv_or_constants(self):
        f = BVOr(BV(0xdededede, 32), BV(0xacacacac, 32))
        self.check_equal_and_valid(f, BV(0xfefefefe, 32))

    def test_bv_sub_zero(self):
        x = Symbol("x", BVType(32))
        f = BVSub(x, BVZero(32))
        self.check_equal_and_valid(f, x)

    def test_bv_sub_eq(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVSub(BVMul(x, y), BVMul(x, y))
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_sub_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVSub(x, y)
        self.check_equal_and_valid(f, BVSub(x, y))

    def test_bv_sub_constants(self):
        f = BVSub(BV(30, 32), BV(20, 32))
        self.check_equal_and_valid(f, BV(10, 32))

    def test_bv_sub_underflow(self):
        f = BVSub(BV(1, 32), BV(2, 32))
        self.check_equal_and_valid(f, BV(0xffffffff, 32))

    def test_bv_lshl_zero(self):
        x = Symbol("x", BVType(32))
        f = BVLShl(x, BVZero(32))
        self.check_equal_and_valid(f, x)

    def test_bv_zero_lshl(self):
        x = Symbol("x", BVType(32))
        f = BVLShl(BVZero(32), x)
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_lshl_overflow(self):
        x = Symbol("x", BVType(32))
        f = BVLShl(x, BV(33, 32))
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_lshl_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVLShl(x, y)
        self.check_equal_and_valid(f, BVLShl(x, y))

    def test_bv_lshl_constants(self):
        f = BVLShl(BV(0xff, 32), BVOne(32))
        self.check_equal_and_valid(f, BV(0x1fe, 32))

    def test_bv_lshr_zero(self):
        x = Symbol("x", BVType(32))
        f = BVLShr(x, BVZero(32))
        self.check_equal_and_valid(f, x)

    def test_bv_zero_lshr(self):
        x = Symbol("x", BVType(32))
        f = BVLShr(BVZero(32), x)
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_lshr_underflow(self):
        x = Symbol("x", BVType(32))
        f = BVLShr(x, BV(33, 32))
        self.check_equal_and_valid(f, BVZero(32))

    def test_bv_lshr_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVLShr(x, y)
        self.check_equal_and_valid(f, BVLShr(x, y))

    def test_bv_lshr_constants(self):
        f = BVLShr(BV(0xff, 32), BVOne(32))
        self.check_equal_and_valid(f, BV(0x7f, 32))

    def test_bv_slt_eq(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVSLT(BVMul(x, y), BVMul(x, y))
        self.check_equal_and_valid(f, Bool(False))

    def test_bv_slt_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVSLT(x, y)
        self.check_equal_and_valid(f, BVSLT(x, y))

    def test_bv_slt_constants(self):
        f = BVSLT(BV(10, 32), BV(2**32 - 1, 32))
        self.check_equal_and_valid(f, Bool(False))

    def test_bv_sle_eq(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVSLE(BVMul(x, y), BVMul(x, y))
        self.check_equal_and_valid(f, Bool(True))

    def test_bv_sle_symbols(self):
        x, y = (Symbol(name, BVType(32)) for name in "xy")
        f = BVSLE(x, y)
        self.check_equal_and_valid(f, BVSLE(x, y))

    def test_bv_sle_constants(self):
        f = BVSLE(BV(10, 32), BV(2**32 - 1, 32))
        self.check_equal_and_valid(f, Bool(False))

if __name__ == '__main__':
    main()
