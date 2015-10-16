#
# This file is part of pySMT.
#
#   Copyright 2015 Andrea Micheli and Marco Gario
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
from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.shortcuts import Symbol, And, Symbol, Equals, TRUE
from pysmt.shortcuts import get_env, is_sat, is_valid, get_model, is_unsat
from pysmt.typing import BVType, BV32, BV128
from pysmt.logics import QF_BV


class TestBV(TestCase):

    @skipIfNoSolverForLogic(QF_BV)
    def test_bv(self):
        mgr = get_env().formula_manager
        BV = mgr.BV

        # Constants
        one = BV(1, 32)
        zero = BV(0, 32)
        big = BV(127, 128)
        binary = BV("111")
        binary2 = BV("#b111")
        binary3 = BV(0b111, 3) # In this case we need to explicit the width

        self.assertEqual(binary, binary2)
        self.assertEqual(binary2, binary3)
        self.assertEqual(one, mgr.BVOne(32))
        self.assertEqual(zero, mgr.BVZero(32))

        # Type Equality
        self.assertTrue(BV32 != BV128)
        self.assertFalse(BV32 != BV32)
        self.assertFalse(BV32 == BV128)
        self.assertTrue(BV32 == BV32)

        with self.assertRaises(ValueError):
            # Negative numbers are not supported
            BV(-1, 10)
        with self.assertRaises(ValueError):
            # Number should fit in the width
            BV(10, 2)

        # Variables
        b128 = Symbol("b", BV128) # BV1, BV8 etc. are defined in pysmt.typing
        b32 = Symbol("b32", BV32)
        hexample = BV(0x10, 32)
        #s_one = BV(-1, 32)
        bcustom = Symbol("bc", BVType(42))

        self.assertIsNotNone(hexample)
        self.assertIsNotNone(bcustom)
        #self.assertIsNotNone(s_one)
        self.assertEqual(bcustom.bv_width(), 42)
        self.assertEqual(hexample.constant_value(), 16)
        #self.assertEqual(str(s_one), "-1_32")

        not_zero32 = mgr.BVNot(zero)
        not_b128 = mgr.BVNot(b128)

        f1 = Equals(not_zero32, b32)
        f2 = Equals(not_b128, big)

        #print(f1)
        #print(f2)

        self.assertTrue(is_sat(f1, logic=QF_BV))
        self.assertTrue(is_sat(f2, logic=QF_BV))

        zero_and_one = mgr.BVAnd(zero, one)
        zero_or_one = mgr.BVOr(zero, one)
        zero_xor_one = mgr.BVXor(zero, one)

        zero_xor_one.simplify()
        # print(zero_and_one)
        # print(zero_or_one)
        # print(zero_xor_one)

        f1 = Equals(zero_and_one, b32)
        f2 = Equals(zero_or_one, b32)
        f3 = Equals(zero_xor_one, b32)
        f4 = Equals(zero_xor_one, one)

        self.assertTrue(is_sat(f1, logic=QF_BV), f1)
        self.assertTrue(is_sat(f2, logic=QF_BV), f2)
        self.assertTrue(is_sat(f3, logic=QF_BV), f3)
        self.assertTrue(is_valid(f4, logic=QF_BV), f4)

        with self.assertRaises(TypeError):
            mgr.BVAnd(b128, zero)

        f = mgr.BVAnd(b32, zero)
        f = mgr.BVOr(f, b32)
        f = mgr.BVXor(f, b32)
        f = Equals(f, zero)

        self.assertTrue(is_sat(f, logic=QF_BV), f)

        zero_one_64 = mgr.BVConcat(zero, one)
        one_zero_64 = mgr.BVConcat(one, zero)
        one_one_64  = mgr.BVConcat(one, one)

        self.assertTrue(zero_one_64.bv_width() == 64)
        f1 = Equals(mgr.BVXor(one_zero_64, zero_one_64),
                    one_one_64)

        self.assertTrue(is_sat(f1, logic=QF_BV), f1)

        # MG: BV indexes grow to the left.
        # This is confusing and we should address this.
        extraction = mgr.BVExtract(zero_one_64, 32, 63)
        self.assertTrue(is_valid(Equals(extraction, zero)))
        #print(extraction)

        ult = mgr.BVULT(zero, one)
        neg = mgr.BVNeg(one)
        self.assertTrue(is_valid(ult, logic=QF_BV), ult)
        test_eq = Equals(neg, one)
        self.assertTrue(is_unsat(test_eq, logic=QF_BV))

        # print(ult)
        # print(neg)

        f = zero
        addition = mgr.BVAdd(f, one)
        multiplication = mgr.BVMul(f, one)
        udiv = mgr.BVUDiv(f, one)

        self.assertTrue(is_valid(Equals(addition, one), logic=QF_BV), addition)
        self.assertTrue(is_valid(Equals(multiplication, zero), logic=QF_BV), multiplication)
        self.assertTrue(is_valid(Equals(udiv, zero), logic=QF_BV), udiv)

        # print(addition)
        # print(multiplication)
        # print(udiv)

        three = mgr.BV(3, 32)
        two = mgr.BV(2, 32)

        reminder = mgr.BVURem(three, two)
        shift_l_a = mgr.BVLShl(one, one)
        shift_l_b = mgr.BVLShl(one, 1)

        self.assertTrue(is_valid(Equals(reminder, one)), reminder)
        self.assertEqual(shift_l_a, shift_l_b)
        self.assertTrue(is_valid(Equals(shift_l_a, two)))
        # print(reminder)
        # print(shift_l_a)
        # print(shift_l_b)

        shift_r_a = mgr.BVLShr(one, one)
        shift_r_b = mgr.BVLShr(one, 1)
        self.assertEqual(shift_r_a, shift_r_b)
        self.assertTrue(is_valid(Equals(shift_r_a, zero)))

        rotate_l = mgr.BVRol(one, 3)
        rotate_r = mgr.BVRor(rotate_l, 3)
        self.assertTrue(is_valid(Equals(one, rotate_r)))

        # print(rotate_l)
        # print(rotate_r)

        zero_ext = mgr.BVZExt(one, 64)
        signed_ext = mgr.BVSExt(one, 64)
        signed_ext2 = mgr.BVSExt(mgr.BVNeg(one), 64)

        self.assertNotEqual(signed_ext2, signed_ext)
        self.assertTrue(is_valid(Equals(zero_ext, signed_ext), logic=QF_BV))

        # print(zero_ext)
        # print(signed_ext)

        x = Symbol("x")
        g = And(x, mgr.BVULT(zero, one))

        res = is_sat(g, logic=QF_BV)
        self.assertTrue(res)

        model = get_model(g, logic=QF_BV)
        self.assertTrue(model[x] == TRUE())

        gt_1 = mgr.BVUGT(zero, one)
        gt_2 = mgr.BVULT(one, zero)
        self.assertEqual(gt_1, gt_2)

        gte_1 = mgr.BVULE(zero, one)
        gte_2 = mgr.BVUGE(one, zero)
        self.assertEqual(gte_1, gte_2)

        self.assertTrue(is_valid(gte_2, logic=QF_BV))

        ide = Equals(mgr.BVNeg(BV(10, 32)), mgr.SBV(-10, 32))
        self.assertValid(ide, logic=QF_BV)

        # These should work without exceptions
        mgr.SBV(-2, 2)
        mgr.SBV(-1, 2)
        mgr.SBV(0, 2)
        mgr.SBV(1, 2)

        # Overflow and Underflow
        with self.assertRaises(ValueError):
            mgr.SBV(2, 2)
        with self.assertRaises(ValueError):
            mgr.SBV(-3, 2)

        # These should work without exceptions
        mgr.BV(0, 2)
        mgr.BV(1, 2)
        mgr.BV(2, 2)
        mgr.BV(3, 2)
        # Overflow
        with self.assertRaises(ValueError):
            mgr.BV(4, 2)
        # No negative number allowed
        with self.assertRaises(ValueError):
            mgr.BV(-1, 2)

        # SBV should behave as BV for positive numbers
        self.assertEqual(mgr.SBV(10, 16), mgr.BV(10, 16))

        return

if __name__ == "__main__":
    main()
