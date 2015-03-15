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

from pysmt.test import TestCase

from pysmt.shortcuts import Symbol, get_env, And
from pysmt.typing import BVType, BV1, BV8, BV32, BV128


class TestBV(TestCase):
    def test_bv(self):
        mgr = get_env().formula_manager
        BV = mgr.BV

        # Constants
        one = BV(1, 32)
        hexample = BV(0x16, 8)
        zero = BV(0, 32)
        s_one = BV(-1, 32)
        big = BV(127, 28)

        # Variables
        b128 = Symbol("b", BV128) # BV1, BV8 etc. are defined in pysmt.typing
        bcustom = Symbol("bc", BVType(42))
        b32 = Symbol("b3", BV32)

        not_zero = mgr.BVNot(zero)
        not_b = mgr.BVNot(b128)
        print(not_zero)
        print(not_b)

        zero_and_one = mgr.BVAnd(zero, one)
        zero_or_one = mgr.BVOr(zero, one)
        zero_xor_one = mgr.BVXor(one, one)

        print(zero_and_one)
        print(zero_or_one)
        print(zero_xor_one)

        with self.assertRaises(TypeError):
            mgr.BVAnd(b128, zero)

        f = mgr.BVAnd(b32, zero)
        f = mgr.BVOr(f, b32)
        f = mgr.BVXor(f, b32)
        print(f)

        zero_one_64 = mgr.BVConcat(zero, one)
        self.assertTrue(zero_one_64.bv_width() == 64)
        print(zero_one_64)

        extraction = mgr.BVExtract(zero_one_64, 5, 10)
        print(extraction)

        ult = mgr.BVULT(zero, one)
        print(ult)

        neg = mgr.BVNeg(extraction)
        print(neg)

        addition = mgr.BVAdd(f, one)
        print(addition)

        multiplication = mgr.BVMul(f, one)
        print(multiplication)

        udiv = mgr.BVUDiv(f, one)
        print(udiv)

        reminder = mgr.BVURem(f, one)
        print(reminder)

        shift_l = mgr.BVLShl(f, one)
        print(shift_l)
        shift_l = mgr.BVLShl(f, 1)
        print(shift_l)

        shift_r = mgr.BVLShr(f, one)
        print(shift_r)
        shift_r = mgr.BVLShr(f, 1)
        print(shift_r)

        rotate_l = mgr.BVRol(f, 3)
        print(rotate_l)
        rotate_r = mgr.BVRor(f, 2)
        print(rotate_r)

        zero_ext = mgr.BVZExt(one, 64)
        print(zero_ext)

        signed_ext = mgr.BVSExt(one, 64)
        print(signed_ext)

        x = Symbol("x")
        g = And(x, mgr.BVULT(zero, one))
        print(g)
        return

if __name__ == "__main__":
    main()
