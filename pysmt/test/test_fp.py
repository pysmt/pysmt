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
from pysmt.shortcuts import Symbol, And, Equals, TRUE, FreshSymbol
from pysmt.shortcuts import is_sat, is_valid, get_model, is_unsat
from pysmt.typing import FPType, RM, FLOAT16, FLOAT32, FLOAT64, FLOAT128, INT, \
                         BOOL
from pysmt.exceptions import PysmtValueError, PysmtTypeError
from pysmt.environment import get_env


class TestFP(TestCase):

    def setUp(self):
        super(TestFP, self).setUp()

        self.tc = get_env().stc
        self.mgr = get_env().formula_manager

    def test_fp(self):
        # Identity test
        self.assertTrue(FLOAT16.is_fp_type())
        self.assertTrue(RM.is_rm_type())
        self.assertFalse(INT.is_fp_type())
        self.assertFalse(INT.is_rm_type())
        self.assertFalse(FLOAT16.is_rm_type())
        self.assertFalse(RM.is_fp_type())
        # Type Equality
        self.assertTrue(FLOAT16 != FLOAT32)
        self.assertTrue(FLOAT32 != FLOAT64)
        self.assertTrue(FLOAT64 != FLOAT128)
        self.assertFalse(FLOAT16 != FLOAT16)
        self.assertTrue(FLOAT16 == FLOAT16)
        self.assertFalse(FLOAT16 == FPType(1, 2))

    def test_type_checking(self):
        mgr = self.mgr

        # test symbol
        var = Symbol('x', FLOAT16)
        self.assertEqual(self.tc.walk(var), FLOAT16)

        # test constant
        def test_tc_fp_special_const(constructor):
            const = constructor(5, 11)
            self.assertEqual(self.tc.walk(const), FLOAT16)

        for constructor in [mgr.FPPositiveZero, mgr.FPNegativeZero,
                            mgr.FPPositiveInfinity, mgr.FPNegativeInfinity,
                            mgr.FPNaN]:
            test_tc_fp_special_const(constructor)
        for rm in [mgr.FPRNE(), mgr.FPRNA(), mgr.FPRTP(), mgr.FPRTN(),
                   mgr.FPRTZ()]:
            self.assertEqual(self.tc.walk(rm), RM)

        # test operations
        def test_tc_fp_op_wo_rnd(op, arity, ret_type):
            fps = map(lambda i: FreshSymbol(FLOAT16), range(arity))
            self.assertEqual(self.tc.walk(op(*tuple(fps))), ret_type)

            ints = map(lambda i: FreshSymbol(INT), range(arity))
            with self.assertRaises(PysmtTypeError):
                op(*tuple(ints))

        for op, arity in [(mgr.FPAbs, 1), (mgr.FPNeg, 1), (mgr.FPRem, 2),
                          (mgr.FPMin, 2), (mgr.FPMax, 2)]:
            test_tc_fp_op_wo_rnd(op, arity, FLOAT16)

        for op, arity in [(mgr.FPLEQ, 2), (mgr.FPLT, 2), (mgr.FPEQ, 2),
                          (mgr.FPIsNormal, 1), (mgr.FPIsSubnormal, 1),
                          (mgr.FPIsZero, 1), (mgr.FPIsInfinite, 1),
                          (mgr.FPIsNaN, 1), (mgr.FPIsNegative, 1),
                          (mgr.FPIsPositive, 1)]:
            test_tc_fp_op_wo_rnd(op, arity, BOOL)

        def test_tc_fp_op_w_rnd(op, arity):
            rm = FreshSymbol(RM)
            fps = list(map(lambda i: FreshSymbol(FLOAT16), range(arity)))
            self.assertEqual(self.tc.walk(op(*tuple([rm] + fps))), FLOAT16)

            with self.assertRaises(PysmtTypeError):
                op(*tuple([FreshSymbol(INT)] + fps))

            ints = list(map(lambda i: FreshSymbol(INT), range(arity)))
            with self.assertRaises(PysmtTypeError):
                op(*tuple([rm] + ints))

        for op, arity in [(mgr.FPAdd, 2), (mgr.FPSub, 2), (mgr.FPMul, 2),
                          (mgr.FPDiv, 2), (mgr.FPFMA, 3), (mgr.FPSqrt, 1),
                          (mgr.FPRoundToIntegral, 1)]:
            test_tc_fp_op_w_rnd(op, arity)


if __name__ == "__main__":
    main()
