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
from pysmt.shortcuts import is_sat, is_valid, get_model, is_unsat
from pysmt.typing import FPType, RM, FLOAT16, FLOAT32, FLOAT64, FLOAT128, INT
from pysmt.exceptions import PysmtValueError, PysmtTypeError


class TestBV(TestCase):

    def test_bv(self):
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




if __name__ == "__main__":
    main()
