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

from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.logics import QF_AUFLIA
from pysmt.typing import ARRAY_INT_INT, ArrayType, INT, REAL
from pysmt.shortcuts import Symbol, Solver, Select, Store, Not, Equals, Int, And, get_type, Real

class TestArray(TestCase):

    def test_array_type(self):
        aii_type = ARRAY_INT_INT
        aii_type2 = ArrayType(INT, INT)
        self.assertEqual(aii_type, aii_type2)

    def test_nested_array_type(self):
        base = ARRAY_INT_INT
        nested = ArrayType(base, base)
        self.assertIsNotNone(nested)

        idx_type = nested.index_type
        elem_type = nested.elem_type
        self.assertEqual(idx_type, base)
        self.assertEqual(elem_type, base)

        # Equality tests
        nested2 = ArrayType(ArrayType(INT, INT),
                            ArrayType(INT, INT))
        self.assertEqual(nested, nested2)

        fake_nested = ArrayType(ArrayType(INT, INT),
                                ArrayType(INT, REAL))
        self.assertNotEqual(nested, fake_nested)


    @skipIfNoSolverForLogic(QF_AUFLIA)
    def test_array(self):
        a = Symbol("a", ARRAY_INT_INT)
        formula = Equals(Select(Store(a, Int(10), Int(100)), Int(10)),
                         Int(100))
        self.assertSat(formula, logic=QF_AUFLIA)

if __name__ == "__main__":
    main()
