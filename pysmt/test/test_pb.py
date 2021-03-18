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

from pysmt.shortcuts import Symbol, Int, is_sat
from pysmt.typing import INT, REAL
from pysmt.test import TestCase, skipIfSolverNotAvailable, main
from pysmt.exceptions import PysmtTypeError



class TestPB(TestCase):
    def test_pb(self):
        mgr = self.env.formula_manager
        PbLe = mgr.PbLe
        PbGe = mgr.PbGe
        PbEq = mgr.PbEq

        x = Symbol("x")
        y = Symbol("y")
        z = Symbol("z", INT)
        w = x
        c1 = Int(1)
        c2 = Int(2)
        c3 = Int(3)
        c4 = Int(-4)
        c5 = Int(-2)

        #1x + 2y <= 3
        f1 = PbLe((x, y), (c1, c2), c3)

        #1x + 2y >= 3
        f2 = PbGe((x, y), (c1, c2), c3)

        #1x + 2y = 3
        f3 = PbEq((x, y), (c1, c2), c3)

        #1w + 2y <= 3
        f4 = PbLe((w, y), (c1, c2), c3)

        #2x + (-4)y <= -2
        f5 = PbLe((x, y), (c2, c4), c5)

        self.assertEqual(f1, f4)

        self.assertTrue(is_sat(f1, "z3"))
        self.assertTrue(is_sat(f2, "z3"))
        self.assertTrue(is_sat(f3, "z3"))
        self.assertTrue(is_sat(f4, "z3"))
        self.assertTrue(is_sat(f5, "z3"))

        #Test PB node
        self.assertIsNotNone(f1)
        self.assertIsNotNone(f2)
        self.assertIsNotNone(f3)
        self.assertTrue(f1.is_pble())
        self.assertTrue(f2.is_pbge())
        self.assertTrue(f3.is_pbeq())


        #Type check of arguments
        #Can't use python integer for coefficients and constant
        with self.assertRaises(PysmtTypeError):
            PbLe((x, z), (1, 2), 3)
        with self.assertRaises(PysmtTypeError):
            PbLe((x, y), (c1, 2), 3)
        with self.assertRaises(PysmtTypeError):
            PbLe((x, y), (1, 2), c3)

        with self.assertRaises(PysmtTypeError):
            PbGe((x, z), (1, 2), 3)
        with self.assertRaises(PysmtTypeError):
            PbGe((x, y), (c1, 2), 3)
        with self.assertRaises(PysmtTypeError):
            PbGe((x, y), (1, 2), c3)

        with self.assertRaises(PysmtTypeError):
            PbEq((x, z), (1, 2), 3)
        with self.assertRaises(PysmtTypeError):
            PbEq((x, y), (c1, 2), 3)
        with self.assertRaises(PysmtTypeError):
            PbEq((x, y), (1, 2), c3)

if __name__ == '__main__':
    main()
