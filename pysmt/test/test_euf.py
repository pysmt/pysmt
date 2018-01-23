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
from pysmt.shortcuts import *
from pysmt.typing import INT, REAL, FunctionType, BV16
from pysmt.logics import UFLRA, UFLIRA
from pysmt.test import TestCase, main
from pysmt.test import skipIfNoSolverForLogic
from pysmt.exceptions import PysmtModeError, PysmtValueError


class TestEUF(TestCase):

    @skipIfNoSolverForLogic(UFLIRA)
    def test_euf(self):
        ftype1 = FunctionType(REAL, [REAL])
        ftype2 = FunctionType(REAL, [REAL, INT])

        f = Symbol("f", ftype1)
        g = Symbol("g", ftype2)

        check = Equals(Function(f, [Real(1)]), Function(g, (Real(2), Int(4))))

        self.assertSat(check, logic=UFLIRA,
                       msg="Formula was expected to be sat")


    def test_infix(self):
        ftype1 = FunctionType(REAL, [REAL])
        ftype2 = FunctionType(REAL, [REAL, INT])
        f = Symbol("f", ftype1)
        g = Symbol("g", ftype2)

        with self.assertRaises(PysmtModeError):
            f(1.0)

        get_env().enable_infix_notation = True

        infix = Equals(f(1.0), g(2.0, 4))
        explicit = Equals(Function(f, [Real(1.0)]), Function(g, [Real(2.0), Int(4)]))
        self.assertEqual(infix, explicit)

        ftype1 = FunctionType(REAL, [BV16])
        ftype2 = FunctionType(BV16, [INT, BV16])
        f = Symbol("bvf", ftype1)
        g = Symbol("bvg", ftype2)
        infix = Equals(f(g(2, 6)), Real(0))
        explicit = Equals(Function(f, [Function(g, [Int(2), BV(6, 16)])]), Real(0))
        self.assertEqual(infix, explicit)

        with self.assertRaises(PysmtValueError):
            f(BV(6, 16), BV(8, 16))

        ftype3 = FunctionType(REAL, [])
        h = Symbol("h", ftype3)
        with self.assertRaises(PysmtValueError):
            h()

    @skipIfNoSolverForLogic(UFLRA)
    def test_quantified_euf(self):
        ftype1 = FunctionType(REAL, [REAL, REAL])

        plus = Symbol("plus", ftype1)
        x = Symbol('x', REAL)
        y = Symbol('y', REAL)
        z = Symbol('z', REAL)

        axiom = ForAll([x, y], Equals(Function(plus, (x, y)), Plus(x, y)))

        test1 = Equals(Plus(z, Real(4)), Function(plus, (Real(4), z)))
        test2 = Equals(Function(plus, (Real(5), Real(4))), Real(9))

        check = Implies(axiom, And(test1, test2))

        self.assertValid(check, logic=UFLRA,
                        msg="Formula was expected to be valid")


    def test_simplify(self):
        ftype1 = FunctionType(REAL, [REAL, REAL])

        plus = Symbol("plus", ftype1)
        x = Symbol('x', REAL)
        y = Symbol('y', REAL)
        z = Symbol('z', REAL)

        f = Function(plus, (Minus(Real(5), Real(5)),
                            Plus(y, Minus(z, z))))
        self.assertEqual(Function(plus, (Real(0), y)),
                          f.simplify())

if __name__ == '__main__':
    main()
