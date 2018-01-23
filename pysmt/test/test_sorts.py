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
from six import StringIO

from pysmt.shortcuts import FreshSymbol, EqualsOrIff, Select, TRUE, FALSE, Function
from pysmt.shortcuts import Array, BV
from pysmt.typing import INT, BOOL, REAL
from pysmt.typing import Type, ArrayType, FunctionType, BVType
from pysmt.typing import PartialType
from pysmt.test import TestCase, main
from pysmt.smtlib.parser import SmtLibParser
from pysmt.exceptions import PysmtValueError, PysmtTypeError


SMTLIB_SRC="""\
(define-sort Set (T) (Array T Bool))
(define-sort I () Int)

(declare-const s1 (Set I))
(declare-const a I)
(declare-const b Int)

(assert (= (select s1 a) true))
(assert (= (select s1 b) false))
(check-sat)
"""

class TestSorts(TestCase):

    def test_smtlib_sort(self):
        # parser = SmtLibParser()
        # buf = StringIO(SMTLIB_SRC)
        # script = parser.get_script(buf)
        pass

    def test_basic_types(self):
        self.assertTrue(BOOL.is_bool_type())
        self.assertFalse(BOOL.is_function_type())

        self.assertTrue(REAL.is_real_type())
        self.assertFalse(REAL.is_bool_type())

        self.assertTrue(INT.is_int_type())
        self.assertFalse(INT.is_real_type())

        ftype = FunctionType(REAL, [REAL, REAL])
        self.assertTrue(ftype.is_function_type())
        self.assertFalse(ftype.is_int_type())

        self.assertNotEqual(BOOL, INT)
        self.assertEqual(REAL, REAL)

        AAIBR = ArrayType(ArrayType(INT, BOOL), REAL)
        self.assertEqual(str(AAIBR), "Array{Array{Int, Bool}, Real}")

        bt1 = BVType(4)
        bt2 = BVType(4)
        self.assertEqual(bt1, bt2)
        self.assertEqual(bt1.width, 4)

    def test_fake_arrays(self):
        FakeArrayType = Type("FakeArray", 2)
        with self.assertRaises(PysmtValueError):
            FreshSymbol(FakeArrayType)
        FakeArrayII = self.env.type_manager.get_type_instance(FakeArrayType, INT, INT)
        self.assertEqual(str(FakeArrayII), "FakeArray{Int, Int}")
        self.assertEqual(FakeArrayII.as_smtlib(False), "(FakeArray Int Int)")
        s = FreshSymbol(FakeArrayII)
        self.assertIsNotNone(s)

    def test_simple_sorts(self):
        # (define-sort I () Int)
        # (define-sort Set (T) (Array T Bool))
        I = INT
        SET = PartialType("Set", lambda t1: ArrayType(t1, BOOL))
        self.assertEqual(ArrayType(INT, BOOL), SET(I))

        # (declare-const s1 (Set I))
        # (declare-const a I)
        # (declare-const b Int)
        s1 = FreshSymbol(SET(I))
        a = FreshSymbol(I)
        b = FreshSymbol(INT)

        # (= (select s1 a) true)
        # (= (select s1 b) false)
        f1 = EqualsOrIff(Select(s1, a), TRUE())
        f2 = EqualsOrIff(Select(s1, b), FALSE())
        self.assertIsNotNone(f1)
        self.assertIsNotNone(f2)

        # Cannot instantiate a PartialType directly:
        with self.assertRaises(PysmtValueError):
            FreshSymbol(SET)

        # (declare-sort A 0)
        # Uninterpreted sort
        A = Type("A", 0)
        B = Type("B")

        c1 = FreshSymbol(A)
        c2 = FreshSymbol(A)
        c3 = FreshSymbol(Type("A"))
        c4 = FreshSymbol(B)
        EqualsOrIff(c1, c2)
        EqualsOrIff(c2, c3)
        with self.assertRaises(PysmtTypeError):
            EqualsOrIff(c1, c4)

        with self.assertRaises(PysmtValueError):
            Type("A", 1)

        C = Type("C", 1)
        CA = self.env.type_manager.get_type_instance(C, A)
        CB = self.env.type_manager.get_type_instance(C, B)
        c5 = FreshSymbol(CA)
        c6 = FreshSymbol(CB)
        self.assertIsNotNone(c5)
        with self.assertRaises(PysmtTypeError):
            EqualsOrIff(c5, c6)

        # Nesting
        self.env.enable_infix_notation = True
        ty = C(C(C(C(C(A)))))
        self.assertIsNotNone(FreshSymbol(ty))

        pty = PartialType("pty", lambda S,T: S(S(S(S(S(T))))))
        self.assertEqual(pty(C,A), ty)

    def test_normalization(self):
        from pysmt.environment import Environment

        env2 = Environment()
        mgr2 = env2.formula_manager

        ty = ArrayType(BOOL, REAL)
        x = FreshSymbol(ty)
        fty = FunctionType(BOOL, (ty,))
        f = FreshSymbol(fty)
        g = Function(f, (x,))
        self.assertIsNotNone(g)
        self.assertNotIn(g, mgr2)
        g2 = mgr2.normalize(g)
        self.assertIn(g2, mgr2)
        # Since the types are from two different environments, they
        # should be different.
        x2 = g2.arg(0)
        ty2 = x2.symbol_type()
        self.assertFalse(ty2 is ty, ty)
        fname = g2.function_name()
        fty2 = fname.symbol_type()
        self.assertFalse(fty2 is fty, fty)

        # Test ArrayValue
        h = Array(BVType(4), BV(0, 4))
        h2 = mgr2.normalize(h)
        self.assertEqual(h.array_value_index_type(),
                         h2.array_value_index_type())
        self.assertFalse(h.array_value_index_type() is \
                         h2.array_value_index_type())

    def test_check_types_in_constructors(self):
        with self.assertRaises(PysmtValueError):
            ArrayType(INT, BV)

        with self.assertRaises(PysmtValueError):
            ArrayType(BV, INT)

        with self.assertRaises(PysmtValueError):
            FunctionType(BV, (REAL,))

        with self.assertRaises(PysmtValueError):
            FunctionType(REAL, (BV,))

if __name__ == '__main__':
    main()
