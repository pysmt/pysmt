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
from pysmt.typing import REAL, BOOL, INT, FunctionType, BV8
from pysmt.type_checker import (assert_no_boolean_in_args,
                                assert_boolean_args,
                                assert_same_type_args,
                                assert_args_type_in)
from pysmt.shortcuts import (Symbol, And, Plus, Minus, Times, Equals, Or, Iff,
                             LE, LT, Not, GE, GT, Ite, Bool, Int, Real, Div,
                             Function)
from pysmt.environment import get_env
from pysmt.exceptions import PysmtTypeError
from pysmt.test import TestCase, main
from pysmt.test.examples import get_example_formulae
from pysmt.decorators import typecheck_result


class TestSimpleTypeChecker(TestCase):

    def setUp(self):
        super(TestSimpleTypeChecker, self).setUp()

        self.tc = get_env().stc
        self.x = Symbol("x", BOOL)
        self.y = Symbol("y", BOOL)
        self.p = Symbol("p", INT)
        self.q = Symbol("q", INT)
        self.r = Symbol("r", REAL)
        self.s = Symbol("s", REAL)

        self.qfo = get_env().qfo


    def test_boolean(self):
        varA = Symbol("At", INT)
        varB = Symbol("Bt", INT)

        f = And(LT(varA, Plus(varB, Int(1))),
                GT(varA, Minus(varB, Int(1))))
        g = Equals(varA, varB)
        h = Iff(f, g)

        tc = get_env().stc
        res = tc.walk(h)
        self.assertEqual(res, BOOL)


    def test_arith_relations(self):
        self.assertEqual(self.tc.walk(LE(self.p, self.q)), BOOL)
        self.assertEqual(self.tc.walk(LT(self.p, self.q)), BOOL)
        self.assertEqual(self.tc.walk(LE(self.r, self.s)), BOOL)
        self.assertEqual(self.tc.walk(LT(self.r, self.s)), BOOL)

        with self.assertRaises(PysmtTypeError):
            LE(self.p, self.r)
        with self.assertRaises(PysmtTypeError):
            LT(self.p, self.r)
        with self.assertRaises(PysmtTypeError):
            LE(self.x, self.y)
        with self.assertRaises(PysmtTypeError):
            LT(self.x, self.y)

        bv_a = Symbol("BV_A", BV8)
        bv_b = Symbol("BV_B", BV8)

        with self.assertRaises(PysmtTypeError):
            LE(bv_a, bv_b)
        with self.assertRaises(PysmtTypeError):
            LT(bv_a, bv_b)


    def test_functions(self):
        vi = Symbol("At", INT)
        vr = Symbol("Bt", REAL)

        f = Symbol("f", FunctionType(INT, [REAL]))
        g = Symbol("g", FunctionType(REAL, [INT]))

        tc = get_env().stc

        self.assertEqual(tc.walk(Function(f, [vr])), INT)
        self.assertEqual(tc.walk(Function(g, [vi])), REAL)
        self.assertEqual(tc.walk(Function(f, [Function(g, [vi])])), INT)
        self.assertEqual(tc.walk(LE(Plus(vi, Function(f, [Real(4)])), Int(8))), BOOL)
        self.assertEqual(tc.walk(LE(Plus(vr, Function(g, [Int(4)])), Real(8))), BOOL)

        with self.assertRaises(PysmtTypeError):
            LE(Plus(vr, Function(g, [Real(4)])), Real(8))

        with self.assertRaises(PysmtTypeError):
            LE(Plus(vi, Function(f, [Int(4)])), Int(8))



    def test_walk_type_to_type(self):
        # TODO: this exploits a private service of the type checker,
        # we should test the external interface
        f = self.x
        args1 = [BOOL, BOOL]
        args2 = [BOOL, REAL]
        args3 = [None, None]

        t = self.tc.walk_type_to_type(f, args1, BOOL, REAL)
        self.assertEqual(t, REAL)

        t = self.tc.walk_type_to_type(f, args2, BOOL, REAL)
        self.assertEqual(t, None)

        t = self.tc.walk_type_to_type(f, args3, BOOL, REAL)
        self.assertEqual(t, None)

    def test_misc(self):
        bool_list = [
            And(self.x, self.y),
            Or(self.x, self.y),
            Not(self.x),
            self.x,
            Equals(self.p, self.q),
            GE(self.p, self.q),
            LE(self.p, self.q),
            GT(self.p, self.q),
            LT(self.p, self.q),
            Bool(True),
            Ite(self.x, self.y, self.x)
        ]

        # TODO: FORALL EXISTS
        real_list = [
            self.r,
            Real(4),
            Plus(self.r, self.s),
            Plus(self.r, Real(2)),
            Minus(self.s, self.r),
            Times(self.r, Real(1)),
            Div(self.r, Real(1)),
            Ite(self.x, self.r, self.s),
        ]

        int_list = [
            self.p,
            Int(4),
            Plus(self.p, self.q),
            Plus(self.p, Int(2)),
            Minus(self.p, self.q),
            Times(self.p, Int(1)),
            Ite(self.x, self.p, self.q),
        ]

        for f in bool_list:
            t = self.tc.walk(f)
            self.assertEqual(t, BOOL, f)

        for f in real_list:
            t = self.tc.walk(f)
            self.assertEqual(t, REAL, f)

        for f in int_list:
            t = self.tc.walk(f)
            self.assertEqual(t, INT, f)


    def test_assert_args(self):
        assert_no_boolean_in_args([self.r, self.p])
        with self.assertRaises(PysmtTypeError):
            assert_no_boolean_in_args([self.x, self.y])

        assert_boolean_args([self.x, self.y])
        with self.assertRaises(PysmtTypeError):
            assert_boolean_args([self.r, self.p])

        assert_same_type_args([self.x, self.y])
        with self.assertRaises(PysmtTypeError):
            assert_same_type_args([self.r, self.p])

        assert_args_type_in([self.x, self.p],
                            allowed_types=[INT, BOOL])
        with self.assertRaises(PysmtTypeError):
            assert_args_type_in([self.x, self.p],
                                allowed_types=[REAL, BOOL])


    def test_decorator_typecheck_result(self):
        from pysmt.fnode import FNode, FNodeContent
        from pysmt.operators import AND
        @typecheck_result
        def good_function():
            return self.x

        @typecheck_result
        def super_bad_function():
            sb = FNode(FNodeContent(node_type=AND, args=(self.p, self.p),
                                    payload=None), -1)
            return sb

        good_function()

        with self.assertRaises(PysmtTypeError):
            super_bad_function()

    def test_examples(self):
        for (f, _, _, _) in get_example_formulae():
            self.assertIs(f.get_type(), BOOL, f)

if __name__ == '__main__':
    main()
