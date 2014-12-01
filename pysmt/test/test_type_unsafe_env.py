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
import unittest

from pysmt.test import TestCase
from pysmt.typing import REAL, INT
from pysmt.shortcuts import get_env, Symbol, Plus, ToReal, push_env, pop_env
from pysmt.environment import TypeUnsafeEnvironment, Environment


class TestTypeUnsafeEnvironment(TestCase):

    def test_check(self):
        """
        Checks that the default environment does not allow for type
        unsafety with Plus
        """

        a = Symbol("A", REAL)
        b = Symbol("B", INT)

        with self.assertRaises(TypeError):
            Plus(a, b)


    def test_with_env(self):
        safe_a = Symbol("A", REAL)
        safe_c = Symbol("C", REAL)
        safe_plus = Plus(safe_a, safe_c)

        with TypeUnsafeEnvironment() as unsafe_env:
            unsafe_a = Symbol("A", REAL)
            unsafe_b = Symbol("B", INT)
            plus = Plus(unsafe_a, unsafe_b)
            unsafe_plus = plus.substitute({unsafe_b: Symbol("C", REAL)})

            self.assertNotEquals(unsafe_a, safe_a)
            self.assertNotEquals(safe_plus, unsafe_plus)

            normalized_plus = unsafe_env.formula_manager.normalize(safe_plus)
            self.assertEquals(normalized_plus, unsafe_plus)


    def test_toreal(self):
        a = Symbol("A", REAL)
        with TypeUnsafeEnvironment():
            self.assertNotEquals(a, ToReal(a))


    def test_push_env(self):
        # TODO: Change as in _with
        safe_a = Symbol("A", REAL)
        safe_c = Symbol("C", REAL)
        safe_plus = Plus(safe_a, safe_c)

        unsafe_env = TypeUnsafeEnvironment()
        push_env(unsafe_env)
        unsafe_a = Symbol("A", REAL)
        unsafe_b = Symbol("B", INT)
        plus = Plus(unsafe_a, unsafe_b)
        unsafe_plus = plus.substitute({unsafe_b: Symbol("C", REAL)})

        self.assertNotEquals(unsafe_a, safe_a)
        self.assertNotEquals(safe_plus, unsafe_plus)

        normalized_plus = unsafe_env.formula_manager.normalize(safe_plus)
        self.assertEquals(normalized_plus, unsafe_plus)
        pop_env()



    def test_direct(self):
        safe_env = Environment()
        safe_mgr = safe_env.formula_manager
        safe_a = safe_mgr.Symbol("A", REAL)
        safe_c = safe_mgr.Symbol("C", REAL)
        safe_plus = safe_mgr.Plus(safe_a, safe_c)

        tue = TypeUnsafeEnvironment()
        unsafe_a = tue.formula_manager.Symbol("A", REAL)
        unsafe_b = tue.formula_manager.Symbol("B", INT)
        unsafe_c = tue.formula_manager.Symbol("C", REAL)
        unsafe_p = tue.formula_manager.Plus(unsafe_a, unsafe_b)
        unsafe_trg = tue.formula_manager.Plus(unsafe_a, unsafe_c)

        unsafe_plus = tue.substituter.substitute(unsafe_p,
                                                {unsafe_b: unsafe_c })

        self.assertEquals(unsafe_trg, unsafe_plus,
                          "%s != %s" % (id(unsafe_trg), id(unsafe_plus)))

        self.assertNotEquals(unsafe_a, safe_a)
        self.assertNotEquals(safe_plus, unsafe_plus)

        normalized_plus = tue.formula_manager.normalize(safe_plus)
        self.assertEquals(normalized_plus, unsafe_plus,
                          "%s != %s" % (id(normalized_plus), id(unsafe_plus)))


if __name__ == '__main__':
    unittest.main()
