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
from pysmt.typing import REAL, INT
from pysmt.test import TestCase, skipIfSolverNotAvailable, main
from pysmt.exceptions import NoSolverAvailableError
from pysmt.logics import UFLIRA


class TestInterpolation(TestCase):
    def test_selection(self):
        with self.assertRaises(NoSolverAvailableError):
            Interpolator(logic=UFLIRA)

        with self.assertRaises(NoSolverAvailableError):
            Interpolator(name="nonexistent")

    @skipIfSolverNotAvailable('msat')
    def test_binary_interpolant_msat(self):
        self._test_binary_interpolant('msat')

    @skipIfSolverNotAvailable('msat')
    def test_sequence_interpolant_msat(self):
        self._test_sequence_interpolant('msat')

    def _test_binary_interpolant(self, name):
        itp = Interpolator(name=name)
        self._bool_example(itp, True)
        self._real_example(itp, True)
        self._int_example(itp, True)

    def _test_sequence_interpolant(self, name):
        itp = Interpolator(name=name)
        self._bool_example(itp, False)
        self._real_example(itp, False)
        self._int_example(itp, False)

    @skipIfSolverNotAvailable('msat')
    def test_context(self):
        with Interpolator() as itp:
            self._bool_example(itp, False)

    def _bool_example(self, itp, binary):
        # Bool Example
        x, y, z = Symbol("bx"), Symbol("by"), Symbol("bz")

        a = And(x, Not(y))
        b = And(Implies(z, y), z)

        if binary:
            i = itp.binary_interpolant(a, b)
        else:
            i = itp.sequence_interpolant([a, b])

        self.assertTrue(i is not None)
        if not binary:
            self.assertTrue(hasattr(i, '__len__'))
            self.assertTrue(len(i) == 1)
            i = i[0]

        self.assertTrue(i.get_free_variables() == set([y]))
        self.assertValid(Implies(a, i))
        self.assertUnsat(And(i, b))


    def _real_example(self, itp, binary):
        # Real Example
        x, y, z = Symbol("rx", REAL), Symbol("ry", REAL), Symbol("rz", REAL)

        a = And(LE(x, Real(0)), LE(y, x))
        b = And(GE(y, z), Equals(z, Real(1)))

        if binary:
            i = itp.binary_interpolant(a, b)
        else:
            i = itp.sequence_interpolant([a, b])

        self.assertTrue(i is not None)
        if not binary:
            self.assertTrue(hasattr(i, '__len__'))
            self.assertTrue(len(i) == 1)
            i = i[0]

        self.assertTrue(i.get_free_variables() == set([y]))
        self.assertValid(Implies(a, i))
        self.assertUnsat(And(i, b))


    def _int_example(self, itp, binary):
        # Int Example
        x, y, z = Symbol("ix", INT), Symbol("iy", INT), Symbol("iz", INT)

        a = And(LE(x, Int(1)), LT(y, x))
        b = And(GE(y, z), GT(z, Int(0)))

        if binary:
            i = itp.binary_interpolant(a, b)
        else:
            i = itp.sequence_interpolant([a, b])

        self.assertTrue(i is not None)
        if not binary:
            self.assertTrue(hasattr(i, '__len__'))
            self.assertTrue(len(i) == 1)
            i = i[0]

        self.assertTrue(i.get_free_variables() == set([y]))
        self.assertValid(Implies(a, i))
        self.assertUnsat(And(i, b))


if __name__ == '__main__':
    main()
