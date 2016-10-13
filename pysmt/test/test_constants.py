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
from six import PY2
from pysmt.test import TestCase, main

from pysmt.constants import Fraction, Integer, HAS_GMPY
from pysmt.constants import is_pysmt_fraction, is_pysmt_integer
from pysmt.constants import is_python_integer, is_python_boolean, is_python_rational
from pysmt.constants import pysmt_integer_from_integer
from pysmt.constants import to_python_integer
from pysmt.constants import pysmt_fraction_from_rational


class TestConstants(TestCase):

    def test_is_methods(self):
        from fractions import Fraction as pyFraction

        self.assertFalse(is_pysmt_fraction(4))
        self.assertTrue(is_pysmt_fraction(Fraction(4)))

        self.assertFalse(is_pysmt_integer(4.0))
        self.assertTrue(is_pysmt_integer(Integer(4)))

        self.assertTrue(is_python_integer(int(2)))
        if PY2:
            self.assertTrue(is_python_integer(long(2)))
        if HAS_GMPY:
            from gmpy2 import mpz
            self.assertTrue(is_python_integer(mpz(1)))

        if HAS_GMPY:
            from gmpy2 import mpz, mpq
            self.assertTrue(is_python_rational(mpz(1)))
            self.assertTrue(is_python_rational(mpq(1)))
        if PY2:
            self.assertTrue(is_python_rational(long(1)))

        self.assertTrue(is_python_rational(pyFraction(5)))
        self.assertTrue(is_python_rational(3))

        self.assertTrue(is_python_boolean(True))
        self.assertTrue(is_python_boolean(False))

    def test_pysmt_integer_from_integer(self):
        from fractions import Fraction as pyFraction

        self.assertEqual(Integer(4), pysmt_integer_from_integer(4))
        self.assertEqual(Integer(4), pysmt_integer_from_integer(Integer(4)))
        self.assertEqual(Integer(4), pysmt_integer_from_integer(Fraction(4)))
        self.assertEqual(Integer(4), pysmt_integer_from_integer(pyFraction(4)))

    def test_to_python_integer(self):
        from fractions import Fraction as pyFraction

        res = long(4) if PY2 else int(4)
        self.assertEqual(res, to_python_integer(pysmt_integer_from_integer(4)))
        self.assertEqual(res, to_python_integer(pysmt_integer_from_integer(Integer(4))))
        self.assertEqual(res, to_python_integer(pysmt_integer_from_integer(Fraction(4))))
        self.assertEqual(res, to_python_integer(pysmt_integer_from_integer(pyFraction(4))))


    def test_pysmt_fraction_from_rational(self):
        from fractions import Fraction as pyFraction

        self.assertEqual(Fraction(4,5), pysmt_fraction_from_rational("4/5"))
        self.assertEqual(Fraction(4,5), pysmt_fraction_from_rational(pyFraction(4,5)))
        self.assertEqual(Fraction(4,5), pysmt_fraction_from_rational(Fraction(4,5)))
        self.assertEqual(Fraction(4), pysmt_fraction_from_rational(4))
        self.assertEqual(Fraction(4), pysmt_fraction_from_rational(Integer(4)))


if __name__ == '__main__':
    main()
