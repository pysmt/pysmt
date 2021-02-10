#!/usr/bin/env python

# Copyright 2014 Andrea Micheli and Marco Gario
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

import os

from pysmt.exceptions import PysmtImportError
# The environment variable can be used to force the configuration
# of the Fraction class.
#
# If it is not set, the default behavior is to use GMPY2 if they are
# installed.
#
# If set to True, GMPY2 are required and and exception will be thrown
# if they are not available
#
# If set to True, Python's Fraction module will be used instead.
#

ENV_USE_GMPY = os.environ.get("PYSMT_GMPY")
if ENV_USE_GMPY is not None:
    ENV_USE_GMPY = ENV_USE_GMPY.lower() in ["true", "1"]

HAS_GMPY = False
try:
    from gmpy2 import mpq, mpz
    HAS_GMPY = True
except ImportError as ex:
    if ENV_USE_GMPY is True:
        raise PysmtImportError(str(ex))

if ENV_USE_GMPY is False:
    # Explicitely disable GMPY
    USE_GMPY = False
elif ENV_USE_GMPY is True:
    # Explicitely enable GMPY
    USE_GMPY = True
else:
    # Enable GMPY if they are available
    USE_GMPY = HAS_GMPY

if HAS_GMPY:
    mpq_type = type(mpq(1,2))
    mpz_type = type(mpz(1))
else:
    mpq_type = None
    mpz_type = None

#
# Fractions using GMPY2
#

from fractions import Fraction as pyFraction
if USE_GMPY:
    Fraction = mpq
else:
    Fraction = pyFraction
FractionClass = type(Fraction(1,2))


def is_pysmt_fraction(var):
    """Tests whether var is a Fraction.

    This takes into account the class being used to represent the Fraction.
    """
    return type(var) == FractionClass

#
# Integers using GMPY2
#
if USE_GMPY:
    Integer = mpz
else:
    Integer = int
IntegerClass = type(Integer(1))


def is_pysmt_integer(var):
    """Tests whether var is an Integer.

    This takes into account the class being used to represent the Integer.
    """
    return type(var) == IntegerClass


def is_python_integer(var):
    """Checks whether var is Python Integer.

    This accounts for: long, int and mpz (if available).
    """
    if type(var) == mpz_type:
        return True
    if type(var) == int:
        return True
    return False


def is_python_rational(var):
    """Tests whether var is a Rational.

    This accounts for: long, int, float, Fraction, mpz, mpq (if available).
    """
    if type(var) == mpz_type or type(var) == mpq_type:
        return True
    if type(var) == pyFraction:
        return True
    if type(var) == int:
        return True
    if type(var) == float:
        return True
    return False


def is_python_boolean(var):
    """Tests whether var is a Boolean."""
    return var is True or var is False


def pysmt_integer_from_integer(value):
    """Return a pysmt Integer for the given value."""
    if type(value) == IntegerClass:
        # Nothing to do
        return value
    return Integer(value)


def to_python_integer(value):
    """Return the python integer value."""
    return int(value)


if USE_GMPY:
    def pysmt_fraction_from_rational(value):
        """Return a pysmt Fraction for the rational value."""
        if type(value) == FractionClass:
            # Nothing to do
            return value
        return Fraction(value)
else:
    def pysmt_fraction_from_rational(value):
        """Return a pysmt Fraction for the rational value."""
        if type(value) == FractionClass:
            # Nothing to do
            return value
        # Python's Fraction is a bit picky, need to
        # construct the object in different ways
        if type(value) == mpq_type:
            n = Integer(value.numerator())
            d = Integer(value.denominator())
            return Fraction(n, d)
        elif type(value) == mpz_type:
            return Fraction(Integer(value))
        else:
            return Fraction(value)

#
# Algebraic Numbers Using Z3
#

USE_Z3 = False
try:
    import z3.z3num
    USE_Z3 = True
except ImportError:
    pass

if USE_Z3:
    class Numeral(z3.z3num.Numeral):
        """Represents a Number (Algebraic)"""
        def __hash__(self):
            return hash(self.sexpr())

else:
    class Numeral(object):
        """Represents a Number (Algebraic)"""
        def __init__(self, obj):
            raise NotImplementedError("Z3 is not installed. "\
                "We currently do not support stand-alone algebraic numbers.")

#
# Strings
#
def is_python_string(str1):
    return type(str1) == str
