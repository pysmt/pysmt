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

#
# Fractions using GMPY2
#

if ENV_USE_GMPY is False:
    from fractions import Fraction
else:
    try:
        from gmpy2 import mpq
        Fraction = mpq
        FractionClass = type(Fraction(1,2))
    except ImportError as ex:
        if ENV_USE_GMPY is True:
            raise ex
        else:
            from fractions import Fraction

FractionClass = type(Fraction(1,2))

def is_fraction(var):
    """Tests whether var is a Fraction.

    This takes into account which library we are using to represent
    fractions, i.e., python standard library or gmpy2.
    """
    # print(type(var), FractionClass, type(var) == FractionClass)
    return type(var) == FractionClass


#
# Algebraic Numbers Using Z3
#
# TODO: Check if this can be represented in gmpy2
#

use_z3 = False
try:
    import z3num
    use_z3 = True
except:
    pass

if use_z3:
    class Numeral(z3num.Numeral):
        """Represents a Number (Algebraic)"""
        def __hash__(self):
            return hash(self.sexpr())

else:
    class Numeral(object):
        """Represents a Number (Algebraic)"""
        def __init__(self, obj):
            raise NotImplementedError("Z3 is not installed. "\
                "We currently do not support stand-alone algebraic numbers.")
