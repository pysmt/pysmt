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
"""Describe all logics supported by pySMT and other logics defined in
the SMTLIB and provides methods to compare and search for particular
logics.
"""

from pysmt.exceptions import UndefinedLogicError, NoLogicAvailableError

class Logic(object):
    """Describes a Logic similarly to the way they are defined in the SMTLIB 2.0

    Note: We define more Logics than the ones defined in the SMTLib
    2.0.  See LOGICS for a list of all the logics and SMTLIB2_LOGICS
    for the restriction to the ones defined in SMTLIB2.0
    """

    def __init__(self, name, description,
                 quantifier_free = False,
                 arrays = False,
                 bit_vectors = False,
                 floating_point = False,
                 integer_arithmetic = False,
                 real_arithmetic = False,
                 integer_difference = False,
                 real_difference = False,
                 linear = False,
                 non_linear = False,
                 uninterpreted = False):

        self.name = name
        self.description = description
        self.quantifier_free = quantifier_free
        self.arrays = arrays
        self.bit_vectors = bit_vectors
        self.floating_point = floating_point
        self.integer_arithmetic = integer_arithmetic
        self.real_arithmetic = real_arithmetic
        self.integer_difference = integer_difference
        self.real_difference = real_difference
        self.linear = linear
        self.non_linear = non_linear
        self.uninterpreted = uninterpreted

        return

    def __str__(self):
        return self.name

    def __repr__(self):
        return str(self)

    def __eq__(self, other):
        if other is None or (not isinstance(other, Logic)):
            return False

        return self.name == other.name and \
            self.description == other.description and \
            self.quantifier_free == other.quantifier_free and \
            self.arrays == other.arrays and \
            self.bit_vectors == other.bit_vectors and \
            self.floating_point == other.floating_point and \
            self.integer_arithmetic == other.integer_arithmetic and \
            self.real_arithmetic == other.real_arithmetic and \
            self.integer_difference == other.integer_difference and \
            self.real_difference == other.real_difference and \
            self.linear == other.linear and \
            self.non_linear == other.non_linear and \
            self.uninterpreted == other.uninterpreted

    def __ne__(self, other):
        return not (self == other)

    def __lt__(self, other):
        return (self != other) and (self.__le__(other))

    def __le__(self, other):
        if self.integer_difference == other.integer_difference:
            le_integer_difference = True
        elif self.integer_difference and not other.integer_arithmetic:
            le_integer_difference = False
        else:
            le_integer_difference = True

        if self.real_difference == other.real_difference:
            le_real_difference = True
        elif self.real_difference and not other.real_arithmetic:
            le_real_difference = False
        else:
            le_real_difference = True

        return ((self.quantifier_free >= other.quantifier_free) and
                (self.arrays <= other.arrays) and
                (self.bit_vectors <= other.bit_vectors) and
                (self.floating_point <= other.floating_point) and
                (self.uninterpreted <= other.uninterpreted) and
                (le_integer_difference) and
                (self.integer_arithmetic <= other.integer_arithmetic) and
                (le_real_difference) and
                (self.real_arithmetic <= other.real_arithmetic) and
                (self.linear <= other.linear) and
                (self.non_linear <= other.non_linear)
            )

    def __ge__(self, other):
        return (other.__le__(self))

    def __gt__(self, other):
        return other.__lt__(self)


# Logics

QF_BOOL = Logic(name="QF_BOOL",
                description=\
                """The simplest logic: quantifier-free boolean logic.""",
                quantifier_free=True)


BOOL = Logic(name="BOOL",
             description=\
             """Quantified boolean logic.""")
QBF=BOOL # Provide additional name for consistency with literature


AUFLIA = Logic(name="AUFLIA",
               description=\
"""Closed formulas over the theory of linear integer arithmetic and
arrays extended with free sort and function symbols but restricted to
arrays with integer indices and values.""",
               arrays=True,
               integer_arithmetic=True,
               linear=True,
               uninterpreted=True)

ALIA = Logic(name="ALIA",
             description=\
"""Closed formulas over the theory of linear integer arithmetic and
arrays.""",
             arrays=True,
             integer_arithmetic=True,
             linear=True)


AUFLIRA = Logic(name="AUFLIRA",
                description=\
"""Closed linear formulas with free sort and function symbols over
one- and two-dimentional arrays of integer index and real value.""",
                arrays=True,
                integer_arithmetic=True,
                real_arithmetic=True,
                linear=True,
                uninterpreted=True)


AUFNIRA = Logic(name="AUFNIRA",
                description=\
"""Closed formulas with free function and predicate symbols over a
theory of arrays of arrays of integer index and real value.""",
                arrays=True,
                integer_arithmetic=True,
                real_arithmetic=True,
                non_linear=True,
                uninterpreted=True)


LRA = Logic(name="LRA",
            description=\
"""Closed linear formulas in linear real arithmetic.""",
            real_arithmetic=True,
            linear=True)


LIA = Logic(name="LIA",
            description=\
"""Closed linear formulas in linear integer arithmetic.""",
            integer_arithmetic=True,
            linear=True)

UFLIRA = Logic(name="UFLIRA",
                description=\
"""Closed linear formulas with free sort and function symbols in
linear and real arithmetic.""",
                integer_arithmetic=True,
                real_arithmetic=True,
                linear=True,
                uninterpreted=True)

QF_UFLIRA = Logic(name="QF_UFLIRA",
                description=\
"""Quantifier-free, closed linear formulas with free sort and function symbols in
linear and real arithmetic.""",
                integer_arithmetic=True,
                real_arithmetic=True,
                linear=True,
                quantifier_free=True,
                uninterpreted=True)

NIA = Logic(name="NIA",
            description=\
"""Closed formulas in non-linear integer arithmetic.""",
            integer_arithmetic=True)


NRA = Logic(name="NRA",
            description=\
"""Closed formulas in non-linear real arithmetic.""",
            real_arithmetic=True)


QF_ABV = Logic(name="QF_ABV",
               description=\
"""Closed quantifier-free formulas over the theory of bitvectors and
bitvector arrays.""",
               quantifier_free=True,
               arrays=True,
               bit_vectors=True)


QF_AUFBV = Logic(name="QF_AUFBV",
                 description=\
"""Closed quantifier-free formulas over the theory of bitvectors and
bitvector arrays extended with free sort and function symbols.""",
                 quantifier_free=True,
                 arrays=True,
                 bit_vectors=True,
                 uninterpreted=True)


QF_AUFLIA = Logic(name="QF_AUFLIA",
                  description=\
"""Closed quantifier-free linear formulas over the theory of integer
arrays extended with free sort and function symbols.""",
                  quantifier_free=True,
                  arrays=True,
                  integer_arithmetic=True,
                  linear=True,
                  uninterpreted=True)


QF_ALIA = Logic(name="QF_ALIA",
                description=\
"""Closed quantifier-free linear formulas over the theory of integer
arrays.""",
                quantifier_free=True,
                arrays=True,
                integer_arithmetic=True,
                linear=True)


QF_AX = Logic(name="QF_AX",
              description=\
"""Closed quantifier-free formulas over the theory of arrays with
extensionality.""",
              quantifier_free=True,
              arrays=True)


QF_BV = Logic(name="QF_BV",
              description=\
"""Closed quantifier-free formulas over the theory of fixed-size
bitvectors.""",
              quantifier_free=True,
              bit_vectors=True)


QF_IDL = Logic(name="QF_IDL",
               description=\
"""Difference Logic over the integers. In essence, Boolean
combinations of inequations of the form x - y < b where x and y are
integer variables and b is an integer constant.""",
               quantifier_free=True,
               integer_arithmetic=True,
               integer_difference=True)


QF_LIA = Logic(name="QF_LIA",
               description=\
"""Unquantified linear integer arithmetic. In essence, Boolean
combinations of inequations between linear polynomials over integer
variables.""",
               quantifier_free=True,
               integer_arithmetic=True,
               linear=True)


QF_LRA = Logic(name="QF_LRA",
                      description=\
"""Unquantified linear real arithmetic. In essence, Boolean
combinations of inequations between linear polynomials over real
variables.""",
                            quantifier_free=True,
                            real_arithmetic=True,
                            linear=True)


QF_NIA = Logic(name="QF_NIA",
                      description=\
"""Quantifier-free integer arithmetic.""",
                            quantifier_free=True,
                            integer_arithmetic=True,
                            non_linear=True)


QF_NRA = Logic(name="QF_NRA",
                      description=\
                      """Quantifier-free real arithmetic.""",
                            quantifier_free=True,
                            real_arithmetic=True,
                            non_linear=True)


QF_RDL = Logic(name="QF_RDL",
                      description=\
"""Difference Logic over the reals. In essence, Boolean combinations
of inequations of the form x - y < b where x and y are real variables
and b is a rational constant.""",
               real_arithmetic=True,
               quantifier_free=True,
               real_difference=True)


QF_UF = Logic(name="QF_UF",
                     description=\
"""Unquantified formulas built over a signature of uninterpreted
(i.e., free) sort and function symbols.""",
                            quantifier_free=True,
                            uninterpreted=True)


QF_UFBV = Logic(name="QF_UFBV",
                       description=\
"""Unquantified formulas over bitvectors with uninterpreted sort
function and symbols.""",
                            quantifier_free=True,
                            bit_vectors=True,
                            uninterpreted=True)


QF_UFIDL = Logic(name="QF_UFIDL",
                        description=\
"""Difference Logic over the integers (in essence) but with
uninterpreted sort and function symbols?""",
                            quantifier_free=True,
                            integer_arithmetic=True,
                            integer_difference=True,
                            uninterpreted=True)


QF_UFLIA = Logic(name="QF_UFLIA",
                 description=\
"""Unquantified linear integer arithmetic with uninterpreted sort and
function symbols.""",
                 quantifier_free=True,
                 integer_arithmetic=True,
                 linear=True,
                 uninterpreted=True)


QF_UFLRA = Logic(name="QF_UFLRA",
                 description=\
"""Unquantified linear real arithmetic with uninterpreted sort and
function symbols.""",
                 quantifier_free=True,
                 real_arithmetic=True,
                 linear=True,
                 uninterpreted=True)


QF_UFNRA = Logic(name="QF_UFNRA",
                 description=\
"""Unquantified non-linear real arithmetic with uninterpreted sort and
function symbols.""",
                 quantifier_free=True,
                 real_arithmetic=True,
                 non_linear=True,
                 uninterpreted=True)


QF_UFNIA = Logic(name="QF_UFNIA",
                 description=\
"""Unquantified non-linear integer arithmetic with uninterpreted sort and
function symbols.""",
                 quantifier_free=True,
                 integer_arithmetic=True,
                 non_linear=True,
                 uninterpreted=True)


UFLRA = Logic(name="UFLRA",
              description=\
"""Linear real arithmetic with uninterpreted sort and function
symbols.""",
              real_arithmetic=True,
              linear=True,
              uninterpreted=True)


UFNIA = Logic(name="UFNIA",
              description=\
"""Non-linear integer arithmetic with uninterpreted sort and function
symbols.""",
              integer_difference=True,
              non_linear=True,
              uninterpreted=True)


SMTLIB2_LOGICS = [ AUFLIA,
                   AUFLIRA,
                   AUFNIRA,
                   ALIA,
                   LRA,
                   LIA,
                   NIA,
                   NRA,
                   UFLRA,
                   UFNIA,
                   UFLIRA,
                   QF_ABV,
                   QF_AUFBV,
                   QF_AUFLIA,
                   QF_ALIA,
                   QF_AX,
                   QF_BV,
                   QF_IDL,
                   QF_LIA,
                   QF_LRA,
                   QF_NIA,
                   QF_NRA,
                   QF_RDL,
                   QF_UF,
                   QF_UFBV ,
                   QF_UFIDL,
                   QF_UFLIA,
                   QF_UFLRA,
                   QF_UFNRA,
                   QF_UFNIA,
                   QF_UFLIRA
               ]

LOGICS = SMTLIB2_LOGICS + [ QF_BOOL, BOOL ]

QF_LOGICS = [l for l in LOGICS if l.quantifier_free]

#
# This is the set of logics supported by the current version of pySMT
#
PYSMT_LOGICS = [QF_BOOL, QF_IDL, QF_LIA, QF_LRA, QF_RDL, QF_UF, QF_UFIDL,
                QF_UFLIA, QF_UFLRA, QF_UFLIRA,
                BOOL, LRA, LIA, UFLIRA ]

PYSMT_QF_LOGICS = [l for l in PYSMT_LOGICS if l.quantifier_free]


def get_logic_by_name(name):
    """Returns the Logic that matches the provided name."""

    for logic in LOGICS:
        if logic.name == name: return logic
    raise UndefinedLogicError(name)

def get_logic_name(quantifier_free=False,
                   arrays=False,
                   bit_vectors=False,
                   floating_point=False,
                   integer_arithmetic=False,
                   real_arithmetic=False,
                   integer_difference=False,
                   real_difference=False,
                   linear=False,
                   non_linear=False,
                   uninterpreted=False):
    """Returns the name of the Logic that matches the given properties."""

    return get_logic(quantifier_free,
                     arrays,
                     bit_vectors,
                     floating_point,
                     integer_arithmetic,
                     real_arithmetic,
                     integer_difference,
                     real_difference,
                     linear,
                     non_linear,
                     uninterpreted).name

def get_logic(quantifier_free=False,
              arrays=False,
              bit_vectors=False,
              floating_point=False,
              integer_arithmetic=False,
              real_arithmetic=False,
              integer_difference=False,
              real_difference=False,
              linear=False,
              non_linear=False,
              uninterpreted=False):
    """Returns the Logic that matches the given properties.

    Equivalent (but better) to executing get_logic_by_name(get_logic_name(...))
    """

    for logic in LOGICS:
        if logic.quantifier_free == quantifier_free and \
           logic.arrays == arrays and \
           logic.bit_vectors == bit_vectors and \
           logic.floating_point == floating_point and \
           logic.integer_arithmetic == integer_arithmetic and \
           logic.real_arithmetic == real_arithmetic and \
           logic.integer_difference == integer_difference and \
           logic.real_difference == real_difference and \
           logic.linear == linear and \
           logic.non_linear == non_linear and \
           logic.uninterpreted == uninterpreted:
            return logic
    raise UndefinedLogicError


def most_generic_logic(logics):
    """Given a set of logics, return the most generic one.

    If a unique most generic logic does not exists, throw an error.
    """
    res = [ l for l in logics if all(l >= x for x in logics)]

    if len(res) != 1:
        raise NoLogicAvailableError("Could not find the most generic"
                                    "logic for %s." % str(logics))
    return res[0]


def get_closer_logic(supported_logics, logic):
    """
    Returns the smaller supported logic that is greater or equal to
    the given logic. Raises NoLogicAvailableError if the solver
    does not support the given logic.

    """
    res = [l for l in supported_logics if logic <= l]
    if len(res) == 0:
        raise NoLogicAvailableError("Logic %s is not supported" % logic)
    return min(res)
