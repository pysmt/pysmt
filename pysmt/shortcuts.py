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
"""Provides the most used functions in a nicely wrapped API.

This module defines a global environment, so that most methods can be
called without the need to specify an environment or a FormulaManager.
Functions trying to access the global environment should use the
method get_env(). Keep in mind that the global state of the
environment might lead to inconsistency and unexpected bugs. This is
particularly true for tests. For tests it is recommended to perform an
environment reset in the setUp phase, to be guaranteed that a fresh
environment is used (this is the default behavior of
:py:class:`pysmt.test.TestCase` ).
"""

# Enable default deprecation warnings!
import os
import warnings
from fractions import Fraction
from typing import Any, Dict, FrozenSet, Iterable, Optional, Sequence, Set, Tuple, Union

import pysmt
from pysmt.fnode import FNode
from pysmt.logics import Logic
from pysmt.substituter import FunctionInterpretation
from pysmt.typing import PySMTType

warnings.filterwarnings('default', module='pysmt')

import pysmt.configuration as config
import pysmt.environment
import pysmt.typing as types
import pysmt.smtlib.parser
import pysmt.smtlib.script
import pysmt.smtlib.printers

# Import types from shortcuts
from pysmt.typing import INT, BOOL, REAL, BVType, FunctionType, ArrayType, Type
# These are to avoid "unused" linting error on exported classes
assert INT or BOOL or REAL or BVType or FunctionType or ArrayType or Type # type: ignore[truthy-function]

def get_env() -> pysmt.environment.Environment:
    """Returns the global environment.

    :returns: The global environment
    :rtype: Environment
    """
    return pysmt.environment.get_env()


def reset_env() -> pysmt.environment.Environment:
    """Resets the global environment, and returns the new one.

    :returns: A new environment after resetting the global environment
    :rtype: Environment
    """
    return pysmt.environment.reset_env()


# Enable by default infix notation
get_env().enable_infix_notation = True


##### Shortcuts for FormulaManager #####
def get_type(formula: FNode) -> Optional[PySMTType]:
    """Returns the type of the formula.

    :param formula: The target formula
    :type  formula: FNode
    :returns: The type of the formula
    """
    return get_env().stc.get_type(formula)


def simplify(formula: FNode) -> FNode:
    """Returns the simplified version of the formula.

    :param formula: The target formula
    :type  formula: FNode
    :returns: The simplified version of the formula
    :rtype: Fnode
    """
    return get_env().simplifier.simplify(formula)


def substitute(formula: FNode, subs: Optional[Dict[FNode, FNode]]=None, interpretations: Optional[Dict[FNode, FunctionInterpretation]]=None) -> FNode:
    """Applies the substitutions defined in the dictionary to the formula.

    :param formula: The target formula
    :type  formula: FNode
    :param subs: Specify the substitutions to apply to the formula
    :type  subs: Optionally a dictionary from FNode to FNode
    :param interpretations: Specify the function interpretations to apply to the formula
    :type  interpretations: Optionally a dictionary from FNode to FunctionInterpretation
    :returns: Formula after applying the substitutions or the interpretations
    :rtype: Fnode
    """
    return get_env().substituter.substitute(formula, subs, interpretations)


def serialize(formula: FNode, threshold: Optional[int]=None) -> str:
    """Provides a string representing the formula.

    :param formula: The target formula
    :type  formula: FNode
    :param threshold: Specify the threshold
    :type  formula: Integer
    :returns: A string representing the formula
    :rtype: string
    """
    return get_env().serializer.serialize(formula,
                                          threshold=threshold)

def get_free_variables(formula: FNode) -> FrozenSet[FNode]:
    """Returns the free variables of the formula.

    :param formula: The target formula
    :type  formula: FNode
    :returns: Free variables in the formula
    """
    return get_env().fvo.get_free_variables(formula)


def get_atoms(formula: FNode) -> FrozenSet[FNode]:
    """Returns the set of atoms of the formula.

    :param formula: The target formula
    :type  formula: FNode
    :returns: the set of atoms of the formula
    """
    return get_env().ao.get_atoms(formula)


def get_formula_size(formula: FNode, measure: Optional[int]=None) -> int:
    """Returns the size of the formula as measured by the given counting type.

    See pysmt.oracles.SizeOracle for details.

    :param formula: The target formula
    :type  formula: FNode
    :param measure: Specify the measure/counting type
    :returns: The size of the formula as measured by the given counting type.
    """
    return get_env().sizeo.get_size(formula, measure)


##### Nodes Creation #####

def ForAll(variables: Iterable[FNode], formula: FNode) -> FNode:
    r""".. math:: \forall v_1, \cdots, v_n . \varphi(v_1, \cdots, v_n)"""
    return get_env().formula_manager.ForAll(variables, formula)


def Exists(variables: Iterable[FNode], formula: FNode) -> FNode:
    r""".. math:: \exists v_1, \cdots, v_n . \varphi(v_1, \cdots, v_n)"""
    return get_env().formula_manager.Exists(variables, formula)


def Function(vname: FNode, params: Sequence[FNode]) -> FNode:
    r""".. math:: vname(p_1, \cdots, p_n)"""
    return get_env().formula_manager.Function(vname, params)


def Not(formula: FNode) -> FNode:
    r""".. math:: \lnot \varphi"""
    return get_env().formula_manager.Not(formula)


def Implies(left: FNode, right: FNode) -> FNode:
    r""".. math:: l \rightarrow r"""
    return get_env().formula_manager.Implies(left, right)


def Iff(left: FNode, right: FNode) -> FNode:
    r""".. math:: l \leftrightarrow r """
    return get_env().formula_manager.Iff(left, right)


def GE(left: FNode, right: FNode) -> FNode:
    r""".. math:: l \ge r"""
    return get_env().formula_manager.GE(left, right)


def Minus(left: FNode, right: FNode) -> FNode:
    r""".. math:: l - r """
    return get_env().formula_manager.Minus(left, right)


def Times(*args: Union[FNode, Iterable[FNode]]) -> FNode:
    r""".. math:: x_1 \times x_2 \cdots \times x_n"""
    return get_env().formula_manager.Times(*args)


def Pow(left: FNode, right: FNode) -> FNode:
    r""".. math:: l ^ r"""
    return get_env().formula_manager.Pow(left, right)


def Div(left: FNode, right: FNode) -> FNode:
    r""".. math:: \frac{l}{r}"""
    return get_env().formula_manager.Div(left, right)


def Equals(left: FNode, right: FNode) -> FNode:
    r""".. math:: l = r"""
    return get_env().formula_manager.Equals(left, right)


def NotEquals(left: FNode, right: FNode):
    r""".. math:: l != r"""
    return get_env().formula_manager.NotEquals(left, right)

def GT(left: FNode, right: FNode) -> FNode:
    r""".. math:: l > r"""
    return get_env().formula_manager.GT(left, right)


def LE(left: FNode, right: FNode) -> FNode:
    r""".. math:: l \le r"""
    return get_env().formula_manager.LE(left, right)


def LT(left: FNode, right: FNode) -> FNode:
    r""".. math:: l < r"""
    return get_env().formula_manager.LT(left, right)


def Ite(iff: FNode, left: FNode, right: FNode) -> FNode:
    r""".. math:: \text{ If } i \text{ Then } l \text{ Else } r"""
    return get_env().formula_manager.Ite(iff, left, right)


def Abs(formula: FNode) -> FNode:
    r"""Returns the absolute value of the formula.

    This is implemented as If(formula > 0, formula, -formula).
    Works for both integer and real values.

    :param formula: The formula to compute the absolute value of
    :returns: The absolute value of the formula
    :raises: ValueError if the formula type is not integer or real
    """
    # Get the type of the formula to determine the appropriate zero value
    formula_type = get_type(formula)

    # Create a zero value of the same type as the formula
    if formula_type == types.INT:
        zero = Int(0)
    elif formula_type == types.REAL:
        zero = Real(0)
    else:
        # Raise an error for unsupported types
        raise ValueError(f"Abs function only supports integer and real types, got {formula_type}")

    return Ite(GT(formula, zero), formula, Minus(zero, formula))


def Symbol(name: str, typename: PySMTType=types.BOOL) -> FNode:
    """Returns a symbol with the given name and type.

    :param name: Specify the name
    :param typename: Specify the typename
    :returns: A symbol with the given name and type
    """
    return get_env().formula_manager.Symbol(name, typename)


def FreshSymbol(typename: PySMTType=types.BOOL, template: Optional[str]=None):
    """Returns a symbol with a fresh name and given type.

    :param typename: Specify the typename
    :param template: Specify the template
    :returns: A symbol with a fresh name and a given type
    """
    return get_env().formula_manager.FreshSymbol(typename, template)


def Int(value: int) -> FNode:
    """Returns an Integer constant with the given value.

    :param value: Specify the value
    :returns: An Integer constant with the given value
    """
    return get_env().formula_manager.Int(value)


def Bool(value: bool) -> FNode:
    """Returns a Boolean constant with the given value.

    :param value: Specify the value
    :returns: A Boolean constant with the given value
    """
    return get_env().formula_manager.Bool(value)


def Real(value: Union[Tuple[int, int], Fraction, int, float]) -> FNode:
    """Returns a Real constant with the given value.

    :param value: Specify the value
    :returns: A Real constant with the given value
    """
    return get_env().formula_manager.Real(value)


def String(value: str) -> FNode:
    """Returns a String constant with the given value."""
    return get_env().formula_manager.String(value)


def TRUE() -> FNode:
    """Returns the Boolean constant TRUE.

    returns: The Boolean constant TRUE
    """
    return get_env().formula_manager.TRUE()


def FALSE() -> FNode:
    """Returns the Boolean constant FALSE.

    returns: The Boolean constant FALSE
    """
    return get_env().formula_manager.FALSE()


def And(*args: Union[FNode, Iterable[FNode]]) -> FNode:
    r""".. math:: \varphi_0 \land \cdots \land \varphi_n """
    return get_env().formula_manager.And(*args)


def Or(*args: Union[FNode, Iterable[FNode]]) -> FNode:
    r""".. math:: \varphi_0 \lor \cdots \lor \varphi_n """
    return get_env().formula_manager.Or(*args)


def Plus(*args: Union[FNode, Iterable[FNode]]) -> FNode:
    r""".. math:: \varphi_0 + \cdots + \varphi_n """
    return get_env().formula_manager.Plus(*args)


def ToReal(formula: FNode) -> FNode:
    """Explicit cast of a term into a Real term."""
    return get_env().formula_manager.ToReal(formula)


def AtMostOne(*args: Union[FNode, Iterable[FNode]]) -> FNode:
    """At most one can be true at anytime.

    Cardinality constraint over a set of boolean expressions.
    """
    return get_env().formula_manager.AtMostOne(*args)


def ExactlyOne(*args: Union[FNode, Iterable[FNode]]) -> FNode:
    """Given a set of boolean expressions requires that exactly one holds."""
    return get_env().formula_manager.ExactlyOne(*args)


def AllDifferent(*args: Union[FNode, Iterable[FNode]]) -> FNode:
    """Given a set of non-boolean expressions, requires that each of them
    has value different from all the others
    """
    return get_env().formula_manager.AllDifferent(*args)


def Xor(left: FNode, right: FNode) -> FNode:
    """Returns the XOR of left and right

    :param left: Specify the left BV
    :type  left: FNode
    :param right: Specify the right BV
    :type  right: FNode
    :returns: The XOR of left and right
    """
    return get_env().formula_manager.Xor(left, right)


def Min(*args: Union[FNode, Sequence[FNode]]) -> FNode:
    """Minimum over a set of real or integer terms."""
    return get_env().formula_manager.Min(*args)


def Max(*args: Union[FNode, Sequence[FNode]]) -> FNode:
    """Maximum over a set of real or integer terms"""
    return get_env().formula_manager.Max(*args)


def EqualsOrIff(left: FNode, right: FNode) -> FNode:
    """Returns Equals() or Iff() depending on the type of the arguments.

    This can be used to deal with ambiguous cases where we might be
    dealing with both Theory and Boolean atoms.
    """
    return get_env().formula_manager.EqualsOrIff(left, right)


#
# Bit Vectors
#
def BV(value: Union[str, int], width: Optional[int]=None) -> FNode:
    """Returns a constant of type BitVector.

    value can be either:
    - a string of 0s and 1s
    - a string starting with "#b" followed by a sequence of 0s and 1s
    - an integer number s.t. 0 <= value < 2**width

    In order to create the BV representation of a signed integer,
    the SBV() method shall be used.

    :param value: Specify the value
    :param width: Specify the width
    :returns: A constant of type BitVector
    :rtype: FNode
    """
    return get_env().formula_manager.BV(value, width)


def SBV(value: Union[str, int], width: Optional[int]=None) -> FNode:
    """Returns a constant of type BitVector interpreting the sign.

    If the specified value is an integer, it is converted in the
    2-complement representation of the given number, otherwise the
    behavior is the same as BV().

    :param value: Specify the value
    :param width: Specify the width of the BV
    :returns: A constant of type BitVector interpreting the sign.
    :rtype: FNode
    """
    return get_env().formula_manager.SBV(value, width)


def BVOne(width: int) -> FNode:
    """Returns the unsigned one constant BitVector.

    :param width: Specify the width of the BitVector
    :returns: The unsigned one constant BitVector
    :rtype: FNode
    """
    return get_env().formula_manager.BVOne(width)


def BVZero(width: int) -> FNode:
    """Returns the zero constant BitVector.

    :param width: Specify the width of the BitVector
    :returns: The unsigned zero constant BitVector
    :rtype: FNode
    """
    return get_env().formula_manager.BVZero(width)


def BVNot(formula: FNode) -> FNode:
    """Returns the bitwise negation of the bitvector

    :param formula: The target formula
    :returns: The bitvector Not(bv)
    :rtype: FNode
    """
    return get_env().formula_manager.BVNot(formula)


def BVAnd(*args: Union[FNode, Sequence[FNode]]) -> FNode:
    """Returns the Bit-wise AND of bitvectors of the same size.
    If more than 2 arguments are passed, a left-associative formula is generated.

    :param *args: Specify the bitvectors
    :returns: The bit-wise AND of the bitvectors using left association
    :rtype: FNode
    """
    return get_env().formula_manager.BVAnd(*args)


def BVOr(*args: Union[FNode, Sequence[FNode]]) -> FNode:
    """Returns the Bit-wise OR of bitvectors of the same size.
    If more than 2 arguments are passed, a left-associative formula is generated.

    :param *args: Specify the bitvectors
    :returns: The bit-wise OR of the bitvectors using left association
    :rtype: FNode
    """
    return get_env().formula_manager.BVOr(*args)


def BVXor(left: FNode, right: FNode) -> FNode:
    """Returns the Bit-wise XOR of two bitvectors of the same size.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The bit-wise XOR of left and right
    :rtype: FNode
    """
    return get_env().formula_manager.BVXor(left, right)


def BVConcat(*args: Union[FNode, Sequence[FNode]]) -> FNode:
    """Returns the Concatenation of the two BVs

    :param args: Specify the bitvectors to concatenate
    :returns: The concatenation of the given BVs
    :rtype: FNode
    """
    return get_env().formula_manager.BVConcat(*args)


def BVExtract(formula: FNode, start: int=0, end: Optional[int]=None) -> FNode:
    """Returns the slice of formula from start to end (inclusive).

    :param formula: The target formula
    :param start: Specify the start index
    :param end: Specify the end index
    :returns: The slice of formula from start to end (inclusive)
    :rtype: Fnode
    """
    return get_env().formula_manager.BVExtract(formula, start=start, end=end)


def BVULT(left: FNode, right: FNode) -> FNode:
    """Returns the Unsigned Less-Than comparison of the two BVs.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Unsigned Less-Than comparison of the two BVs
    :rtype: FNode
    """
    return get_env().formula_manager.BVULT(left, right)


def BVUGT(left: FNode, right: FNode) -> FNode:
    """Returns the Unsigned Greater-Than comparison of the two BVs.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Unsigned Greater-Than comparison of the two BVs
    :rtype: FNode
    """
    return get_env().formula_manager.BVUGT(left, right)


def BVULE(left: FNode, right: FNode) -> FNode:
    """Returns the Unsigned Less-Equal comparison of the two BVs.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Unsigned Less-Equal comparison of the two BVs
    :rtype: FNode
    """
    return get_env().formula_manager.BVULE(left, right)


def BVUGE(left: FNode, right: FNode) -> FNode:
    """Returns the Unsigned Greater-Equal comparison of the two BVs.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Unsigned Greater-Equal comparison of the two BVs
    :rtype: FNode
    """
    return get_env().formula_manager.BVUGE(left, right)


def BVNeg(formula: FNode) -> FNode:
    """Returns the arithmetic negation of the BV.

    :param formula: The target formula
    :returns: The arithmetic negation of the formula
    :rtype: FNode
    """
    return get_env().formula_manager.BVNeg(formula)

def BVAdd(*args: Union[FNode, Sequence[FNode]]) -> FNode:
    """Returns the sum of BV.
    If more than 2 arguments are passed, a left-associative formula is generated.

    :param *args: Specify the bitvectors
    :returns: The sum of the bitvectors using left association.
    :rtype: FNode
    """
    return get_env().formula_manager.BVAdd(*args)


def BVSub(left: FNode, right: FNode) -> FNode:
    """Returns the difference of two BV.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The difference of the two BV
    :rtype: FNode
    """
    return get_env().formula_manager.BVSub(left, right)


def BVMul(*args: Union[FNode, Sequence[FNode]]) -> FNode:
    """Returns the product of BV.
    If more than 2 arguments are passed, a left-associative formula is generated.

    :param *args: Specify the bitvectors
    :returns: The product of the the bitvectors using left association
    :rtype: FNode
    """
    return get_env().formula_manager.BVMul(*args)


def BVUDiv(left: FNode, right: FNode) -> FNode:
    """Returns the Unsigned division of the two BV.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Unsigned division of the two BV
    :rtype: FNode
    """
    return get_env().formula_manager.BVUDiv(left, right)


def BVURem(left: FNode, right: FNode) -> FNode:
    """Returns the Unsigned remainder of the two BV.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Unsigned remainder of the two BV
    :rtype: FNode
    """
    return get_env().formula_manager.BVURem(left, right)


def BVLShl(left: FNode, right: Union[FNode, int]) -> FNode:
    """Returns the logical left shift the BV.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The logical left shift the BV
    :rtype: FNode
    """
    return get_env().formula_manager.BVLShl(left, right)


def BVLShr(left: FNode, right: Union[FNode, int]) -> FNode:
    """Returns the logical right shift the BV.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The logical right shift the BV
    :rtype: FNode
    """
    return get_env().formula_manager.BVLShr(left, right)


def BVAShr(left: FNode, right: FNode) -> FNode:
    """Returns the RIGHT arithmetic shift of the left BV by the number
        of steps specified by the right BV.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The RIGHT arithmetic shift of the left BV by the number
              of steps specified by the right BV
    :rtype: FNode
    """
    return get_env().formula_manager.BVAShr(left, right)


def BVRol(formula: FNode, steps: int) -> FNode:
    """Returns the LEFT rotation of the BV by the number of steps.

    :param formula: The target formula
    :param steps: Specify the number of steps.
    :returns: The LEFT rotation of the BV by the number of steps
    :rtype: FNode
    """
    return get_env().formula_manager.BVRol(formula, steps)


def BVRor(formula: FNode, steps: int) -> FNode:
    """Returns the RIGHT rotation of the BV by the number of steps.

    :param formula: The target formula
    :param steps: Specify the number of steps.
    :returns: The RIGHT rotation of the BV by the number of steps
    :rtype: FNode
    """
    return get_env().formula_manager.BVRor(formula, steps)


def BVZExt(formula: FNode, increase: int) -> FNode:
    """Returns the zero-extension of the BV.

    New bits are set to zero.

    :param formula: The target formula
    :param increase: Specify the increase
    :returns: The extension of the BV
    :rtype: FNode
    """
    return get_env().formula_manager.BVZExt(formula, increase)


def BVSExt(formula: FNode, increase: int) -> FNode:
    """Returns the signed-extension of the BV.

    New bits are set according to the most-significant-bit.

    :param formula: The target formula
    :param increase: Specify the 'increase' value
    :returns: The signed-extension of the BV.
    :rtype: FNode
    """
    return get_env().formula_manager.BVSExt(formula, increase)


def BVSLT(left: FNode, right: FNode) -> FNode:
    """Returns the Signed Less-Than comparison of the two BVs.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Signed Less-Than comparison of the two BVs
    :rtype: FNode
    """
    return get_env().formula_manager.BVSLT(left, right)


def BVSLE(left: FNode, right: FNode) -> FNode:
    """Returns the Signed Less-Equal comparison of the two BVs.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Signed Less-Than-Equal comparison of the two BVs
    :rtype: FNode
    """
    return get_env().formula_manager.BVSLE(left, right)


def BVSGT(left: FNode, right: FNode) -> FNode:
    """Returns the Signed Greater-Than comparison of the two BVs.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Signed Greater-Than comparison of the two BVs
    :rtype: FNode
    """
    return get_env().formula_manager.BVSGT(left, right)


def BVSGE(left: FNode, right: FNode) -> FNode:
    """Returns the Signed Greater-Equal comparison of the two BVs.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Signed Greater-Equal comparison of the two BVs.
    :rtype: FNode
    """
    return get_env().formula_manager.BVSGE(left, right)


def BVSDiv(left: FNode, right: FNode) -> FNode:
    """Returns the Signed division of the two BVs.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The the Signed division of left by right
    :rtype: FNode
    """
    return get_env().formula_manager.BVSDiv(left, right)


def BVSRem(left: FNode, right: FNode) -> FNode:
    """Returns the Signed remainder of the two BVs

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: The Signed remainder of left divided by right
    :rtype: FNode
    """
    return get_env().formula_manager.BVSRem(left, right)


def BVComp(left: FNode, right: FNode) -> FNode:
    """Returns a BV of size 1 equal to 0 if left is equal to right,
        otherwise equal to 1.

    :param left: Specify the left bitvector
    :param right: Specify the right bitvector
    :returns: A BV of size 1 equal to 0 if left is equal to right,
              otherwise 1
    :rtype: FNode
    """
    return get_env().formula_manager.BVComp(left, right)

def BVToNatural(formula: FNode) -> FNode:
    """Returns the Natural number represented by the BitVector.

    :param formula: Bitvector to be converted
    :returns: An integer between 0 and 2^m-1
    :rtype: FNode
    """
    return get_env().formula_manager.BVToNatural(formula)

# Strings
def StrLength(string: FNode) -> FNode:
    """Returns the length of a formula resulting a String"""
    return get_env().formula_manager.StrLength(string)

def StrCharAt(string: FNode, index: FNode) -> FNode:
    """Returns a single character String at position i.

    s is a string term and i is an integer term. i is the position.
    """
    return get_env().formula_manager.StrCharAt(string, index)

def StrConcat(*args) -> FNode:
    """Returns the concatenation of n Strings.

    s1, s2, ..., and sn are String terms.
    String concatenation takes at least 2 arguments.
    """
    return get_env().formula_manager.StrConcat(*args)

def StrContains(string: FNode, target: FNode) -> FNode:
    """Returns wether string contains the target.

    s and t are String terms.
    """
    return get_env().formula_manager.StrContains(string, target)

def StrIndexOf(string: FNode, target: FNode, offset: FNode) -> FNode:
    """Returns the position of the first occurrence of target in string after the offset.

    s and t being a non empty strings and i a non-negative integer.
    It returns -1 if the value to search for never occurs.
    """
    return get_env().formula_manager.StrIndexOf(string, target, offset)

def StrReplace(s: FNode, t1: FNode, t2: FNode) -> FNode:
    """Returns a new string where the first occurrence of t1 is replace by t2.

    where s, t1 and t2 are string terms, t1 is non-empty.
    """
    return get_env().formula_manager.StrReplace(s, t1, t2)

def StrSubstr(s: FNode, i: FNode, j: FNode) -> FNode:
    """Returns a substring of s starting at i and ending at j+i.

    where s is a string term and i, j are integer terms.
    """
    return get_env().formula_manager.StrSubstr(s, i, j)

def StrPrefixOf(s: FNode, t: FNode) -> FNode:
    """Returns whether the s is a prefix of the string t.

    where s and t are string terms.
    """
    return get_env().formula_manager.StrPrefixOf(s, t)

def StrSuffixOf(s: FNode, t: FNode) -> FNode:
    """Returns whether the string s is a suffix of the string t.

    where s and t are string terms.
    """
    return get_env().formula_manager.StrSuffixOf(s, t)

def StrToInt(x: FNode) -> FNode:
    """Returns the corresponding natural number of s is valid;

    If s is not valid, it returns -1.
    """
    return get_env().formula_manager.StrToInt(x)

def IntToStr(x: FNode) -> FNode:
    """Returns the corresponding String representing the natural number x.

    where x is an integer term. If x is not a natural number it
    returns the empty String.
    """
    return get_env().formula_manager.IntToStr(x)

#
# Arrays
#
def Select(array: FNode, index: FNode) -> FNode:
    """Returns a SELECT application on the array at the given index

    :param array: Specify the array
    :param index: Specify the index
    :returns: A SELECT application on array at index
    :rtype: FNode
    """
    return get_env().formula_manager.Select(array, index)


def Store(array: FNode, index: FNode, value: FNode) -> FNode:
    """Returns a STORE application with given value on array at the given index

    :param array: Specify the array
    :param index: Specify the index
    :returns: A STORE on the array at the given index with the given value
    :rtype: FNode
    """
    return get_env().formula_manager.Store(array, index, value)


def Array(idx_type: PySMTType, default: FNode, assigned_values: Optional[Dict[FNode, FNode]]=None) -> FNode:
    """Returns an Array with the given index type and initialization.

    If assigned_values is specified, then it must be a map from
    constants of type idx_type to values of the same type as default
    and the array is initialized correspondingly.

    :param idx_type: Specify the index type
    :param default: Specify the default values
    :param assigned_values: Specify the assigned values
    :returns: A node representing an array having index type equal to
              idx_type, initialized with default values. If assigned_values
              is specified, then it must be a map from constants of type
              idx_type to values of the same type as default and the array
              is initialized correspondingly.
    :rtype: FNode
    """
    return get_env().formula_manager.Array(idx_type, default, assigned_values)


##
## Shortcuts for Solvers Factory
##
def Solver(name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None, **kwargs) -> "pysmt.solvers.solver.Solver":
    """Returns a solver.

    :param name: Specify the name of the solver
    :param logic: Specify the logic that is going to be used.
    :rtype: Solver
    """
    return get_env().factory.Solver(name=name,
                                    logic=logic,
                                    **kwargs)

def UnsatCoreSolver(name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None, unsat_cores_mode: str="all", **kwargs) -> "pysmt.solvers.solver.UnsatCoreSolver":
    """Returns a solver supporting unsat core extraction.

    :param name: Specify the name of the solver
    :param logic: Specify the logic that is going to be used.
    :param unsat_cores_mode: Specify the unsat cores mode.
    :returns: A solver supporting unsat core extraction.
    :rtype: Solver
    """
    return get_env().factory.UnsatCoreSolver(name=name,
                                             logic=logic,
                                             unsat_cores_mode=unsat_cores_mode,
                                             **kwargs)


def QuantifierEliminator(name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None) -> "pysmt.solvers.qelim.QuantifierEliminator":
    """Returns a quantifier eliminator.

    :param name: Specify the name of the solver
    :param logic: Specify the logic that is going to be used.
    :returns: A quantifier eliminator with the specified
              name and logic
    :rtype: QuantifierEliminator
    """
    return get_env().factory.QuantifierEliminator(name=name, logic=logic)


def Interpolator(name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None) -> "pysmt.solvers.interpolation.Interpolator" :
    """Returns an interpolator

    :param name: Specify the name of the solver
    :param logic: Specify the logic that is going to be used.
    :returns: An interpolator
    :rtype: Interpolator
    """
    return get_env().factory.Interpolator(name=name, logic=logic)


def Portfolio(solvers_set: Iterable[Union[str, Tuple[str, Dict[str, Any]]]], logic: Union[str, Logic], **options) -> "pysmt.solvers.portfolio.Portfolio":
    """Creates a portfolio using the specified solvers.

    Solver_set is an iterable. Elements of solver_set can be
      1) a name of a solver
      2) a tuple containing a name of a solver and dict of options

    E.g.,
      Portfolio(["msat", "z3"], incremental=True)
    or
      Portfolio([("msat", {"random_seed": 1}), ("msat", {"random_seed": 2})],
               incremental=True)

    Options specified in the Portfolio are shared among all
    solvers, e.g., in the first example all solvers will receive
    the option 'incremental=True'.

    One process will be used for each of the solvers.

    :param solvers_set: Specify set of solvers to be used in the portfolio.
    :param logic: Specify the logic that is going to be used, this
        might restrict the set of solvers in the portfolio.
    :returns: A portfolio solver
    :rtype: Portfolio
    """
    import pysmt.solvers.portfolio as pf
    return pf.Portfolio(solvers_set=solvers_set,
                        logic=logic,
                        environment=get_env(),
                        **options)

def Optimizer(name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None, **options) -> "pysmt.optimization.optimizer.Optimizer":
    """Returns an Optimizer

    :param name: Specify the name of the solver
    :param logic: Specify the logic that is going to be used.
    :returns: An Optimizer
    :rtype: Optimizer
    """
    return get_env().factory.Optimizer(name=name, logic=logic, **options)


def is_sat(formula: FNode, solver_name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None, portfolio: Optional[Iterable[str]]=None) -> bool:
    """ Returns whether a formula is satisfiable.

    :param formula: The formula to check satisfiability
    :type  formula: FNode
    :param solver_name: Specify the name of the solver to be used
    :type  solver_name: string
    :param logic: Specify the logic that is going to be used
    :param portfolio: A list of solver names to perform portfolio solving.
    :type  portfolio: An iterable of solver names
    :returns: Whether the formula is SAT or UNSAT.
    :rtype: bool
    """
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_sat")
        formula = env.formula_manager.normalize(formula)

    return env.factory.is_sat(formula,
                              solver_name=solver_name,
                              logic=logic,
                              portfolio=portfolio)

# TODO also here mypy didn't notice that the model was not Optional (a mistake)
def get_model(formula: FNode, solver_name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None) -> Optional["pysmt.solvers.solver.Model"]:
    """ Similar to :py:func:`is_sat` but returns a model if the formula is
    satisfiable, otherwise None

    :param formula: The target formula
    :param solver_name: Specify the name of the solver
    :param: logic: Specify the logic that is going to be used
    :returns: A model if the formula is satisfiable
    :rtype: Model
    """
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during get_model")
        formula = env.formula_manager.normalize(formula)

    return env.factory.get_model(formula,
                                 solver_name=solver_name,
                                 logic=logic)


def get_implicant(formula: FNode, solver_name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None) -> Optional[FNode]:
    """Returns a formula f_i such that Implies(f_i, formula) is valid or None
    if formula is unsatisfiable.

    if complete is set to true, all the variables appearing in the
    formula are forced to appear in f_i.
    :param formula: The target formula
    :param solver_name: Specify the name of the solver
    :param: logic: Specify the logic that is going to be used
    :returns: A formula f_i such that Implies(f_i, formula) is valid or None
              if formula is unsatisfiable.
    :rtype: FNode
    """
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during get_model")
        formula = env.formula_manager.normalize(formula)

    return env.factory.get_implicant(formula,
                                     solver_name=solver_name,
                                     logic=logic)


def get_unsat_core(clauses: Iterable[FNode], solver_name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None)  -> Optional[Set[FNode]]:
    """Similar to :py:func:`get_model` but returns the unsat core of the
    conjunction of the input clauses

    :param clauses: Specify the list of input clauses
    :param solver_name: Specify the name of the solver_name
    :param logic: Specify the logic that is going to be used
    :returns: The unsat core of the conjunction of the input clauses
    """
    env = get_env()
    clauses = list(clauses)
    if any(c not in env.formula_manager for c in clauses):
        warnings.warn("Warning: Contextualizing formula during get_model")
        clauses = [env.formula_manager.normalize(c) for c in clauses]

    return env.factory.get_unsat_core(clauses,
                                      solver_name=solver_name,
                                      logic=logic)


def is_valid(formula: FNode, solver_name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None, portfolio: Optional[Union[Iterable[str], Iterable[Tuple[str, Dict[str, Any]]]]]=None) -> bool:
    """Similar to :py:func:`is_sat` but checks validity.

    :param formula: The target formula
    :type  formula: FNode
    :param solver_name: Specify the name of the solver to be used
    :param logic: Specify the logic that is going to be used
    :param portfolio: A list of solver names to perform portfolio solving.
    :returns: Whether the formula is SAT or UNSAT but checks validity
    :rtype: bool
    """
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_valid")
        formula = env.formula_manager.normalize(formula)

    return env.factory.is_valid(formula,
                                solver_name=solver_name,
                                logic=logic,
                                portfolio=portfolio)


def is_unsat(formula: FNode, solver_name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None, portfolio: Optional[Union[Iterable[str], Iterable[Tuple[str, Dict[str, Any]]]]]=None) -> bool:
    """Similar to :py:func:`is_sat` but checks unsatisfiability.

    :param formula: The target formula
    :type  formula: FNode
    :param solver_name: Specify the name of the solver to be used
    :param logic: Specify the logic that is going to be used
    :param portfolio: A list of solver names to perform portfolio solving.
    :returns: Whether the formula is UNSAT or not
    :rtype: bool
    """
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_unsat")
        formula = env.formula_manager.normalize(formula)

    return env.factory.is_unsat(formula,
                                solver_name=solver_name,
                                logic=logic,
                                portfolio=portfolio)


def qelim(formula: FNode, solver_name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None) -> FNode:
    """Performs quantifier elimination of the given formula.

    :param formula: The target formula
    :param solver_name: Specify the name of the solver to be used
    :param logic: Specify the logic that is going to be used
    :returns: A formula after performing quantifier elimination
    :rtype: FNode
    """
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_unsat")
        formula = env.formula_manager.normalize(formula)

    return env.factory.qelim(formula,
                             solver_name=solver_name,
                             logic=logic)

def binary_interpolant(formula_a: FNode, formula_b: FNode, solver_name: Optional[str]=None, logic: Optional[Union[str, Logic]]=None) -> Optional[FNode]:
    """Computes an interpolant of (formula_a, formula_b).

    Returns None if the conjunction is satisfiable

    :param formula_a: Specify formula_a
    :param formula_b: Specify formula_b
    :param solver_name: Specify the name of the solver to be used
    :param logic: Specify the logic that is going to be used
    :returns: An interpolant of (formula_a, formula_b); None
              if the conjunction is satisfiable
    :rtype: FNode or None
    """
    env = get_env()
    formulas = [formula_a, formula_b]
    for i, f in enumerate(formulas):
        if f not in env.formula_manager:
            warnings.warn("Warning: Contextualizing formula during "
                          "binary_interpolant")
            formulas[i] = env.formula_manager.normalize(f)

    return env.factory.binary_interpolant(formulas[0], formulas[1],
                                          solver_name=solver_name,
                                          logic=logic)


def sequence_interpolant(formulas: Sequence[FNode], solver_name: Optional[str]=None, logic:Optional[Union[str, Logic]]=None) -> Optional[FNode]:
    """Computes a sequence interpolant of the formulas.

    Returns None if the conjunction is satisfiable.

    :param formulas: The target formulas
    :param solver_name: Specify the name of the solver to be used
    :param logic: Specify the logic that is going to be used
    :returns: A sequence intepolant of the formulas; None
              if the conjunction is satisfiable
    :rtype: FNode or None
    """
    env = get_env()
    formulas = list(formulas)
    for i, f in enumerate(formulas):
        if f not in env.formula_manager:
            warnings.warn("Warning: Contextualizing formula during "
                          "sequence_interpolant")
            formulas[i] = env.formula_manager.normalize(f)

    return env.factory.sequence_interpolant(formulas,
                                            solver_name=solver_name,
                                            logic=logic)


def read_configuration(config_filename: Union[str, os.PathLike], environment: Optional["pysmt.environment.Environment"]=None):
    """Reads the pysmt configuration of the given file path and applies
    it on the specified environment. If no environment is specified,
    the top-level environment will be used.

    :param config_filename: Specify the name of the config file
    :param environment: Specify the environment
    """
    if environment is None:
        environment = get_env()
    config.configure_environment(config_filename, environment)


def write_configuration(config_filename: Union[str, os.PathLike], environment: Optional["pysmt.environment.Environment"]=None):
    """Dumps the current pysmt configuration to the specified file path

    :param config_filename: Specify the name of the config file
    :param environment: Specify the environment
    """
    if environment is None:
        environment = get_env()
    config.write_environment_configuration(config_filename, environment)


def read_smtlib(fname: str) -> FNode:
    """Reads the SMT formula from the given file.

    This supports compressed files, if the fname ends in .bz2 .

    :param fname: Specify the filename
    :returns: An SMT formula
    :rtype: FNode
    """
    return pysmt.smtlib.parser.get_formula_fname(fname)


def write_smtlib(formula: FNode, fname: Union[str, os.PathLike]):
    """Writes the given formula in Smt-Lib format to the given file.

    :param formula: Specify the SMT formula to be written
    :param fname: Specify the filename
    """
    with open(fname, "w") as fout:
        script = pysmt.smtlib.script.smtlibscript_from_formula(formula)
        script.serialize(fout)


def to_smtlib(formula: FNode, daggify: bool=True) -> str:
    """Returns a Smt-Lib string representation of the formula.

    The daggify parameter can be used to switch from a linear-size
    representation that uses 'let' operators to represent the
    formula as a dag or a simpler (but possibly exponential)
    representation that expands the formula as a tree.

    See :py:class:`SmtPrinter`
    """
    return pysmt.smtlib.printers.to_smtlib(formula, daggify=daggify)
