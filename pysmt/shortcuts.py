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
method get_global_env(). Keep in mind that the global state of the
environment might lead to inconsistency and unexpected bugs. This is
particularly true for tests. For tests it is recommended to perform an
environment reset in the setUp phase, to be guaranteed that a fresh
environment is used.
"""
# Enable default deprecation warnings!
import warnings
warnings.simplefilter('default')

import pysmt.typing as types
import pysmt.configuration as config
import pysmt.environment


def get_env():
    """Returns the global environment."""
    return pysmt.environment.get_env()

def reset_env():
    """Resets the global environment, and returns the new one."""
    return pysmt.environment.reset_env()

# Enable by default infix notation
get_env().enable_infix_notation = True

##### Shortcuts for FormulaManager #####
def get_type(formula):
    """Returns the type of the formula."""
    return get_env().stc.get_type(formula)

def simplify(formula):
    """Returns the simplified version of the formula."""
    return get_env().simplifier.simplify(formula)

def substitute(formula, subs):
    """Applies the substitutions defined in the dictionary to the formula."""
    return get_env().substituter.substitute(formula, subs)

def serialize(formula, threshold=None):
    """Provides a string representing the formula."""
    return get_env().serializer.serialize(formula,
                                          threshold=threshold)

def get_free_variables(formula):
    """Returns the simplified version of the formula."""
    return get_env().fvo.get_free_variables(formula)

def get_atoms(formula):
    """Returns the set of atoms of the formula."""
    return get_env().ao.get_atoms(formula)

def get_formula_size(formula, measure=None):
    """Returns the size of the formula as measured by the given counting type.
    See pysmt.oracles.SizeOracle for details.
    """
    return get_env().sizeo.get_size(formula, measure)


##### Nodes Creation #####

def ForAll(variables, formula):
    r""".. math:: \forall v_1, \cdots, v_n . \varphi(v_1, \cdots, v_n)"""
    return get_env().formula_manager.ForAll(variables, formula)

def Exists(variables, formula):
    r""".. math:: \exists v_1, \cdots, v_n . \varphi(v_1, \cdots, v_n)"""
    return get_env().formula_manager.Exists(variables, formula)

def Function(vname, params):
    r""".. math:: vname(p_1, \cdots, p_n)"""
    return get_env().formula_manager.Function(vname, params)

def Not(formula):
    r""".. math:: \lnot \varphi"""
    return get_env().formula_manager.Not(formula)

def Implies(left, right):
    r""".. math:: l \rightarrow r"""
    return get_env().formula_manager.Implies(left, right)

def Iff(left, right):
    r""".. math:: l \leftrightarrow r """
    return get_env().formula_manager.Iff(left, right)

def GE(left, right):
    r""".. math:: l \ge r"""
    return get_env().formula_manager.GE(left, right)

def Minus(left, right):
    r""".. math:: l - r """
    return get_env().formula_manager.Minus(left, right)

def Times(left, right):
    r""".. math:: l * r"""
    return get_env().formula_manager.Times(left, right)

def Div(left, right):
    r""".. math:: \frac{l}{r}"""
    return get_env().formula_manager.Div(left, right)

def Equals(left, right):
    r""".. math:: l = r"""
    return get_env().formula_manager.Equals(left, right)

def GT(left, right):
    r""".. math:: l > r"""
    return get_env().formula_manager.GT(left, right)

def LE(left, right):
    r""".. math:: l \le r"""
    return get_env().formula_manager.LE(left, right)

def LT(left, right):
    r""".. math:: l < r"""
    return get_env().formula_manager.LT(left, right)

def Ite(iff, left, right):
    r""".. math:: \text{ If } i \text{ Then } l \text{ Else } r"""
    return get_env().formula_manager.Ite(iff, left, right)

def Symbol(name, typename=types.BOOL):
    """Returns a symbol with the given name and type."""
    return get_env().formula_manager.Symbol(name, typename)

def FreshSymbol(typename=types.BOOL, template=None):
    """Returns a symbol with a fresh name and given type."""
    return get_env().formula_manager.FreshSymbol(typename, template)

def Int(value):
    """Returns an Integer constant with the given value."""
    return get_env().formula_manager.Int(value)

def Bool(value):
    """Returns a Boolean constant with the given value."""
    return get_env().formula_manager.Bool(value)

def Real(value):
    """Returns a Real constant with the given value."""
    return get_env().formula_manager.Real(value)

def TRUE():
    """Returns the Boolean constant TRUE."""
    return get_env().formula_manager.TRUE()

def FALSE():
    """Returns the Boolean constant FALSE."""
    return get_env().formula_manager.FALSE()

def And(*args):
    r""".. math:: \varphi_0 \land \cdots \land \varphi_n """
    return get_env().formula_manager.And(*args)

def Or(*args):
    r""".. math:: \varphi_0 \lor \cdots \lor \varphi_n """
    return get_env().formula_manager.Or(*args)

def Plus(*args):
    r""".. math:: \varphi_0 + \cdots + \varphi_n """
    return get_env().formula_manager.Plus(*args)

def ToReal(formula):
    """Explicit cast of a term into a Real term."""
    return get_env().formula_manager.ToReal(formula)

def AtMostOne(*args):
    """At most one can be true at anytime.

    Cardinality constraint over a set of boolean expressions.
    """
    return get_env().formula_manager.AtMostOne(*args)

def ExactlyOne(*args):
    """Given a set of boolean expressions requires that exactly one holds."""
    return get_env().formula_manager.ExactlyOne(*args)

def AllDifferent(*args):
    """Given a set of non-boolean expressions, requires that each of them
    has value different from all the others
    """
    return get_env().formula_manager.AllDifferent(*args)

def Xor(left, right):
    """Returns the XOR of left and right"""
    return get_env().formula_manager.Xor(left, right)

def Min(*args):
    """Minimum over a set of real or integer terms."""
    return get_env().formula_manager.Min(*args)

def Max(*args):
    """Maximum over a set of real or integer terms"""
    return get_env().formula_manager.Max(*args)

def EqualsOrIff(left, right):
    """Returns Equals() or Iff() depending on the type of the arguments.

    This can be used to deal with ambiguous cases where we might be
    dealing with both Theory and Boolean atoms.
    """
    return get_env().formula_manager.EqualsOrIff(left, right)

# Bit Vectors
def BV(value, width=None):

    """Returns a constant of type BitVector.

    value can be either:
    - a string of 0s and 1s
    - a string starting with "#b" followed by a sequence of 0s and 1s
    - an integer number s.t. 0 <= value < 2**width

    In order to create the BV representation of a signed integer,
    the SBV() method shall be used.
    """
    return get_env().formula_manager.BV(value, width)

def SBV(value, width=None):
    """Returns a constant of type BitVector interpreting the sign.

    If the specified value is an integer, it is converted in the
    2-complement representation of the given number, otherwise the
    behavior is the same as BV().
    """
    return get_env().formula_manager.SBV(value, width)

def BVOne(width=None):
    """Returns the unsigned one constant BitVector."""
    return get_env().formula_manager.BVOne(width)

def BVZero(width=None):
    """Returns the zero constant BitVector."""
    return get_env().formula_manager.BVZero(width)

def BVNot(formula):
    """Returns the bitvector Not(bv)"""
    return get_env().formula_manager.BVNot(formula)

def BVAnd(left, right):
    """Returns the Bit-wise AND of two bitvectors of the same size."""
    return get_env().formula_manager.BVAnd(left, right)

def BVOr(left, right):
    """Returns the Bit-wise OR of two bitvectors of the same size."""
    return get_env().formula_manager.BVOr(left, right)

def BVXor(left, right):
    """Returns the Bit-wise XOR of two bitvectors of the same size."""
    return get_env().formula_manager.BVXor(left, right)

def BVConcat(left, right):
    """Returns the Concatenation of the two BVs"""
    return get_env().formula_manager.BVConcat(left, right)

def BVExtract(formula, start=0, end=None):
    """Returns the slice of formula from start to end (inclusive)."""
    return get_env().formula_manager.BVExtract(formula, start=start, end=end)

def BVULT(left, right):
    """Returns the formula left < right."""
    return get_env().formula_manager.BVULT(left, right)

def BVUGT(left, right):
    """Returns the formula left > right."""
    return get_env().formula_manager.BVUGT(left, right)

def BVULE(left, right):
    """Returns the formula left <= right."""
    return get_env().formula_manager.BVULE(left, right)

def BVUGE(left, right):
    """Returns the formula left >= right."""
    return get_env().formula_manager.BVUGE(left, right)

def BVNeg(formula):
    """Returns the arithmetic negation of the BV."""
    return get_env().formula_manager.BVNeg(formula)

def BVAdd(left, right):
    """Returns the sum of two BV."""
    return get_env().formula_manager.BVAdd(left, right)

def BVSub(left, right):
    """Returns the difference of two BV."""
    return get_env().formula_manager.BVSub(left, right)

def BVMul(left, right):
    """Returns the product of two BV."""
    return get_env().formula_manager.BVMul(left, right)

def BVUDiv(left, right):
    """Returns the division of the two BV."""
    return get_env().formula_manager.BVUDiv(left, right)

def BVURem(left, right):
    """Returns the reminder of the two BV."""
    return get_env().formula_manager.BVURem(left, right)

def BVLShl(left, right):
    """Returns the logical left shift the BV."""
    return get_env().formula_manager.BVLShl(left, right)

def BVLShr(left, right):
    """Returns the logical right shift the BV."""
    return get_env().formula_manager.BVLShr(left, right)

def BVRol(formula, steps):
    """Returns the LEFT rotation of the BV by the number of steps."""
    return get_env().formula_manager.BVRol(formula, steps)

def BVRor(formula, steps):
    """Returns the RIGHT rotation of the BV by the number of steps."""
    return get_env().formula_manager.BVRor(formula, steps)

def BVZExt(formula, increase):
    """Returns the extension of the BV

    New bits are set to zero.
    """
    return get_env().formula_manager.BVZExt(formula, increase)

def BVSExt(formula, increase):
    """Returns the signed extension of the BV

    New bits are set according to the most-significant-bit.
    """
    return get_env().formula_manager.BVSExt(formula, increase)

def BVSLT(left, right):
    """Returns the SIGNED LOWER-THAN comparison for BV."""
    return get_env().formula_manager.BVSLT(left, right)

def BVSLE(left, right):
    """Returns the SIGNED LOWER-THAN-OR-EQUAL-TO comparison for BV."""
    return get_env().formula_manager.BVSLE(left, right)

def BVSGT(left, right):
    """Returns the SIGNED GREATER-THAN comparison for BV."""
    return get_env().formula_manager.BVSGT(left, right)

def BVSGE(left, right):
    """Returns the SIGNED GREATER-THAN-OR-EQUAL-TO comparison for BV."""
    return get_env().formula_manager.BVSGE(left, right)

def BVSDiv(left, right):
    """Returns the SIGNED DIVISION of left by right"""
    return get_env().formula_manager.BVSDiv(left, right)

def BVSRem(left, right):
    """Returns the SIGNED REMAINDER of left divided by right"""
    return get_env().formula_manager.BVSRem(left, right)

def BVComp(left, right):
    """Returns a BV of size 1 equal to 0 if left is equal to right,
        otherwise 1 is returned."""
    return get_env().formula_manager.BVComp(left, right)

def BVAShr(left, right):
    """Returns the RIGHT arithmetic rotation of the left BV by the number
        of steps specified by the right BV."""
    return get_env().formula_manager.BVAShr(left, right)

# arrays
def Select(arr, idx):
    """ Returns a SELECT application on array 'arr' at index 'idx' """
    return get_env().formula_manager.Select(arr, idx)

def Store(arr, idx, elem):
    """ Returns a STORE application on array 'arr' at index 'idx' with value 'elem' """
    return get_env().formula_manager.Store(arr, idx, elem)

def Array(idx_type, default, assigned_values=None):
    """Creates a node representing an array having index type equal to
    idx_type, initialized with default values.

    If assigned_values is specified, then it must be a map from
    constants of type idx_type to values of the same type as default
    and the array is initialized correspondingly.
    """
    return get_env().formula_manager.Array(idx_type, default, assigned_values)

#### Shortcuts for Solvers Factory #####
def Solver(quantified=False, name=None, logic=None, **kwargs):
    """Returns a solver."""
    return get_env().factory.Solver(quantified=quantified,
                                    name=name,
                                    logic=logic,
                                    **kwargs)

def UnsatCoreSolver(quantified=False, name=None, logic=None,
                    unsat_cores_mode="all"):
    """Returns a solver supporting unsat core extraction."""
    return get_env().factory.UnsatCoreSolver(quantified=quantified,
                                             name=name,
                                             logic=logic,
                                             unsat_cores_mode=unsat_cores_mode)

def QuantifierEliminator(name=None, logic=None):
    """Returns a quantifier eliminator"""
    return get_env().factory.QuantifierEliminator(name=name, logic=logic)

def Interpolator(name=None, logic=None):
    """Returns an interpolator"""
    return get_env().factory.Interpolator(name=name, logic=logic)

def is_sat(formula, solver_name=None, logic=None):
    """ Returns whether a formula is satisfiable.

    :param formula: The formula to check satisfiability
    :type  formula: FNode
    :param solver_name: Specify the name of the solver to be used.
    :param logic: Specify the logic that is going to be used.
    :returns: Whether the formula is SAT or UNSAT.
    :rtype: bool
    """
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_sat")
        formula = env.formula_manager.normalize(formula)

    return env.factory.is_sat(formula,
                              solver_name=solver_name,
                              logic=logic)

def get_model(formula, solver_name=None, logic=None):
    """ Similar to :py:func:`is_sat` but returns a model if the formula is
    satisfiable, otherwise None."""
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during get_model")
        formula = env.formula_manager.normalize(formula)

    return env.factory.get_model(formula,
                                 solver_name=solver_name,
                                 logic=logic)

def get_implicant(formula, solver_name=None, logic=None):
    """Returns a formula f_i such that Implies(f_i, formula) is valid or None
    if formula is unsatisfiable.

    if complete is set to true, all the variables appearing in the
    formula are forced to appear in f_i.
    """
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during get_model")
        formula = env.formula_manager.normalize(formula)

    return env.factory.get_implicant(formula,
                                     solver_name=solver_name,
                                     logic=logic)

def get_unsat_core(clauses, solver_name=None, logic=None):
    """Similar to :py:func:`get_model` but returns the unsat core of the
    conjunction of the input clauses"""
    env = get_env()
    if any(c not in env.formula_manager for c in clauses):
        warnings.warn("Warning: Contextualizing formula during get_model")
        clauses = [env.formula_manager.normalize(c) for c in clauses]

    return env.factory.get_unsat_core(clauses,
                                      solver_name=solver_name,
                                      logic=logic)

def is_valid(formula, solver_name=None, logic=None):
    """Similar to :py:func:`is_sat` but checks validity."""
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_valid")
        formula = env.formula_manager.normalize(formula)

    return env.factory.is_valid(formula,
                                solver_name=solver_name,
                                logic=logic)

def is_unsat(formula, solver_name=None, logic=None):
    """Similar to :py:func:`is_sat` but checks unsatisfiability."""
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_unsat")
        formula = env.formula_manager.normalize(formula)

    return env.factory.is_unsat(formula,
                                solver_name=solver_name,
                                logic=logic)

def qelim(formula, solver_name=None, logic=None):
    """Performs quantifier elimination of the given formula."""
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_unsat")
        formula = env.formula_manager.normalize(formula)

    return env.factory.qelim(formula,
                             solver_name=solver_name,
                             logic=logic)

def binary_interpolant(formula_a, formula_b, solver_name=None, logic=None):
    """Computes an interpolant of (formula_a, formula_b). Returns None
    if the conjunction is satisfiable"""
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

def sequence_interpolant(formulas, solver_name=None, logic=None):
    """Computes a sequence interpolant of the formulas. Returns None
    if the conjunction is satisfiable"""
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

def read_configuration(config_filename, environment=None):
    """
    Reads the pysmt configuration of the given file path and applies
    it on the specified environment. If no environment is specified,
    the top-level environment will be used.
    """
    if environment is None:
        environment = get_env()
    config.configure_environment(config_filename, environment)

def write_configuration(config_filename, environment=None):
    """
    Dumps the current pysmt configuration to the specified file path
    """
    if environment is None:
        environment = get_env()
    config.write_environment_configuration(config_filename, environment)
