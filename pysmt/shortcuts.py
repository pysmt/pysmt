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

import pysmt.typing as types
import pysmt.environment
import pysmt.configuration as config

# Enable default deprecation warnings!
import warnings
warnings.simplefilter('default')

#### GLOBAL ENVIRONMENTS STACKS ####
ENVIRONMENTS_STACK = []

def get_env():
    """Returns the Environment at the head of the stack."""
    return ENVIRONMENTS_STACK[-1]

def push_env(env=None):
    """Push a env in the stack. If env is None, a new Environment is created."""
    if env is None:
        env = pysmt.environment.Environment()
    ENVIRONMENTS_STACK.append(env)

def pop_env():
    """Pop an env from the stack."""
    return ENVIRONMENTS_STACK.pop()

def reset_env():
    """Destroys and recreate the head environment."""
    pop_env()
    push_env()
    return get_env()

# Create the default environment
push_env()


##### Shortcuts for FormulaManager #####
def get_type(formula):
    """Returns the type of the formula."""
#    return _choose_environment(env).stc.get_type(formula)
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

def AtMostOne(bool_exprs):
    """
    Cardinality constraint over a set of boolean expressions.
    At most one can be true at anytime.
    """
    return get_env().formula_manager.AtMostOne(bool_exprs)

def ExactlyOne(bool_symbols):
    """Given a set of boolean symbols requires that exactly one holds."""
    return get_env().formula_manager.ExactlyOne(bool_symbols)

def Xor(left, right):
    """Returns the XOR of left and right"""
    return get_env().formula_manager.Xor(left, right)


#### Shortcuts for Solvers Factory #####
def Solver(quantified=False, name=None, logic=None):
    """Returns a solver."""
    return get_env().factory.Solver(quantified=quantified,
                                    name=name,
                                    logic=logic)

def QuantifierEliminator(name=None):
    """Returns a quantifier eliminator"""
    return get_env().factory.QuantifierEliminator(name=name)

def is_sat(formula, quantified=False, solver_name=None, logic=None):
    """ Returns whether a formula is satisfiable.

    :param formula: The formula to check satisfiability
    :type  formula: FNode
    :param quantified: A boolean indicating whether the formula is
                       quantified (this will influence the choice of
                       the solver.
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
                              quantified=quantified,
                              solver_name=solver_name,
                              logic=logic)

def is_valid(formula, quantified=False, solver_name=None, logic=None):
    """Similar to :py:func:`is_sat` but checks validity."""
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_valid")
        formula = env.formula_manager.normalize(formula)

    return env.factory.is_valid(formula,
                                quantified=quantified,
                                solver_name=solver_name,
                                logic=logic)

def is_unsat(formula, quantified=False, solver_name=None, logic=None):
    """Similar to :py:func:`is_sat` but checks unsatisfiability."""
    env = get_env()
    if formula not in env.formula_manager:
        warnings.warn("Warning: Contextualizing formula during is_unsat")
        formula = env.formula_manager.normalize(formula)

    return env.factory.is_unsat(formula,
                                quantified=quantified,
                                solver_name=solver_name,
                                logic=logic)

def qelim(formula, solver_name=None):
    """Performs quantifier elimination of the given formula."""
    _qelim = get_env().factory.QuantifierEliminator(name=solver_name)
    return _qelim.eliminate_quantifiers(formula)


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
