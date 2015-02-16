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
"""MathSAT-based FNodes."""

import collections
import re
from fractions import Fraction

import mathsat


import pysmt.shortcuts as shortcuts
from pysmt.operators import ALL_TYPES, QUANTIFIERS, CONSTANTS
from pysmt.operators import (FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF,
                             SYMBOL, FUNCTION,
                             REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT,
                             PLUS, MINUS, TIMES,
                             LE, LT, EQUALS,
                             ITE,
                             TOREAL)
from pysmt.typing import BOOL, REAL, INT, PYSMT_TYPES

FNodeContent = collections.namedtuple("FNodeContent",
                                      ["node_type", "args", "payload"])

# Operators for which Args is an FNode (used by compute_dependencies
DEPENDENCIES_SIMPLE_ARGS = (set(ALL_TYPES) - \
                            (set([SYMBOL, FUNCTION]) | QUANTIFIERS | CONSTANTS))


class MsatFNode(object):
    r"""FNode represent the basic structure for representing a formula.

    FNodes are built using the FormulaManager, and should not be
    explicitely instantiated, since the FormulaManager takes care of
    memoization, thus guaranteeing that equivalent are represented by
    the same object.

    An FNode is a wrapper to the structure FNodeContent. FNodeContent
    defines the type of the node (see operators.py), its arguments
    (e.g., for the formula A /\ B, args=(A,B)) and its payload,
    content of the node that is not an FNode (e.g., for an integer
    constant, the payload might be the python value 1).
    """

    def __init__(self, manager, msat_env, msat_term):
        self.manager = manager
        self._env = msat_env
        self._term = msat_term
        self._dependencies = None
        return

    # __eq__ and __hash__ are left as default
    # This is because we always have shared FNode's

    def node_type(self):
        if mathsat.msat_term_is_true(self._env, self._term):
            return BOOL_CONSTANT
        if mathsat.msat_term_is_false(self._env, self._term):
            return BOOL_CONSTANT
        if mathsat.msat_term_is_boolean_constant(self._env, self._term):
            return SYMBOL
        if mathsat.msat_term_is_number(self._env, self._term):
            return REAL_CONSTANT
        if mathsat.msat_term_is_and(self._env, self._term):
            return AND
        if mathsat.msat_term_is_or(self._env, self._term):
            return OR
        if mathsat.msat_term_is_not(self._env, self._term):
            return NOT
        if mathsat.msat_term_is_iff(self._env, self._term):
            return IFF
        if mathsat.msat_term_is_term_ite(self._env, self._term):
            return ITE
        if mathsat.msat_term_is_constant(self._env, self._term):
            return SYMBOL
        if mathsat.msat_term_is_uf(self._env, self._term):
            return FUNCTION
        if mathsat.msat_term_is_equal(self._env, self._term):
            return EQUALS
        if mathsat.msat_term_is_leq(self._env, self._term):
            return LE
        if mathsat.msat_term_is_plus(self._env, self._term):
            return PLUS
        if mathsat.msat_term_is_times(self._env, self._term):
            return TIMES
        raise NotImplementedError

    def args(self):
        arity = mathsat.msat_term_arity(self._term)
        return [self.manager.new_node(mathsat.msat_term_get_arg(self._term, i))
                for i in xrange(arity)]


    def arg(self, idx):
        return self.manager.new_node(mathsat.msat_term_get_arg(self._term, idx))


    def get_dependencies(self):
        if self._dependencies is None:
            self._dependencies = self._compute_dependencies()
        return self._dependencies

    def _compute_dependencies(self):
        if self.node_type() in DEPENDENCIES_SIMPLE_ARGS:
            res = set()
            for s in self.get_sons():
                res.update(s.get_dependencies())
            return res

        elif self.node_type() in QUANTIFIERS:
            raise NotImplementedError

        elif self.node_type() == SYMBOL:
            return frozenset([self])

        elif self.node_type() in CONSTANTS:
            return frozenset()

        elif self.node_type() == FUNCTION:
            res = set([self.function_name()])
            for p in self.args():
                res.update(p.get_dependencies())
            return res

        else:
            assert False
        return


    def get_sons(self):
        return self.args()


    def simplify(self):
        # MathSAT already simplifies internally
        return self

    def substitute(self, subs):
        return shortcuts.substitute(self, subs=subs)

    def is_constant(self, _type=None, value=None):
        if self.node_type() not in CONSTANTS:
            return False

        assert _type is None or _type in PYSMT_TYPES
        if _type is not None:
            if _type == INT and self.node_type() != INT_CONSTANT:
                return False
            if _type == REAL and self.node_type() != REAL_CONSTANT:
                return False
            if _type == BOOL and self.node_type() != BOOL_CONSTANT:
                return False

        if value is not None:
            return self.constant_value() == value
        else:
            return True

    def is_bool_constant(self, value=None):
        return self.is_constant(BOOL, value)

    def is_real_constant(self, value=None):
        return self.is_constant(REAL, value)

    def is_int_constant(self, value=None):
        return self.is_constant(INT, value)


    def is_symbol(self, type_=None):
        if type_:
            return self.node_type() == SYMBOL and \
                   self.symbol_type() == type_
        return self.node_type() == SYMBOL

    def is_literal(self):
        if self.is_symbol(BOOL):
            return True
        if self.is_not():
            return self.arg(0).is_symbol(BOOL)

    def is_true(self):
        return self.is_bool_constant(True)

    def is_false(self):
        return self.is_bool_constant(False)

    def is_one(self):
        return self.is_real_constant(1)

    def is_zero(self):
        return self.is_real_constant(0)

    def is_toreal(self):
        return self.node_type() == TOREAL

    def is_forall(self):
        return self.node_type() == FORALL

    def is_exists(self):
        return self.node_type() == EXISTS

    def is_and(self):
        return self.node_type() == AND

    def is_or(self):
        return self.node_type() == OR

    def is_not(self):
        return self.node_type() == NOT

    def is_plus(self):
        return self.node_type() == PLUS

    def is_minus(self):
        return self.node_type() == MINUS

    def is_times(self):
        return self.node_type() == TIMES

    def is_implies(self):
        return self.node_type() == IMPLIES

    def is_iff(self):
        return self.node_type() == IFF

    def is_ite(self):
        return self.node_type() == ITE

    def is_equals(self):
        return self.node_type() == EQUALS

    def is_le(self):
        return self.node_type() == LE

    def is_lt(self):
        return self.node_type() == LT

    def __str__(self):
        return self.serialize(threshold=5)

    def __repr__(self):
        return str(self)

    def serialize(self, threshold=None):
        return shortcuts.serialize(self, threshold=threshold)

    def is_quantifier(self):
        return self.is_exists() or self.is_forall()

    def is_function_application(self):
        return self.node_type() == FUNCTION

    def is_boolean_operator(self):
        return self.is_and() or \
            self.is_or() or \
            self.is_not() or \
            self.is_iff() or \
            self.is_implies()

    def is_term(self):
        """All FNodes are terms, except for function definition."""
        if self.is_symbol() and self.symbol_type().is_function_type():
            return False
        else:
            return True

    def _msat_type_to_type(self, mt):
        if mathsat.msat_is_bool_type(self._env, mt):
            return BOOL
        elif mathsat.msat_is_rational_type(self._env, mt):
            return REAL
        elif mathsat.msat_is_integer_type(self._env, mt):
            return INT
        else:
            raise NotImplementedError


    def symbol_type(self):
        msat_type = mathsat.msat_term_get_type(self._term)
        return self._msat_type_to_type(msat_type)

    def symbol_name(self):
        decl = mathsat.msat_term_get_decl(self._term)
        return mathsat.msat_decl_get_name(decl)

    def constant_value(self):
        if self.is_bool_constant():
            if mathsat.msat_term_is_true(self._env, self._term):
                return True
            return False
        else:
            # it is a number
            rep = mathsat.msat_term_repr(self._term)
            match = re.match(r"(-?\d+)/(\d+)", rep)
            assert match is not None
            return Fraction((int(match.group(1)), int(match.group(2))))


    def function_name(self):
        decl = mathsat.msat_term_get_decl(self._term)
        return mathsat.msat_decl_get_name(decl)

    def quantifier_vars(self):
        raise NotImplementedError

    # Infix Notation
    def _apply_infix(self, right, function):
        if shortcuts.get_env().enable_infix_notation:
            return function(self, right)
        else:
            raise Exception("Cannot use infix notation")

    def Implies(self, right):
        return self._apply_infix(right, shortcuts.Implies)

    def Iff(self, right):
        return self._apply_infix(right, shortcuts.Iff)

    def Equals(self, right):
        return self._apply_infix(right, shortcuts.Equals)

    def Ite(self, right):
        return self._apply_infix(right, shortcuts.Ite)

    def And(self, right):
        return self._apply_infix(right, shortcuts.And)

    def Or(self, right):
        return self._apply_infix(right, shortcuts.Or)

    def __add__(self, right):
        return self._apply_infix(right, shortcuts.Plus)

    def __sub__(self, right):
        return self._apply_infix(right, shortcuts.Minus)

    def __mul__(self, right):
        return self._apply_infix(right, shortcuts.Times)

    def __div__(self, right):
        return self._apply_infix(right, shortcuts.Div)

    def __truediv__(self, right):
        return self.__div__(right)

    def __gt__(self, right):
        return self._apply_infix(right, shortcuts.GT)

    def __ge__(self, right):
        return self._apply_infix(right, shortcuts.GE)

    def __lt__(self, right):
        return self._apply_infix(right, shortcuts.LT)

    def __le__(self, right):
        return self._apply_infix(right, shortcuts.GE)

# EOC FNode
