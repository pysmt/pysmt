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
"""FNode are the building blocks of formulae."""
import collections

import pysmt.shortcuts
from pysmt.operators import CONSTANTS
from pysmt.operators import (FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF,
                             SYMBOL, FUNCTION,
                             REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT,
                             PLUS, MINUS, TIMES,
                             LE, LT, EQUALS,
                             ITE,
                             TOREAL,
                             BV_CONSTANT, BV_NOT, BV_AND, BV_OR, BV_XOR,
                             BV_CONCAT, BV_EXTRACT,
                             BV_ULT, BV_NEG, BV_ADD,
                             BV_MUL, BV_UDIV, BV_UREM,
                             BV_LSHL, BV_LSHR,
                             BV_ROL, BV_ROR,
                             BV_ZEXT, BV_SEXT,
                             BV_OPERATORS, THEORY_OPERATORS, RELATIONS)
from pysmt.typing import BOOL, REAL, INT, PYSMT_TYPES, BVType
from pysmt.decorators import deprecated
from pysmt.utils import is_python_integer, is_python_rational, is_python_boolean

FNodeContent = collections.namedtuple("FNodeContent",
                                      ["node_type", "args", "payload"])

class FNode(object):
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

    The node_id is an integer uniquely identifying the node within the
    FormulaManager it belongs.
    """

    def __init__(self, content, node_id):
        self._content = content
        self._node_id = node_id
        return

    # __eq__ is left as default while __hash__ uses the node id. This
    # is because we always have shared FNodes, hence in a single
    # environment two nodes have always different ids, but in
    # different environments they can have the same id. This is not an
    # issue since, by default, equality coincides with identity.
    def __hash__(self):
        return self._node_id

    def node_id(self):
        return self._node_id

    def node_type(self):
        return self._content.node_type

    def args(self):
        return self._content.args

    def arg(self, idx):
        return self._content.args[idx]

    @deprecated("get_free_variables")
    def get_dependencies(self):
        return self.get_free_variables()

    def get_free_variables(self):
        return pysmt.shortcuts.get_free_variables(self)

    def get_atoms(self):
        return pysmt.shortcuts.get_atoms(self)

    def get_sons(self):
        return self.args()

    def simplify(self):
        return pysmt.shortcuts.simplify(self)

    def substitute(self, subs):
        return pysmt.shortcuts.substitute(self, subs=subs)

    def size(self, measure=None):
        return pysmt.shortcuts.get_formula_size(self, measure)

    def is_constant(self, _type=None, value=None):
        if self.node_type() not in CONSTANTS:
            return False

        if _type is not None:
            if _type.is_int_type() and self.node_type() != INT_CONSTANT:
                return False
            if _type.is_real_type() and self.node_type() != REAL_CONSTANT:
                return False
            if _type.is_bool_type() and self.node_type() != BOOL_CONSTANT:
                return False
            if _type.is_bv_type():
                if self.node_type() != BV_CONSTANT:
                    return False
                if self._content.payload[1] != _type.width:
                    return False

        if value is not None:
            return value == self.constant_value()
        return True

    def is_bool_constant(self, value=None):
        return self.is_constant(BOOL, value)

    def is_real_constant(self, value=None):
        return self.is_constant(REAL, value)

    def is_int_constant(self, value=None):
        return self.is_constant(INT, value)

    def is_bv_constant(self, value=None, width=None):
        if value is None and width is None:
            return self.node_type() == BV_CONSTANT

        if width is None:
            return self.is_constant(value=value)
        else:
            return self.is_constant(_type=BVType(width=width),
                                    value=value)

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
        return self.is_real_constant(1) or self.is_int_constant(1)

    def is_zero(self):
        return self.is_real_constant(0) or self.is_int_constant(0)

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

    def is_theory_relation(self):
        return self.node_type() in RELATIONS

    def is_theory_op(self):
        return self.node_type() in THEORY_OPERATORS

    def is_bv_op(self):
        return self.node_type() in BV_OPERATORS

    def is_bv_not(self):
        return self.node_type() == BV_NOT

    def is_bv_and(self):
        return self.node_type() == BV_AND

    def is_bv_or(self):
        return self.node_type() == BV_OR

    def is_bv_xor(self):
        return self.node_type() == BV_XOR

    def is_bv_concat(self):
        return self.node_type() == BV_CONCAT

    def is_bv_extract(self):
        return self.node_type() == BV_EXTRACT

    def is_bv_ult(self):
        return self.node_type() == BV_ULT

    def is_bv_neg(self):
        return self.node_type() == BV_NEG

    def is_bv_add(self):
        return self.node_type() == BV_ADD

    def is_bv_mul(self):
        return self.node_type() == BV_MUL

    def is_bv_udiv(self):
        return self.node_type() == BV_UDIV

    def is_bv_urem(self):
        return self.node_type() == BV_UREM

    def is_bv_lshl(self):
        return self.node_type() == BV_LSHL

    def is_bv_lshr(self):
        return self.node_type() == BV_LSHR

    def is_bv_rol(self):
        return self.node_type() == BV_ROL

    def is_bv_ror(self):
        return self.node_type() == BV_ROR

    def is_bv_zext(self):
        return self.node_type() == BV_ZEXT

    def is_bv_sext(self):
        return self.node_type() == BV_SEXT

    def bv_width(self):
        if self.is_bv_constant():
            return self._content.payload[1]
        elif self.is_symbol():
            assert self.symbol_type().is_bv_type()
            return self.symbol_type().width
        elif self.is_function_application():
            # Return width defined in the declaration
            return self.function_name().symbol_type().return_type.width
        elif self.is_ite():
            # Recursively call bv_width on the left child
            # (The right child has the same width if the node is well-formed)
            width_l = self.arg(1).bv_width()
            return width_l
        else:
            # BV Operator
            assert self.is_bv_op(), "Unsupported method bv_width on %s" % self
            return self._content.payload[0]

    def bv_extract_start(self):
        assert self.is_bv_extract()
        return self._content.payload[1]

    def bv_extract_end(self):
        assert self.is_bv_extract()
        return self._content.payload[2]

    def bv_rotation_step(self):
        assert self.is_bv_ror() or self.is_bv_rol()
        return self._content.payload[1]

    def bv_extend_step(self):
        assert self.is_bv_zext() or self.is_bv_sext()
        return self._content.payload[1]

    def __str__(self):
        return self.serialize(threshold=5)

    def __repr__(self):
        return str(self)

    def serialize(self, threshold=None):
        return pysmt.shortcuts.serialize(self, threshold=threshold)

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

    def symbol_type(self):
        return self._content.payload[1]

    def symbol_name(self):
        return self._content.payload[0]

    def constant_value(self):
        if self.node_type() == BV_CONSTANT:
            return self._content.payload[0]
        return self._content.payload

    def bv_unsigned_value(self):
        # TODO: We currently support only unsigned bitvectors
        value = self.constant_value()
        return value

    def bv_bin_str(self, reverse=False):
        fstr = '{0:0%db}' % self.bv_width()
        bitstr = fstr.format(self.constant_value())
        if reverse:
            bitstr = bitstr[::-1]
        return bitstr

    def function_name(self):
        return self._content.payload

    def quantifier_vars(self):
        return self._content.payload

    # Infix Notation
    def _apply_infix(self, right, function):
        env = pysmt.shortcuts.get_env()
        if env.enable_infix_notation:
            if is_python_boolean(right):
                right = pysmt.shortcuts.Bool(right)
            elif is_python_integer(right):
                ty = env.stc.get_type(self)
                if ty.is_real_type():
                    right = pysmt.shortcuts.Real(right)
                else:
                    right = pysmt.shortcuts.Int(right)
            elif is_python_rational(right):
                right = pysmt.shortcuts.Real(right)

            return function(self, right)
        else:
            raise Exception("Cannot use infix notation")

    def Implies(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Implies)

    def Iff(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Iff)

    def Equals(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Equals)

    def Ite(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Ite)

    def And(self, right):
        return self._apply_infix(right, pysmt.shortcuts.And)

    def Or(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Or)

    def __add__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Plus)

    def __radd__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Plus)

    def __sub__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Minus)

    def __rsub__(self, right):
        minus_self = -self
        return minus_self._apply_infix(right, pysmt.shortcuts.Plus)

    def __mul__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Times)

    def __rmul__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Times)

    def __div__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Div)

    def __truediv__(self, right):
        return self.__div__(right)

    def __gt__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.GT)

    def __ge__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.GE)

    def __lt__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.LT)

    def __le__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.LE)

    def __and__(self, other):
        return self.And(other)

    def __rand__(self, other):
        return self.And(other)

    def __or__(self, other):
        return self.Or(other)

    def __ror__(self, other):
        return self.Or(other)

    def __xor__(self, other):
        return self._apply_infix(other, pysmt.shortcuts.Xor)

    def __neg__(self):
        return self._apply_infix(-1, pysmt.shortcuts.Times)

    def __invert__(self):
        env = pysmt.shortcuts.get_env()
        if not env.enable_infix_notation:
            raise Exception("Cannot use infix notation")
        return pysmt.shortcuts.Not(self)

    def __int__(self):
        if self.is_int_constant():
            return self.constant_value()
        raise NotImplementedError("Cannot convert `%s` to integer" % str(self))

    def __long__(self):
        if self.is_int_constant():
            return self.constant_value()
        raise NotImplementedError("Cannot convert `%s` to integer" % str(self))

    def __float__(self):
        if self.is_int_constant() or self.is_real_constant():
            return float(self.constant_value())
        raise NotImplementedError("Cannot convert `%s` to float" % str(self))



# EOC FNode
