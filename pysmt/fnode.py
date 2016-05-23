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

import pysmt.environment
from pysmt.operators import (FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF,
                             SYMBOL, FUNCTION,
                             REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT,
                             PLUS, MINUS, TIMES,
                             LE, LT, EQUALS,
                             ITE,
                             TOREAL,
                             BV_CONSTANT, BV_NOT, BV_AND, BV_OR, BV_XOR,
                             BV_CONCAT, BV_EXTRACT,
                             BV_ULT, BV_ULE, BV_NEG, BV_ADD, BV_SUB,
                             BV_MUL, BV_UDIV, BV_UREM,
                             BV_LSHL, BV_LSHR,
                             BV_ROL, BV_ROR,
                             BV_ZEXT, BV_SEXT,
                             BV_SLT, BV_SLE,
                             BV_COMP,
                             BV_SDIV, BV_SREM,
                             BV_ASHR,
                             ARRAY_SELECT, ARRAY_STORE, ARRAY_VALUE)
from pysmt.operators import  (BOOL_OPERATORS, THEORY_OPERATORS,
                              BV_OPERATORS, LIRA_OPERATORS, ARRAY_OPERATORS,
                              RELATIONS, CONSTANTS)
from pysmt.typing import BOOL, REAL, INT, BVType
from pysmt.decorators import deprecated
from pysmt.utils import is_python_integer, is_python_rational, is_python_boolean
from pysmt.utils import twos_complement

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
    __slots__ = ["_content", "_node_id"]

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
        """Returns the subformulae."""
        return self._content.args

    def arg(self, idx):
        """Return the given subformula at the given position."""
        return self._content.args[idx]

    @deprecated("get_free_variables")
    def get_dependencies(self):
        return self.get_free_variables()

    def get_free_variables(self):
        """Return the set of Symbols that are free in the formula."""
        return _env().fvo.get_free_variables(self)

    def get_atoms(self):
        """Return the set of atoms appearing in the formula."""
        return _env().ao.get_atoms(self)

    @deprecated("args")
    def get_sons(self):
        return self.args()

    def simplify(self):
        """Return a simplified version of the formula."""
        return _env().simplifier.simplify(self)

    def substitute(self, subs):
        """Return a formula in which subformula have been substituted.

        subs is a dictionary mapping terms to be subtituted with their
        substitution.
        """
        return _env().substituter.substitute(self, subs=subs)

    def size(self, measure=None):
        """Return the size of the formula according to the given metric.

        See :py:class:`SizeOracle`
        """
        return _env().sizeo.get_size(self, measure)

    def get_type(self):
        """Return the type of the formula by calling the Type-Checker.

        See :py:class:`SimpleTypeChecker`
        """
        return _env().stc.get_type(self)

    def is_constant(self, _type=None, value=None):
        """Test whether the formula is a constant.

        Optionally, check that the constant is of the given type and value.
        """
        if self.node_type() not in CONSTANTS:
            if self.node_type() == ARRAY_VALUE:
                # An array value can be a constant if all its children
                # are constants
                for c in self.args():
                    if not c.is_constant():
                        return False
                if _type is not None or value is not None:
                    raise ValueError("constant type and value checking is " \
                                     "not available for array values")
                return True
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
        """Test whether the formula is a Boolean constant.

        Optionally, check that the constant has the given value.
        """
        return self.is_constant(BOOL, value)

    def is_real_constant(self, value=None):
        """Test whether the formula is a Real constant.

        Optionally, check that the constant has the given value.
        """
        return self.is_constant(REAL, value)

    def is_int_constant(self, value=None):
        """Test whether the formula is an Integer constant.

        Optionally, check that the constant has the given value.
        """
        return self.is_constant(INT, value)

    def is_bv_constant(self, value=None, width=None):
        """Test whether the formula is a BitVector constant.

        Optionally, check that the constant has the given value.
        """
        if value is None and width is None:
            return self.node_type() == BV_CONSTANT

        if width is None:
            return self.is_constant(value=value)
        else:
            return self.is_constant(_type=BVType(width=width),
                                    value=value)

    def is_symbol(self, type_=None):
        """Test whether the formula is a Symbol.

        Optionally, check that the symbol has the given type.
        """
        if type_:
            return self.node_type() == SYMBOL and \
                   self.symbol_type() == type_
        return self.node_type() == SYMBOL

    def is_literal(self):
        """Test whether the formula is a literal.

        A literal is a positive or negative Boolean symbol.
        """
        if self.is_symbol(BOOL):
            return True
        if self.is_not():
            return self.arg(0).is_symbol(BOOL)

    def is_true(self):
        """Test whether the formula is the True Boolean constant."""
        return self.is_bool_constant(True)

    def is_false(self):
        """Test whether the formula is the False Boolean constant."""
        return self.is_bool_constant(False)

    def is_one(self):
        return self.is_real_constant(1) or self.is_int_constant(1)

    def is_zero(self):
        return self.is_real_constant(0) or self.is_int_constant(0)

    def is_toreal(self):
        """Test whether the node is the ToReal operator."""
        return self.node_type() == TOREAL

    def is_forall(self):
        """Test whether the node is the ForAll operator."""
        return self.node_type() == FORALL

    def is_exists(self):
        """Test whether the node is the Exists operator."""
        return self.node_type() == EXISTS

    def is_quantifier(self):
        """Test whether the node is a Quantifier."""
        return self.is_exists() or self.is_forall()

    def is_and(self):
        """Test whether the node is the And operator."""
        return self.node_type() == AND

    def is_or(self):
        """Test whether the node is the Or operator."""
        return self.node_type() == OR

    def is_not(self):
        """Test whether the node is the Not operator."""
        return self.node_type() == NOT

    def is_plus(self):
        """Test whether the node is the Plus operator."""
        return self.node_type() == PLUS

    def is_minus(self):
        """Test whether the node is the Minus operator."""
        return self.node_type() == MINUS

    def is_times(self):
        """Test whether the node is the Times operator."""
        return self.node_type() == TIMES

    def is_implies(self):
        """Test whether the node is the Implies operator."""
        return self.node_type() == IMPLIES

    def is_iff(self):
        """Test whether the node is the Iff operator."""
        return self.node_type() == IFF

    def is_ite(self):
        """Test whether the node is the Ite operator."""
        return self.node_type() == ITE

    def is_equals(self):
        """Test whether the node is the Equals operator."""
        return self.node_type() == EQUALS

    def is_le(self):
        """Test whether the node is the LE (less than equal) relation."""
        return self.node_type() == LE

    def is_lt(self):
        """Test whether the node is the LT (less than) relation."""
        return self.node_type() == LT

    def is_bool_op(self):
        """Test whether the node is a Boolean operator."""
        return self.node_type() in BOOL_OPERATORS

    def is_theory_relation(self):
        """Test whether the node is a theory relation."""
        return self.node_type() in RELATIONS

    def is_theory_op(self):
        """Test whether the node is a theory operator."""
        return self.node_type() in THEORY_OPERATORS

    def is_lira_op(self):
        """Test whether the node is a LIRA operator."""
        return self.node_type() in LIRA_OPERATORS

    def is_bv_op(self):
        """Test whether the node is a BitVector operator."""
        return self.node_type() in BV_OPERATORS

    def is_array_op(self):
        """Test whether the node is an array operator."""
        return self.node_type() in ARRAY_OPERATORS

    def is_bv_not(self):
        """Test whether the node is the BVNot operator."""
        return self.node_type() == BV_NOT

    def is_bv_and(self):
        """Test whether the node is the BVAnd operator."""
        return self.node_type() == BV_AND

    def is_bv_or(self):
        """Test whether the node is the BVOr operator."""
        return self.node_type() == BV_OR

    def is_bv_xor(self):
        """Test whether the node is the BVXor operator."""
        return self.node_type() == BV_XOR

    def is_bv_concat(self):
        """Test whether the node is the BVConcat operator."""
        return self.node_type() == BV_CONCAT

    def is_bv_extract(self):
        """Test whether the node is the BVConcat operator."""
        return self.node_type() == BV_EXTRACT

    def is_bv_ult(self):
        """Test whether the node is the BVULT (unsigned less than) relation."""
        return self.node_type() == BV_ULT

    def is_bv_ule(self):
        """Test whether the node is the BVULE (unsigned less than) relation."""
        return self.node_type() == BV_ULE

    def is_bv_neg(self):
        """Test whether the node is the BVNeg operator."""
        return self.node_type() == BV_NEG

    def is_bv_add(self):
        """Test whether the node is the BVAdd operator."""
        return self.node_type() == BV_ADD

    def is_bv_mul(self):
        """Test whether the node is the BVMul operator."""
        return self.node_type() == BV_MUL

    def is_bv_udiv(self):
        """Test whether the node is the BVUDiv operator."""
        return self.node_type() == BV_UDIV

    def is_bv_urem(self):
        """Test whether the node is the BVURem operator."""
        return self.node_type() == BV_UREM

    def is_bv_lshl(self):
        """Test whether the node is the BVLShl (logical shift left) operator."""
        return self.node_type() == BV_LSHL

    def is_bv_lshr(self):
        """Test whether the node is the BVLShr (logical shift right) operator."""
        return self.node_type() == BV_LSHR

    def is_bv_rol(self):
        """Test whether the node is the BVRol (rotate left) operator."""
        return self.node_type() == BV_ROL

    def is_bv_ror(self):
        """Test whether the node is the BVRor (rotate right) operator."""
        return self.node_type() == BV_ROR

    def is_bv_zext(self):
        """Test whether the node is the BVZext (zero extension) operator."""
        return self.node_type() == BV_ZEXT

    def is_bv_sext(self):
        """Test whether the node is the BVSext (signed extension) operator."""
        return self.node_type() == BV_SEXT

    def is_bv_sub(self):
        """Test whether the node is the BVSub (subtraction) operator."""
        return self.node_type() == BV_SUB

    def is_bv_slt(self):
        """Test whether the node is the BVSLT (signed less-than) operator."""
        return self.node_type() == BV_SLT

    def is_bv_sle(self):
        """Test whether the node is the BVSLE (signed less-than-or-equal-to) operator."""
        return self.node_type() == BV_SLE

    def is_bv_comp(self):
        """Test whether the node is the BVComp (comparison) operator."""
        return self.node_type() == BV_COMP

    def is_bv_sdiv(self):
        """Test whether the node is the BVSDiv (signed division) operator."""
        return self.node_type() == BV_SDIV

    def is_bv_srem(self):
        """Test whether the node is the BVSRem (signed reminder) operator."""
        return self.node_type() == BV_SREM

    def is_bv_ashr(self):
        """Test whether the node is the BVAshr (arithmetic shift right) operator."""
        return self.node_type() == BV_ASHR

    def is_select(self):
        """Test whether the node is the SELECT (array select) operator."""
        return self.node_type() == ARRAY_SELECT

    def is_store(self):
        """Test whether the node is the STORE (array store) operator."""
        return self.node_type() == ARRAY_STORE

    def is_array_value(self):
        """Test whether the node is an array value operator."""
        return self.node_type() == ARRAY_VALUE

    def bv_width(self):
        """Return the BV width of the formula."""
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
        elif self.is_select():
            # This must be a select over an array with BV value type
            ty = self.arg(0).get_type()
            return ty.elem_type.width
        else:
            # BV Operator
            assert self.is_bv_op(), "Unsupported method bv_width on %s" % self
            return self._content.payload[0]

    def bv_extract_start(self):
        """Return the starting index for BVExtract."""
        assert self.is_bv_extract()
        return self._content.payload[1]

    def bv_extract_end(self):
        """Return the ending index for BVExtract."""
        assert self.is_bv_extract()
        return self._content.payload[2]

    def bv_rotation_step(self):
        """Return the rotation step for BVRor and BVRol."""
        assert self.is_bv_ror() or self.is_bv_rol()
        return self._content.payload[1]

    def bv_extend_step(self):
        """Return the extension step for BVZext and BVSext."""
        assert self.is_bv_zext() or self.is_bv_sext()
        return self._content.payload[1]

    def __str__(self):
        return self.serialize(threshold=5)

    def __repr__(self):
        return str(self)

    def serialize(self, threshold=None):
        """Returns a human readable representation of the formula.

        The threshold parameter can be used to limit the amount of the
        formula that will be printed.
        See :py:class:`HRSerializer`
        """
        return _env().serializer.serialize(self, threshold=threshold)

    def is_function_application(self):
        """Test whether the node is a Function application."""
        return self.node_type() == FUNCTION

    @deprecated("is_bool_op")
    def is_boolean_operator(self):
        return self.is_bool_op()

    def is_term(self):
        """Test whether the node is a term.

        All nodes are terms, except for function definitions.
        """
        return not (self.is_symbol() and self.symbol_type().is_function_type())

    def symbol_type(self):
        """Return the type of the Symbol."""
        return self._content.payload[1]

    def symbol_name(self):
        """Return the name of the Symbol."""
        return self._content.payload[0]

    def constant_value(self):
        """Return the value of the Constant."""
        if self.node_type() == BV_CONSTANT:
            return self._content.payload[0]
        return self._content.payload

    def constant_type(self):
        """Return the type of the Constant."""
        if self.node_type() == INT_CONSTANT:
            return INT
        elif self.node_type() == REAL_CONSTANT:
            return REAL
        elif self.node_type() == BOOL_CONSTANT:
            return BOOL
        else:
            assert self.node_type() == BV_CONSTANT,\
                "Unsupported method constant_type '%s'" % self
            return BVType(width=self.bv_width())

    def bv2nat(self):
        """Return the unsigned value encoded by the BitVector."""
        return self.bv_unsigned_value()

    def bv_unsigned_value(self):
        """Return the unsigned value encoded by the BitVector."""
        return self.constant_value()

    def bv_signed_value(self):
        """Return the signed value encoded by the BitVector."""
        return twos_complement(self.constant_value(), self.bv_width())

    def bv_bin_str(self, reverse=False):
        """Return the binary representation of the BitVector as string.

        The reverse option is provided to deal with MSB/LSB.
        """
        fstr = '{0:0%db}' % self.bv_width()
        bitstr = fstr.format(self.constant_value())
        if reverse:
            bitstr = bitstr[::-1]
        return bitstr

    def array_value_index_type(self):
        return self._content.payload

    def array_value_get(self, index):
        assert index.is_constant()
        idx = index.simplify()
        args = self.args()
        s = 0
        e = (len(args) - 1) / 2
        while e - s > 0:
            p = (e - s) / 2
            i = args[2 * p + 1]
            if i == idx:
                return args[i+1]
            elif i < idx:
                s = p
            else:
                e = p
        return self.array_value_default()

    def array_value_assigned_values_map(self):
        res = {}
        args = self.args()
        for i,c in enumerate(args[1::2]):
            res[c] = args[i+1]
        return res

    def array_value_default(self):
        return self.args()[0]

    def function_name(self):
        """Return the Function name."""
        return self._content.payload

    def quantifier_vars(self):
        """Return the list of quantified variables."""
        return self._content.payload

    # Infix Notation
    def _apply_infix(self, right, function, bv_function=None):
        if _env().enable_infix_notation:
            mgr = _mgr()
            # BVs
            # Default bv_function to function
            if bv_function is None: bv_function = function
            if _is_bv(self):
                if is_python_integer(right):
                    right = mgr.BV(right, width=self.bv_width())
                return bv_function(self, right)
            # Boolean, Integer and Arithmetic
            if is_python_boolean(right):
                right = mgr.Bool(right)
            elif is_python_integer(right):
                ty = self.get_type()
                if ty.is_real_type():
                    right = mgr.Real(right)
                else:
                    right = mgr.Int(right)
            elif is_python_rational(right):
                right = mgr.Real(right)
            return function(self, right)
        else:
            raise Exception("Cannot use infix notation")

    def Implies(self, right):
        return self._apply_infix(right, _mgr().Implies)

    def Iff(self, right):
        return self._apply_infix(right, _mgr().Iff)

    def Equals(self, right):
        return self._apply_infix(right, _mgr().Equals)

    def Ite(self, right):
        return self._apply_infix(right, _mgr().Ite)

    def And(self, right):
        return self._apply_infix(right, _mgr().And)

    def Or(self, right):
        return self._apply_infix(right, _mgr().Or)

    # BV
    def BVSLT(self, right):
        return self._apply_infix(right, _mgr().BVSLT)

    def BVSLE(self, right):
        return self._apply_infix(right, _mgr().BVSLE)

    def BVComp(self, right):
        return self._apply_infix(right, _mgr().BVComp)

    def BVSDiv(self, right):
        return self._apply_infix(right, _mgr().BVSDiv)

    def BVSRem(self, right):
        return self._apply_infix(right, _mgr().BVSRem)

    def BVAShr(self, right):
        return self._apply_infix(right, _mgr().BVAShr)

    def BVNand(self, right):
        return self._apply_infix(right, _mgr().BVNand)

    def BVNor(self, right):
        return self._apply_infix(right, _mgr().BVNor)

    def BVXnor(self, right):
        return self._apply_infix(right, _mgr().BVXnor)

    def BVSGT(self, right):
        return self._apply_infix(right, _mgr().BVSGT)

    def BVSGE(self, right):
        return self._apply_infix(right, _mgr().BVSGE)

    def BVSMod(self, right):
        return self._apply_infix(right, _mgr().BVSMod)

    def BVRol(self, steps):
        return _mgr().BVRol(self, steps)

    def BVRor(self, steps):
        return _mgr().BVRor(self, steps)

    def BVZExt(self, increase):
        return _mgr().BVZExt(self, increase)

    def BVSExt(self, increase):
        return _mgr().BVSExt(self, increase)

    def BVRepeat(self, count):
        return _mgr().BVRepeat(self, count)

    #
    # Infix operators
    #
    def __add__(self, right):
        return self._apply_infix(right, _mgr().Plus, _mgr().BVAdd)

    def __radd__(self, right):
        return self._apply_infix(right, _mgr().Plus, _mgr().BVAdd)

    def __sub__(self, right):
        return self._apply_infix(right, _mgr().Minus, _mgr().BVSub)

    def __rsub__(self, left):
        # Swap operators to perform right-subtract
        # For BVs we might need to build the BV constant
        if _is_bv(self):
            if is_python_integer(left):
                left = _mgr().BV(left, width=self.bv_width())
            return left._apply_infix(self, _mgr().BVSub)
        # (x - y) = (-y + x)
        minus_self = -self
        return minus_self._apply_infix(left, _mgr().Plus)

    def __mul__(self, right):
        return self._apply_infix(right, _mgr().Times, _mgr().BVMul)

    def __rmul__(self, right):
        return self._apply_infix(right, _mgr().Times, _mgr().BVMul)

    def __div__(self, right):
        return self._apply_infix(right, _mgr().Div, _mgr().BVUDiv)

    def __truediv__(self, right):
        return self.__div__(right)

    def __gt__(self, right):
        return self._apply_infix(right, _mgr().GT, _mgr().BVUGT)

    def __ge__(self, right):
        return self._apply_infix(right, _mgr().GE, _mgr().BVUGE)

    def __lt__(self, right):
        return self._apply_infix(right, _mgr().LT, _mgr().BVULT)

    def __le__(self, right):
        return self._apply_infix(right, _mgr().LE, _mgr().BVULE)

    def __and__(self, other):
        return self._apply_infix(other, _mgr().And, _mgr().BVAnd)

    def __rand__(self, other):
        return self._apply_infix(other, _mgr().And, _mgr().BVAnd)

    def __or__(self, other):
        return self._apply_infix(other, _mgr().Or, _mgr().BVOr)

    def __ror__(self, other):
        return self._apply_infix(other, _mgr().Or, _mgr().BVOr)

    def __xor__(self, other):
        return self._apply_infix(other, _mgr().Xor, _mgr().BVXor)

    def __rxor__(self, other):
        return self._apply_infix(other, _mgr().Xor, _mgr().BVXor)

    def __neg__(self):
        if _is_bv(self):
            return _mgr().BVNeg(self)
        return self._apply_infix(-1, _mgr().Times)

    def __invert__(self):
        if not _env().enable_infix_notation:
            raise Exception("Cannot use infix notation")
        if _is_bv(self):
            return _mgr().BVNot(self)
        return _mgr().Not(self)

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

    def __getitem__(self, idx):
        if not _env().enable_infix_notation:
            raise Exception("Cannot use infix notation")
        if isinstance(idx, slice):
            end = idx.stop
            start = idx.start
            if start is None: start = 0
        else:
            # Single point [idx]
            end = idx
            start = idx
        if _is_bv(self):
            return _mgr().BVExtract(self, start=start, end=end)
        raise NotImplementedError

    def __lshift__(self, right):
        return self._apply_infix(right, None, bv_function=_mgr().BVLShl)

    def __rshift__(self, right):
        return self._apply_infix(right, None, bv_function=_mgr().BVLShr)

    def __mod__(self, right):
        return self._apply_infix(right, None, bv_function=_mgr().BVURem)
# EOC FNode

def _env():
    """Aux function to obtain the environment."""
    return pysmt.environment.get_env()

def _mgr():
    """Aux function to obtain the formula manager."""
    return pysmt.environment.get_env().formula_manager

def _is_bv(node):
    """Aux function to check if a fnode is a BV."""
    return (node.is_symbol() and node.symbol_type().is_bv_type()) or \
            node.node_type() in BV_OPERATORS
