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
"""The FormulaManager is used to create formulae.

All objects are memoized so that two syntactically equivalent formulae
are represented by the same object.

The FormulaManager provides many more constructors than the operators
defined (operators.py). This is because many operators are rewritten,
and therefore are only virtual. Common examples are GE, GT that are
rewritten as LE and LT. Similarly, the operator Xor is rewritten using
its definition.
"""

import sys
if sys.version_info >= (3, 3):
    from collections.abc import Iterable
else:
    from collections import Iterable

import warnings

import pysmt.typing as types
import pysmt.operators as op


from pysmt.fnode import FNode, FNodeContent
from pysmt.exceptions import UndefinedSymbolError, PysmtValueError,PysmtTypeError
from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.constants import Fraction
from pysmt.constants import (is_pysmt_fraction,
                             is_pysmt_integer,
                             is_python_rational,
                             is_python_integer,
                             is_python_string,
                             pysmt_fraction_from_rational,
                             pysmt_integer_from_integer)


class FormulaManager(object):
    """FormulaManager is responsible for the creation of all formulae."""

    def __init__(self, env=None):
        self.env = env
        # Attributes for handling symbols and formulae
        self.formulae = {}
        self.symbols = {}
        self._fresh_guess = 0
        # get_type() from TypeChecker will be initialized lazily
        self.get_type = None
        self._next_free_id = 1

        self.int_constants = {}
        self.real_constants = {}
        self.string_constants = {}

        self.true_formula = self.create_node(node_type=op.BOOL_CONSTANT,
                                             args=tuple(),
                                             payload=True)
        self.false_formula = self.create_node(node_type=op.BOOL_CONSTANT,
                                              args=tuple(),
                                              payload=False)
        return

    def _do_type_check_real(self, formula):
        self.get_type(formula)

    def _do_type_check(self, formula):
        self.get_type = self.env.stc.get_type
        self._do_type_check = self._do_type_check_real
        return self._do_type_check(formula)

    def create_node(self, node_type, args, payload=None):
        content = FNodeContent(node_type, args, payload)
        if content in self.formulae:
            return self.formulae[content]
        else:
            n = FNode(content, self._next_free_id)
            self._next_free_id += 1
            self.formulae[content] = n
            self._do_type_check(n)
            return n

    def _create_symbol(self, name, typename=types.BOOL):
        if len(name) == 0:
            raise PysmtValueError("Empty string is not a valid name")
        if not isinstance(typename, types.PySMTType):
            raise PysmtValueError("typename must be a PySMTType.")
        n = self.create_node(node_type=op.SYMBOL,
                             args=tuple(),
                             payload=(name, typename))
        self.symbols[name] = n
        return n

    def new_fresh_symbol(self, typename, base="FV%d"):
        count = self._fresh_guess
        while (base % count) in self.symbols:
            count = count + 1

        name = (base % count)
        self._fresh_guess = count + 1
        v = self.Symbol(name, typename)
        assert v is not None
        return v

    def get_symbol(self, name):
        try:
            return self.symbols[name]
        except KeyError:
            raise UndefinedSymbolError(name)

    def get_all_symbols(self):
        return self.symbols.values()

    def get_or_create_symbol(self, name, typename):
        s = self.symbols.get(name, None)
        if s is None:
            return self._create_symbol(name, typename)
        if not s.symbol_type() == typename:
            raise PysmtTypeError("Trying to redefine symbol '%s' with a new type"
                                 ". Previous type was '%s' new type is '%s'" %
                                 (name, s.symbol_type(), typename))
        return s

    # Node definitions start here

    def Symbol(self, name, typename=types.BOOL):
        return self.get_or_create_symbol(name, typename)

    def FreshSymbol(self, typename=types.BOOL, template=None):
        if template is None:
            return self.new_fresh_symbol(typename)
        return self.new_fresh_symbol(typename, template)

    def ForAll(self, variables, formula):
        """ Creates an expression of the form:
            Forall variables. formula(variables)

        Restrictions:
         - Formula must be of boolean type
         - Variables must be BOOL, REAL or INT
        """
        if len(variables) == 0:
            return formula
        return self.create_node(node_type=op.FORALL,
                                args=(formula,),
                                payload=tuple(variables))

    def Exists(self, variables, formula):
        """ Creates an expression of the form:
            Exists variables. formula(variables)

        Restrictions:
         - Formula must be of boolean type
         - Variables must be BOOL, REAL or INT
        """
        if len(variables) == 0:
            return formula
        return self.create_node(node_type=op.EXISTS,
                                args=(formula,),
                                payload=tuple(variables))

    def Function(self, vname, params):
        """Returns the function application of vname to params.

        Note: Applying a 0-arity function returns the function itself.
        """
        if len(params) == 0:
            return vname
        assert len(params) == len(vname.symbol_type().param_types)
        return self.create_node(node_type=op.FUNCTION,
                                args=tuple(params),
                                payload=vname)

    def Not(self, formula):
        """ Creates an expression of the form:
            not formula

        Restriction: Formula must be of boolean type
        """
        if formula.is_not():
            return formula.arg(0)
        return self.create_node(node_type=op.NOT, args=(formula,))

    def Implies(self, left, right):
        """ Creates an expression of the form:
            left -> right

        Restriction: Left and Right must be of boolean type
        """
        return self.create_node(node_type=op.IMPLIES, args=(left, right))

    def Iff(self, left, right):
        """ Creates an expression of the form:
            left <-> right

        Restriction: Left and Right must be of boolean type
        """
        return self.create_node(node_type=op.IFF, args=(left, right))

    def Minus(self, left, right):
        """ Creates an expression of the form:
            left - right

        Restriction: Left and Right must be both INT or REAL type
        """
        return self.create_node(node_type=op.MINUS, args=(left, right))

    def Times(self, *args):
        """ Creates a multiplication of terms

        This function has polimorphic n-arguments:
          - Times(a,b,c)
          - Times([a,b,c])

        Restriction:
         - Arguments must be all of the same type
         - Arguments must be INT or REAL
        """
        tuple_args = self._polymorph_args_to_tuple(args)
        if len(tuple_args) == 0:
            raise PysmtTypeError("Cannot create a Times without arguments.")

        if len(tuple_args) == 1:
            return tuple_args[0]
        else:
            return self.create_node(node_type=op.TIMES,
                                    args=tuple_args)

    def Pow(self, base, exponent):
        """ Creates the n-th power of the base.

        The exponent must be a constant.
        """
        if not exponent.is_constant():
            raise PysmtValueError("The exponent of POW must be a constant.", exponent)

        if base.is_constant():
            val = base.constant_value() ** exponent.constant_value()
            if base.is_constant(types.REAL):
                return self.Real(val)
            else:
                assert base.is_constant(types.INT)
                return self.Int(val)
        return self.create_node(node_type=op.POW, args=(base, exponent))

    def Div(self, left, right):
        """ Creates an expression of the form: left / right """
        if (right.is_constant(types.REAL, 0) or
            right.is_constant(types.INT, 0)) \
           and self.env.enable_div_by_0:
            # Allow division by 0 byt warn the user
            # This can only happen in non-linear logics
            warnings.warn("Warning: Division by 0")
        elif right.is_constant(types.REAL):
            # If right is a constant we rewrite as left * 1/right
            inverse = Fraction(1) / right.constant_value()
            return self.Times(left, self.Real(inverse))

        # This is a non-linear expression
        return self.create_node(node_type=op.DIV,
                                args=(left, right))

    def Equals(self, left, right):
        """ Creates an expression of the form: left = right

        For the boolean case use Iff
        """
        return self.create_node(node_type=op.EQUALS,
                                args=(left, right))

    def NotEquals(self, left, right):
        """ Creates an expression of the form: left != right"""
        return self.Not(self.Equals(left, right))

    def GE(self, left, right):
        """ Creates an expression of the form:
            left >= right

        Restriction: Left and Right must be both REAL or INT type
        """
        return self.create_node(node_type=op.LE, args=(right, left))

    def GT(self, left, right):
        """ Creates an expression of the form:
            left > right

        Restriction: Left and Right must be both REAL or INT type
        """
        return self.create_node(node_type=op.LT, args=(right, left))

    def LE(self, left, right):
        """ Creates an expression of the form:
            left <= right

        Restriction: Left and Right must be both REAL or INT type
        """
        return self.create_node(node_type=op.LE, args=(left, right))

    def LT(self, left, right):
        """ Creates an expression of the form:
            left < right

        Restriction: Left and Right must be both REAL or INT type
        """
        return self.create_node(node_type=op.LT, args=(left, right))

    def Ite(self, iff, left, right):
        """ Creates an expression of the form:
            if( iff ) then  left  else  right

        Restriction:
          - Iff must be BOOL
          - Left and Right must be both of the same type
        """
        return self.create_node(node_type=op.ITE, args=(iff, left, right))

    def Real(self, value):
        """ Returns a Real-type constant of the given value.

        value can be:
          - A Fraction(n,d)
          - A tuple (n,d)
          - A long or int n
          - A float
          - (Optionally) a mpq or mpz object
        """
        if value in self.real_constants:
            return self.real_constants[value]

        if is_pysmt_fraction(value):
            val = value
        elif type(value) == tuple:
            val = Fraction(value[0], value[1])
        elif is_python_rational(value):
            val = pysmt_fraction_from_rational(value)
        else:
            raise PysmtTypeError("Invalid type in constant. The type was:" + \
                                 str(type(value)))

        n = self.create_node(node_type=op.REAL_CONSTANT,
                             args=tuple(),
                             payload=val)
        self.real_constants[value] = n
        return n

    def Int(self, value):
        """Return a constant of type INT."""
        if value in self.int_constants:
            return self.int_constants[value]

        if is_pysmt_integer(value):
            val = value
        elif is_python_integer(value):
            val = pysmt_integer_from_integer(value)
        else:
            raise PysmtTypeError("Invalid type in constant. The type was:" + \
                                 str(type(value)))
        n = self.create_node(node_type=op.INT_CONSTANT,
                             args=tuple(),
                             payload=val)
        self.int_constants[value] = n
        return n

    def String(self, value):
        """Return a constant of type STRING."""
        if value in self.string_constants:
            return self.string_constants[value]

        if is_python_string(value):
            n = self.create_node(node_type=op.STR_CONSTANT,
                                 args=tuple(),
                                 payload=value)
            self.string_constants[value] = n
            return n
        else:
            raise TypeError("Invalid type in constant. The type was:" + \
                            str(type(value)))

    def TRUE(self):
        """Return the boolean constant True."""
        return self.true_formula

    def FALSE(self):
        """Return the boolean constant False."""
        return self.false_formula

    def Bool(self, value):
        if type(value) != bool:
            raise PysmtTypeError("Expecting bool, got %s" % type(value))

        if value:
            return self.true_formula
        else:
            return self.false_formula

    def And(self, *args):
        """ Returns a conjunction of terms.

        This function has polimorphic arguments:
          - And(a,b,c)
          - And([a,b,c])

        Restriction: Arguments must be boolean
        """
        tuple_args = self._polymorph_args_to_tuple(args)

        if len(tuple_args) == 0:
            return self.TRUE()
        elif len(tuple_args) == 1:
            return tuple_args[0]
        else:
            return self.create_node(node_type=op.AND,
                                    args=tuple_args)

    def Or(self, *args):
        """ Returns an disjunction of terms.

        This function has polimorphic n-arguments:
          - Or(a,b,c)
          - Or([a,b,c])

        Restriction: Arguments must be boolean
        """
        tuple_args = self._polymorph_args_to_tuple(args)

        if len(tuple_args) == 0:
            return self.FALSE()
        elif len(tuple_args) == 1:
            return tuple_args[0]
        else:
            return self.create_node(node_type=op.OR,
                                    args=tuple_args)

    def Plus(self, *args):
        """ Returns an sum of terms.

        This function has polimorphic n-arguments:
          - Plus(a,b,c)
          - Plus([a,b,c])

        Restriction:
         - Arguments must be all of the same type
         - Arguments must be INT or REAL
        """
        tuple_args = self._polymorph_args_to_tuple(args)
        if len(tuple_args) == 0:
            raise PysmtTypeError("Cannot create a Plus without arguments.")

        if len(tuple_args) == 1:
            return tuple_args[0]
        else:
            return self.create_node(node_type=op.PLUS,
                                    args=tuple_args)

    def ToReal(self, formula):
        """ Cast a formula to real type. """
        t = self.env.stc.get_type(formula)
        if t == types.REAL:
            # Ignore casting of a Real
            return formula
        elif t == types.INT:
            if formula.is_int_constant():
                return self.Real(formula.constant_value())
            return self.create_node(node_type=op.TOREAL,
                                    args=(formula,))
        else:
            raise PysmtTypeError("Argument is of type %s, but INT was "
                                 "expected!\n" % t)

    def AtMostOne(self, *args):
        """ At most one of the bool expressions can be true at anytime.

        This using a quadratic encoding:
           A -> !(B \\/ C)
           B -> !(C)
        """
        bool_exprs = self._polymorph_args_to_tuple(args)
        constraints = []
        for (i, elem) in enumerate(bool_exprs[:-1], start=1):
            constraints.append(self.Implies(elem,
                                            self.Not(self.Or(bool_exprs[i:]))))
        return self.And(constraints)


    def ExactlyOne(self, *args):
        """ Encodes an exactly-one constraint on the boolean symbols.

        This using a quadratic encoding:
           A \\/ B \\/ C
           A -> !(B \\/ C)
           B -> !(C)
        """
        args = self._polymorph_args_to_tuple(args)
        return self.And(self.Or(*args),
                        self.AtMostOne(*args))

    def AllDifferent(self, *args):
        """ Encodes the 'all-different' constraint using two possible
        encodings.

        AllDifferent(x, y, z) := (x != y) & (x != z) & (y != z)
        """
        exprs = self._polymorph_args_to_tuple(args)
        res = []
        for i, a in enumerate(exprs):
            for b in exprs[i+1:]:
                res.append(self.Not(self.EqualsOrIff(a, b)))
        return self.And(res)

    def Xor(self, left, right):
        """Returns the xor of left and right: left XOR right """
        return self.Not(self.Iff(left, right))

    def Min(self, *args):
        """Returns the encoding of the minimum expression within args"""
        exprs = self._polymorph_args_to_tuple(args)
        assert len(exprs) > 0
        if len(exprs) == 1:
            return exprs[0]
        elif len(exprs) == 2:
            a, b = exprs
            return self.Ite(self.LE(a, b), a, b)
        else:
            h = len(exprs) // 2
            return self.Min(self.Min(exprs[0:h]), self.Min(exprs[h:]))

    def Max(self, *args):
        """Returns the encoding of the maximum expression within args"""
        exprs = self._polymorph_args_to_tuple(args)
        assert len(exprs) > 0
        if len(exprs) == 1:
            return exprs[0]
        elif len(exprs) == 2:
            a, b = exprs
            return self.Ite(self.LE(a, b), b, a)
        else:
            h = len(exprs) // 2
            return self.Max(self.Max(exprs[0:h]), self.Max(exprs[h:]))

    def EqualsOrIff(self, left, right):
        """Returns Equals() or Iff() depending on the type of the arguments.

        This can be used to deal with ambiguous cases where we might be
        dealing with both Theory and Boolean atoms.
        """
        type_ = self.env.stc.get_type(left)
        if type_.is_bool_type():
            return self.Iff(left, right)
        else:
            return self.Equals(left, right)

    # BitVectors
    def BV(self, value, width=None):
        """Return a constant of type BitVector.

        value can be either:
        - a string of 0s and 1s
        - a string starting with "#b" followed by a sequence of 0s and 1s
        - an integer number s.t. 0 <= value < 2**width

        In order to create the BV representation of a signed integer,
        the SBV() method shall be used.
        """

        if type(value) is str:
            if value.startswith("#b"):
                str_width = len(value)-2
                value = int(value[2:],2)
            elif all(v in ["0", "1"] for v in value):
                str_width = len(value)
                value = int(value, 2)
            else:
                raise PysmtValueError("Expecting binary value as string, got " \
                                      "%s instead." % value)

            if width is not None and width != str_width:
                raise PysmtValueError("Specified width does not match string " \
                                      "width (%d != %d)" % (width, str_width))
            width = str_width

        if width is None:
            raise PysmtValueError("Need to specify a width for the constant")

        if is_pysmt_integer(value):
            _value = value
        elif is_python_integer(value):
            _value = pysmt_integer_from_integer(value)
        else:
            raise PysmtTypeError("Invalid type in constant. The type was: %s" \
                                 % str(type(value)))
        if _value < 0:
            raise PysmtValueError("Cannot specify a negative value: %d" \
                                  % _value)
        if _value >= 2**width:
            raise PysmtValueError("Cannot express %d in %d bits" \
                                  % (_value, width))

        return self.create_node(node_type=op.BV_CONSTANT,
                                args=tuple(),
                                payload=(_value, width))


    def SBV(self, value, width=None):
        """Returns a constant of type BitVector interpreting the sign.

        If the specified value is an integer, it is converted in the
        2-complement representation of the given number, otherwise the
        behavior is the same as BV().
        """
        if is_python_integer(value):
            if width is None:
                raise PysmtValueError("Need to specify a width for the constant")

            min_val = -(2**(width-1))
            max_val = (2**(width-1)) - 1
            if value < min_val:
                raise PysmtValueError("Cannot represent a value (%d) lower " \
                                      "than %d in %d bits" % (value, min_val,
                                                              width))
            if value > max_val:
                raise PysmtValueError("Cannot represent a value (%d) greater " \
                                      "than %d in %d bits" % (value, max_val,
                                                              width))

            if value >= 0:
                return self.BV(value, width)
            else:
                comp_value = (2**width) + value # value is negative!
                return self.BV(comp_value, width)
        else:
            return self.BV(value, width=width)

    def BVOne(self, width):
        """Returns the bit-vector representing the unsigned one."""
        return self.BV(1, width=width)

    def BVZero(self, width):
        """Returns the bit-vector with all bits set to zero."""
        return self.BV(0, width=width)

    def BVNot(self, formula):
        """Returns the bitvector Not(bv)"""
        return self.create_node(node_type=op.BV_NOT,
                                args=(formula,),
                                payload=(formula.bv_width(),))

    def BVAnd(self, left, right):
        """Returns the Bit-wise AND of two bitvectors of the same size."""
        return self.create_node(node_type=op.BV_AND,
                                args=(left,right),
                                payload=(left.bv_width(),))

    def BVOr(self, left, right):
        """Returns the Bit-wise OR of two bitvectors of the same size."""
        return self.create_node(node_type=op.BV_OR,
                                args=(left,right),
                                payload=(left.bv_width(),))

    def BVXor(self, left, right):
        """Returns the Bit-wise XOR of two bitvectors of the same size."""
        return self.create_node(node_type=op.BV_XOR,
                                args=(left,right),
                                payload=(left.bv_width(),))

    def BVConcat(self, *args):
        """Returns the Concatenation of the given BVs"""
        ex = self._polymorph_args_to_tuple(args)
        base = self.create_node(node_type=op.BV_CONCAT,
                                args=(ex[0], ex[1]),
                                payload=(ex[0].bv_width() + ex[1].bv_width(),))
        for e in ex[2:]:
            base = self.create_node(node_type=op.BV_CONCAT,
                                    args=(base, e),
                                    payload=(base.bv_width() + e.bv_width(),))
        return base

    def BVExtract(self, formula, start=0, end=None):
        """Returns the slice of formula from start to end (inclusive)."""
        if end is None: end = formula.bv_width()-1
        assert is_python_integer(start) and is_python_integer(end)
        assert end >= start and start >= 0, "Start: %d ; End: %d" % (start,end)
        size = end-start+1

        assert size <= formula.bv_width(), \
            "Invalid size: start=%d, end=%d, width=%d" % \
            (start, end, formula.bv_width())
        return self.create_node(node_type=op.BV_EXTRACT,
                                args=(formula,),
                                payload=(size, start, end))

    def BVULT(self, left, right):
        """Returns the formula left < right."""
        return self.create_node(node_type=op.BV_ULT,
                                args=(left, right))

    def BVUGT(self, left, right):
        """Returns the formula left > right."""
        return self.create_node(node_type=op.BV_ULT,
                                args=(right, left))

    def BVULE(self, left, right):
        """Returns the formula left <= right."""
        return self.create_node(node_type=op.BV_ULE,
                                args=(left, right))

    def BVUGE(self, left, right):
        """Returns the formula left >= right."""
        return self.create_node(node_type=op.BV_ULE,
                                args=(right, left))

    def BVNeg(self, formula):
        """Returns the arithmetic negation of the BV."""
        return self.create_node(node_type=op.BV_NEG,
                                args=(formula,),
                                payload=(formula.bv_width(),))

    def BVAdd(self, left, right):
        """Returns the sum of two BV."""
        return self.create_node(node_type=op.BV_ADD,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVSub(self, left, right):
        """Returns the difference of two BV."""
        return self.create_node(node_type=op.BV_SUB,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVMul(self, left, right):
        """Returns the product of two BV."""
        return self.create_node(node_type=op.BV_MUL,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVUDiv(self, left, right):
        """Returns the division of the two BV."""
        return self.create_node(node_type=op.BV_UDIV,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVURem(self, left, right):
        """Returns the reminder of the two BV."""
        return self.create_node(node_type=op.BV_UREM,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVLShl(self, left, right):
        """Returns the logical left shift the BV."""
        if is_python_integer(right):
            right = self.BV(right, left.bv_width())
        return self.create_node(node_type=op.BV_LSHL,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVLShr(self, left, right):
        """Returns the logical right shift the BV."""
        if is_python_integer(right):
            right = self.BV(right, left.bv_width())
        return self.create_node(node_type=op.BV_LSHR,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVRol(self, formula, steps):
        """Returns the LEFT rotation of the BV by the number of steps."""
        if not is_python_integer(steps):
            raise PysmtTypeError("BVRol: 'steps' should be an integer. Got %s" \
                                 % steps)
        return self.create_node(node_type=op.BV_ROL,
                                args=(formula,),
                                payload=(formula.bv_width(), steps))

    def BVRor(self, formula, steps):
        """Returns the RIGHT rotation of the BV by the number of steps."""
        if not is_python_integer(steps):
            raise PysmtTypeError("BVRor: 'steps' should be an integer. Got %s" \
                                 % steps)
        return self.create_node(node_type=op.BV_ROR,
                                args=(formula,),
                                payload=(formula.bv_width(), steps))

    def BVZExt(self, formula, increase):
        """Returns the extension of the BV with 'increase' additional bits

        New bits are set to zero.
        """
        if not is_python_integer(increase):
            raise PysmtTypeError("BVZext: 'increase' should be an integer. "
                                 "Got %s" % increase)
        return self.create_node(node_type=op.BV_ZEXT,
                                args=(formula,),
                                payload=(formula.bv_width()+increase,
                                         increase))

    def BVSExt(self, formula, increase):
        """Returns the signed extension of the BV with 'increase' additional bits

        New bits are set according to the most-significant-bit.
        """
        if not is_python_integer(increase):
            raise PysmtTypeError("BVSext: 'increase' should be an integer. "
                                 "Got %s" % increase)
        return self.create_node(node_type=op.BV_SEXT,
                                args=(formula,),
                                payload=(formula.bv_width()+increase,
                                         increase))

    def BVSLT(self, left, right):
        """Returns the SIGNED LOWER-THAN comparison for BV."""
        return self.create_node(node_type=op.BV_SLT,
                                args=(left, right))

    def BVSLE(self, left, right):
        """Returns the SIGNED LOWER-THAN-OR-EQUAL-TO comparison for BV."""
        return self.create_node(node_type=op.BV_SLE,
                                args=(left, right))

    def BVComp(self, left, right):
        """Returns a BV of size 1 equal to 0 if left is equal to right,
        otherwise 1 is returned."""
        return self.create_node(node_type=op.BV_COMP,
                                args=(left, right),
                                payload=(1,))

    def BVSDiv(self, left, right):
        """Returns the SIGNED DIVISION of left by right"""
        return self.create_node(node_type=op.BV_SDIV,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVSRem(self, left, right):
        """Returns the SIGNED REMAINDER of left divided by right"""
        return self.create_node(node_type=op.BV_SREM,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVAShr(self, left, right):
        """Returns the RIGHT arithmetic rotation of the left BV by the number
        of steps specified by the right BV."""
        if is_python_integer(right):
            right = self.BV(right, left.bv_width())
        return self.create_node(node_type=op.BV_ASHR,
                                args=(left, right),
                                payload=(left.bv_width(),))

    def BVNand(self, left, right):
        """Returns the NAND composition of left and right."""
        return self.BVNot(self.BVAnd(left, right))

    def BVNor(self, left, right):
        """Returns the NOR composition of left and right."""
        return self.BVNot(self.BVOr(left, right))

    def BVXnor(self, left, right):
        """Returns the XNOR composition of left and right."""
        return self.BVOr(self.BVAnd(left, self.BVNot(right)),
                         self.BVAnd(self.BVNot(left), right))

    def BVSGT(self, left, right):
        """Returns the SIGNED GREATER-THAN comparison for BV."""
        return self.BVSLT(right, left)

    def BVSGE(self, left, right):
        """Returns the SIGNED GREATER-THAN-OR-EQUAL-TO comparison for BV."""
        return self.BVSLE(right, left)

    def BVSMod(self, left, right):
        """Returns the SIGNED MODULUS of left divided by right."""
        # According to SMT-LIB standard (2015-06-23) BVSMod is defined as follows
        # http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV
        #
        # For all terms s,t of sort (_ BitVec m), where 0 < m,
        # (bvsmod s t) abbreviates
        # (let ((?msb_s ((_ extract |m-1| |m-1|) s))
        #       (?msb_t ((_ extract |m-1| |m-1|) t)))
        #   (let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
        #         (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
        #     (let ((u (bvurem abs_s abs_t)))
        #       (ite (= u (_ bv0 m))
        #            u
        #       (ite (and (= ?msb_s #b0) (= ?msb_t #b0))
        #            u
        #       (ite (and (= ?msb_s #b1) (= ?msb_t #b0))
        #            (bvadd (bvneg u) t)
        #       (ite (and (= ?msb_s #b0) (= ?msb_t #b1))
        #            (bvadd u t)
        #            (bvneg u))))))))
        m = left.bv_width()
        s = left
        t = right
        zero_1 = self.BV("#b0")
        one_1 = self.BV("#b1")

        msb_s = self.BVExtract(s, m-1, m-1)
        msb_t = self.BVExtract(t, m-1, m-1)
        abs_s = self.Ite(self.Equals(msb_s, zero_1), s, self.BVNeg(s))
        abs_t = self.Ite(self.Equals(msb_t, zero_1), t, self.BVNeg(t))
        u = self.BVURem(abs_s, abs_t)

        cond1 = self.Equals(u, self.BV(0, m))
        cond2 = self.And(self.Equals(msb_s, zero_1), self.Equals(msb_t, zero_1))
        cond3 = self.And(self.Equals(msb_s, one_1), self.Equals(msb_t, zero_1))
        cond4 = self.And(self.Equals(msb_s, zero_1), self.Equals(msb_t, one_1))

        case3 = self.BVAdd(self.BVNeg(u), t)
        case4 = self.BVAdd(u, t)
        case5 = self.BVNeg(u)

        return self.Ite(self.Or(cond1, cond2), u,
                        self.Ite(cond3, case3, self.Ite(cond4, case4, case5)))

    def BVRepeat(self, formula, count=1):
        """Returns the concatenation of count copies of formula."""
        res = formula
        for _ in range(count-1):
            res = self.BVConcat(res, formula)
        return res

    def StrLength(self, formula):
        """Returns the length of a formula resulting a String"""
        return self.create_node(node_type=op.STR_LENGTH, args=(formula,))

    def StrConcat(self, *args):
        """Returns the concatenation of n Strings.

        s1, s2, ..., and sn are String terms.
        String concatenation takes at least 2 arguments.
        """
        tuple_args = self._polymorph_args_to_tuple(args)
        if len(tuple_args) <= 1:
            raise TypeError("Cannot create a Str_Concat without arguments.")
        return self.create_node(node_type=op.STR_CONCAT, args=tuple_args)

    def StrContains(self, s, t):
        """Returns wether the String s contains the String t.

        s and t are String terms.
        """
        return self.create_node(node_type=op.STR_CONTAINS, args=(s, t))

    def StrIndexOf(self, s, t, i):
        """Returns the position of the first occurrence of t in s after the index i.

        s and t being a non empty strings and i a non-negative integer.
        It returns -1 if the value to search for never occurs.
        """
        return self.create_node(node_type=op.STR_INDEXOF, args=(s, t, i))

    def StrReplace(self, s, t1, t2):
        """Returns a new string where the first occurrence of t1 is replace by t2.

        where s, t1 and t2 are string terms, t1 is non-empty.
        """
        return self.create_node(node_type=op.STR_REPLACE, args=(s, t1, t2))

    def StrSubstr(self, s, i, j):
        """Returns a substring of s starting at i and ending at j+i.

        where s is a string term and i, j are integer terms.
        """
        return self.create_node(node_type=op.STR_SUBSTR, args=(s, i, j))

    def StrPrefixOf(self, s, t):
        """Returns whether the s is a prefix of the string t.

        where s and t are string terms.
        """
        return self.create_node(node_type=op.STR_PREFIXOF, args=(s, t))

    def StrSuffixOf(self, s, t):
        """Returns whether the string s is a suffix of the string t.

        where s and t are string terms.
        """
        return self.create_node(node_type=op.STR_SUFFIXOF, args=(s, t))

    def StrToInt(self, s):
        """Returns the corresponding natural number of s.

        If s does not represent a natural number, it returns -1.
        """
        return self.create_node(node_type=op.STR_TO_INT, args=(s,))

    def IntToStr(self, x):
        """Returns the corresponding String representing the natural number x.

        where x is an integer term. If x is not a natural number it
        returns the empty String.
        """
        return self.create_node(node_type=op.INT_TO_STR, args=(x, ))

    def StrCharAt(self, s, i):
        """Returns a single character String at position i.

        s is a string term and i is an integer term. i is the position.
        """
        return self.create_node(node_type=op.STR_CHARAT, args=(s, i))

    def BVToNatural(self, formula):
        """Returns the Natural number represented by the BitVector.

        Given a BitVector of width m returns an integer between 0 and 2^m-1
        """
        return self.create_node(node_type=op.BV_TONATURAL, args=(formula,))

    def Select(self, arr, idx):
        """Creates a node representing an array selection."""
        return self.create_node(node_type=op.ARRAY_SELECT, args=(arr, idx))

    def Store(self, arr, idx, val):
        """Creates a node representing an array update."""
        return self.create_node(node_type=op.ARRAY_STORE, args=(arr, idx, val))

    def Array(self, idx_type, default, assigned_values=None):
        """Creates a node representing an array having index type equal to
           idx_type, initialized with default values.

           If assigned_values is specified, then it must be a map from
           constants of type idx_type to values of the same type as
           default and the array is initialized correspondingly.
        """
        if not isinstance(idx_type, types.PySMTType):
            raise PysmtTypeError("idx_type is not a valid type: '%s'" % idx_type)

        args = [default]
        if assigned_values:
            for k in sorted(assigned_values, key=id):
                if not k.is_constant():
                    raise PysmtValueError("Array initialization indexes must "
                                          "be constants")
                # It is useless to represent assignments equal to the default
                if assigned_values[k] != default:
                    args.append(k)
                    args.append(assigned_values[k])
        return self.create_node(node_type=op.ARRAY_VALUE, args=tuple(args),
                                payload=idx_type)

    def _Algebraic(self, val):
        """Returns the algebraic number val."""
        return self.create_node(node_type=op.ALGEBRAIC_CONSTANT,
                                args=tuple(),
                                payload=val)

    #
    # Helper functions
    #
    def normalize(self, formula):
        """Returns the formula normalized to the current Formula Manager.

        This method is useful to contextualize a formula coming from another
        formula manager.

        E.g., f_a is defined with the FormulaManager a, and we want to
              obtain f_b that is the formula f_a expressed on the
              FormulaManager b : f_b = b.normalize(f_a)
        """
        normalizer = FormulaContextualizer(self.env)
        return normalizer.walk(formula)

    def _polymorph_args_to_tuple(self, args):
        """ Helper function to return a tuple of arguments from args.

        This function is used to allow N-ary operators to express their arguments
        both as a list of arguments or as a tuple of arguments: e.g.,
           And([a,b,c]) and And(a,b,c)
        are both valid, and they are converted into a tuple (a,b,c) """

        if len(args) == 1 and isinstance(args[0], Iterable):
            args = args[0]
        return tuple(args)

    def __contains__(self, node):
        """Checks whether the given node belongs to this formula manager.

        This overloads the 'in' operator, making it possible to write:

           E.g., if x in formula_manager: ...
        """
        if node._content in self.formulae:
            return self.formulae[node._content] == node
        else:
            return False

#EOC FormulaManager


class FormulaContextualizer(IdentityDagWalker):
    """Helper class to recreate a formula within a new environment."""

    def __init__(self, env=None):
        IdentityDagWalker.__init__(self, env=env)
        self.type_normalize = self.env.type_manager.normalize

    def walk_symbol(self, formula, args, **kwargs):
        # Recreate the Symbol taking into account the type information
        ty = formula.symbol_type()
        newty = self.type_normalize(ty)
        return self.mgr.Symbol(formula.symbol_name(), newty)

    def walk_array_value(self, formula, args, **kwargs):
        # Recreate the ArrayValue taking into account the type information
        assign = dict(zip(args[1::2], args[2::2]))
        ty = self.type_normalize(formula.array_value_index_type())
        return self.mgr.Array(ty, args[0], assign)

    def walk_function(self, formula, args, **kwargs):
        # We re-create the symbol name
        old_name = formula.function_name()
        new_name = self.walk_symbol(old_name, None)
        return self.mgr.Function(new_name, args)
