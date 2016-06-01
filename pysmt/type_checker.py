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
"""This module provides basic services to perform type checking and
reasoning about the type of formulae.

 * SimpleTypeChecker provides the pysmt.typing type of a formula
 * The functions assert_*_args are useful for testing the type of
   arguments of a given function.
"""
from six.moves import xrange

import pysmt.walkers as walkers
import pysmt.operators as op
import pysmt.shortcuts

from pysmt.typing import BOOL, REAL, INT, BVType, STRING


class SimpleTypeChecker(walkers.DagWalker):

    def __init__(self, env=None):
        walkers.DagWalker.__init__(self, env=env)

        self.set_function(self.walk_bool_to_bool, op.AND, op.OR, op.NOT,
                          op.IMPLIES, op.IFF)
        self.set_function(self.walk_symbol, op.SYMBOL)
        self.set_function(self.walk_math_relation, op.EQUALS, op.LE, op.LT)
        self.set_function(self.walk_identity_real, op.REAL_CONSTANT)
        self.set_function(self.walk_identity_bool, op.BOOL_CONSTANT)
        self.set_function(self.walk_identity_int, op.INT_CONSTANT)
        self.set_function(self.walk_quantifier, op.FORALL, op.EXISTS)
        self.set_function(self.walk_realint_to_realint, op.PLUS, op.MINUS,
                          op.TIMES)
        self.set_function(self.walk_ite, op.ITE)
        self.set_function(self.walk_int_to_real, op.TOREAL)
        self.set_function(self.walk_function, op.FUNCTION)

        self.set_function(self.walk_identity_bv, op.BV_CONSTANT)
        self.set_function(self.walk_bv_to_bool, op.BV_ULT, op.BV_ULE, op.BV_SLT,
                          op.BV_SLE)
        self.set_function(self.walk_bv_to_bv, op.BV_ADD, op.BV_SUB, op.BV_NOT,
                          op.BV_AND, op.BV_OR, op.BV_XOR, op.BV_NEG, op.BV_MUL,
                          op.BV_UDIV, op.BV_UREM, op.BV_LSHL, op.BV_LSHR,
                          op.BV_SDIV, op.BV_SREM, op.BV_ASHR)
        self.set_function(self.walk_bv_rotate, op.BV_ROL, op.BV_ROR)
        self.set_function(self.walk_bv_extend, op.BV_ZEXT, op.BV_SEXT)
        self.set_function(self.walk_bv_comp, op.BV_COMP)
        
        self.set_function(self.walk_identity_string, op.STRING_CONSTANT)
        
        self.be_nice = False

    def _get_key(self, formula, **kwargs):
        return formula

    def get_type(self, formula):
        """ Returns the pysmt.types type of the formula """
        res = self.walk(formula)
        if not self.be_nice and  res is None:
            raise TypeError("The formula '%s' is not well-formed" % str(formula))
        return res

    def walk_type_to_type(self, formula, args, type_in, type_out):
        assert formula is not None
        for x in args:
            if x is None or x != type_in:
                return None
        return type_out

    def walk_bool_to_bool(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, BOOL, BOOL)

    def walk_real_to_bool(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, REAL, BOOL)

    def walk_int_to_real(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, INT, REAL)

    def walk_real_to_real(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, REAL, REAL)

    def walk_realint_to_realint(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        rval = self.walk_type_to_type(formula, args, REAL, REAL)
        if rval is None:
            rval = self.walk_type_to_type(formula, args, INT, INT)
        return rval

    def walk_bv_to_bv(self, formula, args, **kwargs):
        #pylint: disable=unused-argument

        # We check that all children are BV and the same size
        target_bv_type = BVType(formula.bv_width())
        for a in args:
            if not a == target_bv_type:
                return None
        return target_bv_type

    def walk_bv_comp(self, formula, args, **kwargs):
        # We check that all children are BV and the same size
        a,b = args
        if a != b or (not a.is_bv_type()):
            return None
        return BVType(1)

    def walk_bv_to_bool(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        width = args[0].width
        for a in args[1:]:
            if (not a.is_bv_type()) or width != a.width:
                return None
        return BOOL

    def walk_bv_concat(self, formula, args, **kwargs):
        # Width of BV operators are computed at construction time.
        # The type-checker only verifies that they are indeed
        # correct.
        try:
            l_width = args[0].width
            r_width = args[1].width
            target_width = formula.bv_width()
        except AttributeError:
            return None
        if not l_width + r_width == target_width:
            return None
        return BVType(target_width)

    def walk_bv_extract(self, formula, args, **kwargs):
        arg = args[0]
        if not arg.is_bv_type():
            return None
        base_width = arg.width
        target_width = formula.bv_width()
        start = formula.bv_extract_start()
        end = formula.bv_extract_end()
        if start >= base_width or end >= base_width:
            return None
        if base_width < target_width:
            return None
        if target_width != (end-start+1):
            return None
        return BVType(target_width)

    def walk_bv_rotate(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        target_width = formula.bv_width()
        if target_width < formula.bv_rotation_step() or target_width < 0:
            return None
        if target_width != args[0].width:
            return None
        return BVType(target_width)

    def walk_bv_extend(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        target_width = formula.bv_width()
        if target_width < args[0].width or target_width < 0:
            return None
        return BVType(target_width)

    def walk_math_relation(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if args[0].is_real_type():
            return self.walk_type_to_type(formula, args, REAL, BOOL)
        if args[0].is_int_type():
            return self.walk_type_to_type(formula, args, INT, BOOL)
        if args[0].is_bv_type():
            return self.walk_bv_to_bool(formula, args)
        if args[0].is_string_type():
            return self.walk_type_to_type(formula, args, STRING, BOOL)
        return None

    def walk_ite(self, formula, args, **kwargs):
        assert formula is not None
        if None in args: return None
        if (args[0] == BOOL and args[1]==args[2]):
            return args[1]
        return None

    def walk_identity_bool(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return BOOL

    def walk_identity_real(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return REAL

    def walk_identity_int(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return INT

    def walk_identity_string(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return STRING

    def walk_identity_bv(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return BVType(formula.bv_width())

    def walk_symbol(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 0
        return formula.symbol_type()

    def walk_quantifier(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 1
        if args[0] == BOOL:
            return BOOL
        return None

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()
        assert name.is_symbol()
        tp = name.symbol_type()
        assert tp.is_function_type()

        if len(args) != len(tp.param_types):
            return None

        for i in xrange(len(args)):
            if args[i] != tp.param_types[i]:
                return None

        return tp.return_type

    def walk_str_length(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 1
        assert args[0] == STRING
        return  INT
    
    def walk_str_concat(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) > 1
        for a in args:
            if (not a.is_string_type()):
                return None
        return STRING
        
    def walk_str_contains(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 2
        assert args[0].is_string_type() and args[1].is_string_type()
        return BOOL
    
    def walk_str_indexof(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 3
        assert args[0].is_string_type() and args[1].is_string_type() and args[2].is_int_type()
        return INT
    
    def walk_str_replace(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 3
        assert args[0].is_string_type() and args[1].is_string_type() and args[2].is_string_type()
        return STRING
        
    def walk_str_substr(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 3
        assert args[0].is_string_type() and args[1].is_int_type() and args[2].is_int_type()
        return STRING
        
    def walk_str_prefixof(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 2
        assert args[0].is_string_type() and args[1].is_string_type()
        return BOOL
    
    def walk_str_suffixof(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 2
        assert args[0].is_string_type() and args[1].is_string_type()
        return BOOL
    
    def walk_str_to_int(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 1
        assert args[0].is_string_type()
        return INT
    
    def walk_int_to_str(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 1
        assert args[0].is_int_type()
        return STRING
    
    def walk_str_to_unit16(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 1
        assert args[0].is_string_type()
        return INT
    
    def walk_uint16_to_str(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 1
        assert args[0].is_int_type()
        return STRING
    
    def walk_str_to_uint32(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 1
        assert args[0].is_string_type()
        return INT
    
    def walk_uint32_to_str(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 1
        assert args[0].is_int_type()
        return STRING
    
    def walk_str_charat(self, formula, args, **kwargs):
        assert formula is not None
        assert len(args) == 2
        assert args[0].is_string_type() and args[1].is_int_type()
        return STRING
        
# EOC SimpleTypeChecker


def assert_no_boolean_in_args(args):
    """ Enforces that the elements in args are not of BOOL type."""
    get_type = pysmt.shortcuts.get_type
    for arg in args:
        if (get_type(arg) == BOOL):
            raise TypeError("Boolean Expressions are not allowed in arguments")


def assert_boolean_args(args):
    """ Enforces that the elements in args are of BOOL type. """
    get_type = pysmt.shortcuts.get_type
    for arg in args:
        t = get_type(arg)
        if (t != BOOL):
            raise TypeError("%s is not allowed in arguments" % t)


def assert_same_type_args(args):
    """ Enforces that all elements in args have the same type. """
    get_type = pysmt.shortcuts.get_type
    ref_t = get_type(args[0])
    for arg in args[1:]:
        t = get_type(arg)
        if (t != ref_t):
            raise TypeError("Arguments should be of the same type!\n" +
                             str([str((a, get_type(a))) for a in args]))


def assert_args_type_in(args, allowed_types):
    """ Enforces that the type of the arguments is an allowed type """
    get_type = pysmt.shortcuts.get_type
    for arg in args:
        t = get_type(arg)
        if (t not in allowed_types):
            raise TypeError(
                "Argument is of type %s, but one of %s was expected!\n" %
                (t, str(allowed_types)))
