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
 * QuantifierOracle says whether a formula is quantifier free
 * The functions assert_*_args are useful for testing the type of
   arguments of a given function.
"""

import pysmt.walkers as walkers
import pysmt.operators as op
import pysmt.shortcuts

from pysmt.typing import BOOL, REAL, INT

class SimpleTypeChecker(walkers.DagWalker):

    def __init__(self, env=None):
        walkers.DagWalker.__init__(self, env=env)

        self.functions[op.AND] = self.walk_bool_to_bool
        self.functions[op.OR] = self.walk_bool_to_bool
        self.functions[op.NOT] = self.walk_bool_to_bool
        self.functions[op.IMPLIES] = self.walk_bool_to_bool
        self.functions[op.IFF] = self.walk_bool_to_bool
        self.functions[op.SYMBOL] = self.walk_symbol
        self.functions[op.EQUALS] = self.walk_math_relation
        self.functions[op.LE] = self.walk_math_relation
        self.functions[op.LT] = self.walk_math_relation
        self.functions[op.REAL_CONSTANT] = self.walk_identity_real
        self.functions[op.BOOL_CONSTANT] = self.walk_identity_bool
        self.functions[op.INT_CONSTANT] = self.walk_identity_int
        self.functions[op.FORALL] = self.walk_quantifier
        self.functions[op.EXISTS] = self.walk_quantifier
        self.functions[op.PLUS] = self.walk_realint_to_realint
        self.functions[op.MINUS] = self.walk_realint_to_realint
        self.functions[op.TIMES] = self.walk_realint_to_realint
        self.functions[op.ITE] = self.walk_ite
        self.functions[op.TOREAL] = self.walk_int_to_real
        self.functions[op.FUNCTION] = self.walk_function

        assert self.is_complete(verbose=True)

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
        if any((x is None or x != type_in) for x in args):
            return None
        return type_out

    def walk_bool_to_bool(self, formula, args):
        return self.walk_type_to_type(formula, args, BOOL, BOOL)

    def walk_real_to_bool(self, formula, args):
        return self.walk_type_to_type(formula, args, REAL, BOOL)

    def walk_int_to_real(self, formula, args):
        return self.walk_type_to_type(formula, args, INT, REAL)

    def walk_real_to_real(self, formula, args):
        return self.walk_type_to_type(formula, args, REAL, REAL)

    def walk_realint_to_realint(self, formula, args):
        rval = self.walk_type_to_type(formula, args, REAL, REAL)
        if rval is None:
            rval = self.walk_type_to_type(formula, args, INT, INT)
        return rval

    def walk_math_relation(self, formula, args):
        rval = self.walk_type_to_type(formula, args, REAL, BOOL)
        if rval is None:
            rval = self.walk_type_to_type(formula, args, INT, BOOL)
        return rval

    def walk_ite(self, formula, args):
        assert formula is not None
        if None in args: return None
        if (args[0] == BOOL and args[1]==args[2]):
            return args[1]
        return None

    def walk_identity_bool(self, formula, args):
        assert formula is not None
        assert len(args) == 0
        return BOOL

    def walk_identity_real(self, formula, args):
        assert formula is not None
        assert len(args) == 0
        return REAL

    def walk_identity_int(self, formula, args):
        assert formula is not None
        assert len(args) == 0
        return INT

    def walk_symbol(self, formula, args):
        assert formula is not None
        assert len(args) == 0
        return formula.symbol_type()

    def walk_quantifier(self, formula, args):
        assert formula is not None
        assert len(args) == 1
        if args[0] == BOOL:
            return BOOL
        return None

    def walk_function(self, formula, args):
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

# EOC SimpleTypeChecker


class QuantifierOracle(walkers.DagWalker):
    def __init__(self, env=None):
        walkers.DagWalker.__init__(self, env=env)

        # Clear the mapping function
        self.functions.clear()

        # Propagate truth value, and force False when a Quantifier
        # is found.
        for elem in op.ALL_TYPES:
            if elem in [op.FORALL, op.EXISTS]:
                self.functions[elem] = self.walk_false
            else:
                self.functions[elem] = self.walk_all

        # Check that no operator in undefined
        assert self.is_complete(verbose=True)

    def is_qf(self, formula):
        """ Returns whether formula is Quantifier Free. """
        return self.walk(formula)


# EOC QuantifierOracle


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
