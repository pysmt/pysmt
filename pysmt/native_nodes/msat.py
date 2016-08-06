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


import pysmt.shortcuts
import pysmt.formula
from pysmt.operators import QUANTIFIERS, CONSTANTS
from pysmt.operators import (FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF,
                             SYMBOL, FUNCTION,
                             REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT,
                             PLUS, MINUS, TIMES,
                             LE, LT, EQUALS,
                             ITE,
                             TOREAL)
from pysmt.typing import BOOL, REAL, INT, PYSMT_TYPES
import pysmt.solvers.msat


def msat_type_to_type(msat_env, mt):
    if mathsat.msat_is_bool_type(msat_env, mt):
        return BOOL
    elif mathsat.msat_is_rational_type(msat_env, mt):
        return REAL
    elif mathsat.msat_is_integer_type(msat_env, mt):
        return INT
    else:
        raise NotImplementedError


def term_to_node_type(term, manager):
    if mathsat.msat_term_is_true(manager.msat_env, term):
        return BOOL_CONSTANT
    if mathsat.msat_term_is_false(manager.msat_env, term):
        return BOOL_CONSTANT
    if mathsat.msat_term_is_boolean_constant(manager.msat_env, term):
        return SYMBOL
    if mathsat.msat_term_is_number(manager.msat_env, term):
        return REAL_CONSTANT
    if mathsat.msat_term_is_and(manager.msat_env, term):
        return AND
    if mathsat.msat_term_is_or(manager.msat_env, term):
        return OR
    if mathsat.msat_term_is_not(manager.msat_env, term):
        return NOT
    if mathsat.msat_term_is_iff(manager.msat_env, term):
        return IFF
    if mathsat.msat_term_is_term_ite(manager.msat_env, term):
        return ITE
    if mathsat.msat_term_is_constant(manager.msat_env, term):
        return SYMBOL
    if mathsat.msat_term_is_uf(manager.msat_env, term):
        return FUNCTION
    if mathsat.msat_term_is_equal(manager.msat_env, term):
        return EQUALS
    if mathsat.msat_term_is_leq(manager.msat_env, term):
        return LE
    if mathsat.msat_term_is_plus(manager.msat_env, term):
        return PLUS
    if mathsat.msat_term_is_times(manager.msat_env, term):
        return TIMES
    raise NotImplementedError



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

    def __init__(self, manager, msat_term):
        self.manager = manager
        self._content = msat_term
        self._dependencies = None
        self._sons = None
        return

    def __eq__(self, other):
        return isinstance(other, MsatFNode) and \
            self._content == other._content and \
            self.manager == other.manager

    def __hash__(self):
        return hash(self._content)

    def node_type(self):
        return term_to_node_type(self._content, self.manager)

    def args(self):
        if self._sons is None:
            self._sons = [MsatFNode(self.manager, mathsat.msat_term_get_arg(self._content, i))
                          for i in xrange(mathsat.msat_term_arity(self._content))]
        return self._sons

    def arg(self, idx):
        return MsatFNode(self.manager, mathsat.msat_term_get_arg(self._content, idx))


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
        return pysmt.shortcuts.substitute(self, subs=subs)

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
        if type(self._content) == tuple:
            return self._content[2]
        msat_type = mathsat.msat_term_get_type(self._content)
        return msat_type_to_type(self.manager.msat_env, msat_type)

    def symbol_name(self):
        if type(self._content) == tuple:
            return self._content[1]
        decl = mathsat.msat_term_get_decl(self._content)
        return mathsat.msat_decl_get_name(decl)

    def constant_value(self):
        if self.is_bool_constant():
            if mathsat.msat_term_is_true(self.manager.msat_env, self._content):
                return True
            return False
        else:
            # it is a number
            rep = mathsat.msat_term_repr(self._content)
            match = re.match(r"(-?\d+)/(\d+)", rep)
            assert match is not None
            return Fraction((int(match.group(1)), int(match.group(2))))


    def function_name(self):
        decl = mathsat.msat_term_get_decl(self._content)
        return self.manager.function_name(decl)

    def quantifier_vars(self):
        raise NotImplementedError

    # Infix Notation
    def _apply_infix(self, right, function):
        if pysmt.shortcuts.get_env().enable_infix_notation:
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

    def __sub__(self, right):
        return self._apply_infix(right, pysmt.shortcuts.Minus)

    def __mul__(self, right):
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
        return self._apply_infix(right, pysmt.shortcuts.GE)

# EOC FNode


class MsatFormulaManager(pysmt.formula.FormulaManager):
    """FormulaManager is responsible for the creation of all formulae."""

    def __init__(self, env=None, msat_env=None):
        if env is None:
            env = pysmt.shortcuts.get_env()
        self.env = env
        if msat_env is None:
            config = mathsat.msat_create_config()
            check = mathsat.msat_set_option(config, "model_generation", "true")
            assert check == 0
            msat_env = mathsat.msat_create_env(config)
        self.msat_env = msat_env

        pysmt.formula.FormulaManager.__init__(self, env)

        self._converter = None
        self.declarations = {}
        self.rdeclarations = {}
        return

    def converter(self):
        if self._converter is None:
            self._converter = pysmt.solvers.msat.MSatConverter(self.env,
                                                               self.msat_env)
        return self._converter

    def function_name(self, declaration):
        declid = mathsat.msat_decl_id(declaration)
        return self.rdeclarations[declid]


    def create_node(self, node_type, args, payload=None):
        term = None

        print("creating", node_type, payload)
        # MG: Isn't this part of code already implemented by the Converter?
        #     why can't we reuse that?
        if node_type == SYMBOL:
            name, typename = payload
            if name not in self.declarations:
                msat_type = self.converter().type_to_msat(typename)
                decl = mathsat.msat_declare_function(self.msat_env,
                                                     name,
                                                     msat_type)
                self.declarations[name] = decl
                declid = mathsat.msat_decl_id(decl)
                self.rdeclarations[declid] = name
            decl = self.declarations[name]
            if typename.is_function_type():
                content = pysmt.fnode.FNodeContent(SYMBOL, args, payload)
                if content in self.formulae:
                    return self.formulae[content]
                else:
                    res = pysmt.fnode.FNode(content)
                    self.formulae[content] = res
                    return res
            else:
                term = mathsat.msat_make_constant(self.msat_env, decl)

        elif node_type == REAL_CONSTANT:
            n,d = payload.numerator, payload.denominator
            rep = str(n) + "/" + str(d)
            term =  mathsat.msat_make_number(self.msat_env, rep)

        elif node_type == INT_CONSTANT:
            rep = str(payload)
            term =  mathsat.msat_make_number(self.msat_env, rep)

        elif node_type == BOOL_CONSTANT:
            if payload:
                term = mathsat.msat_make_true(self.msat_env)
            else:
                term = mathsat.msat_make_false(self.msat_env)

        elif node_type == FUNCTION:
            name = payload.symbol_name()
            typename = payload.symbol_type()
            if name not in self.declarations:
                msat_type = self.converter().type_to_msat(typename)
                decl = mathsat.msat_declare_function(self.msat_env,
                                                     name,
                                                     msat_type)
                self.declarations[name] = decl
                declid = mathsat.msat_decl_id(decl)
                self.rdeclarations[declid] = name
            decl = self.declarations[name]
            term = mathsat.msat_make_uf(self.msat_env, decl, [a._content for a in args])

        elif node_type == IFF:
            assert len(args) == 2
            term = mathsat.msat_make_iff(self.msat_env, args[0]._content, args[1]._content)

        elif node_type == IMPLIES:
            assert len(args) == 2
            term = mathsat.msat_make_or(self.msat_env,
                                        mathsat.msat_make_not(self.msat_env, args[0]._content),
                                        args[1]._content)

        else:
            fun = self.converter().functions[node_type]
            term = fun(None, [a._content for a in args])

        if mathsat.MSAT_ERROR_TERM(term):
            raise TypeError()

        return MsatFNode(self, term)


    def __contains__(self, node):
        """Checks whether the given node belongs to this formula manager.

        This overloads the 'in' operator, making it possible to write:

           E.g., if x in formula_manager: ...
        """
        if isinstance(node, MsatFNode):
            return node.manager == self

        if node._content in self.formulae:
            return self.formulae[node._content] == node
        else:
            return False

#EOC FormulaManager
