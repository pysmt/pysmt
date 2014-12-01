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
from fractions import Fraction

import pysmt.operators as op
from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.typing import REAL, INT, BOOL, PySMTType

class GenericNumber(object):
    """
    Temporary repaces a Real or Int constant in a type unsafe
    environment to represent an unknown "Real or int" value.
    """

    def __init__(self, number):
        """
        Creates a GenericNumber representing the given number.
        number MUST be a python integer.
        """
        self.value = number

    def as_real(self, mgr):
        return mgr.Real(Fraction(self.value, 1))

    def as_int(self, mgr):
        return mgr.Int(self.value)

    def get_sons(self):
        return []

    def is_constant(self, _type=None, value=None):
        if value:
            return self.value == value
        return True

    def constant_value(self):
        return self.value

    def is_real_constant(self):
        return True

    def is_int_constant(self):
        return True




def disambiguate(tu_env, formula,
                 create_toreal_on_demand=False,
                 fix_equals=False):
    """
    Takes a formula defined over the given type unsafe environment
    (tu_env) and replaces all the occurrencies of GenericNumber to
    proper instances of Real() or Int() resolving the types
    accordingly.

    If create_toreal_on_demand is set to true, the function is allowed
    to introduce ToReal nodes to create a well typed formula (If it is
    set to false, a TypeError will be raised)

    If fix_equals is true, the function transforms an equal between
    booleans in an Iff.

    """
    disambiguator = \
        NumberDisambiguator(tu_env,
                            create_toreal_on_demand=create_toreal_on_demand,
                            fix_equals=fix_equals)
    return disambiguator.disambiguate(formula)



class NumberDisambiguator(object):

    class GenericType(PySMTType):
        def __str__(self):
            return "Generic"


    GENERIC = GenericType()

    def __init__(self, env, create_toreal_on_demand=False, fix_equals=False):
        self.env = env
        self.mgr = self.env.formula_manager
        self.memoization = {}
        self.ft_memoization = {}
        self.ot_memoization = {}
        self.create_toreal_on_demand = create_toreal_on_demand
        self.identity = IdentityDagWalker(env, invalidate_memoization=True)
        if fix_equals:
            self.identity.functions[op.EQUALS] = self._equals_or_iff

    def _equals_or_iff(self, formula, args):
        assert len(args) == 2
        left, right = args
        lty = self.env.stc.get_type(left)
        if lty == BOOL:
            return self.mgr.Iff(left, right)
        else:
            return self.mgr.Equals(left, right)


    def is_generic_number(self, f):
        return isinstance(f, GenericNumber)


    def get_operator_type(self, expr):
        """
        Given a expr, this function returns its most specific return
        type. E.g. Plus(Real(1), GenericNumber(3)) yields REAL as a
        result
        """
        if expr in self.ot_memoization:
            return self.ot_memoization[expr]

        res = None
        if self.is_generic_number(expr):
            res = NumberDisambiguator.GENERIC
        elif expr.is_symbol():
            res = expr.symbol_type()
        elif expr.is_real_constant():
            res = REAL
        elif expr.is_int_constant():
            res = INT
        elif expr.is_toreal():
            res = REAL

        elif expr.is_ite():
            res = self.get_most_specific_type([self.get_operator_type(expr.arg(1)),
                                               self.get_operator_type(expr.arg(2))])
        elif expr.is_function_application():
            fun = expr.function_name()
            funty = fun.symbol_type()
            res = funty.return_type
        elif expr.is_boolean_operator() or expr.is_literal() or \
             expr.is_bool_constant() or expr.is_quantifier():
            res = BOOL
        elif expr.is_le() or expr.is_lt() or expr.is_equals():
            res = BOOL
        elif expr.is_plus():
            res = self.get_most_specific_type([self.get_operator_type(o)
                                               for o in expr.args()])
        elif expr.is_times() or expr.is_minus():
            res = self.get_most_specific_type([self.get_operator_type(expr.arg(0)),
                                               self.get_operator_type(expr.arg(1))])
        else:
            raise NotImplementedError("Unexpected expr encountered: " + \
                                      str(expr))

        if res is None:
            raise TypeError("The formula is not well typed")
        self.ot_memoization[expr] = res
        return res

    def get_most_specific_type(self, types):
        """
        Given a list of types, it returns the most specific among
        them. If two concrete types are found, the function returns
        None.

        E.g.
        [REAl, GENERIC, REAL] -> REAL;
        [REAL, GENERIC, INT] -> None
        [GENERIC, GENERIC] -> GENERIC
        """
        if len(types) == 0:
            return None

        res = types[0]
        for x in types[1:]:
            if res == NumberDisambiguator.GENERIC:
                res = x
            elif res != x and x != NumberDisambiguator.GENERIC:
                # Conflicting types found! E.g. res = INT and x = REAL
                return None
        return res


    def force_type(self, formula, ty):
        """
        Given a formula and a type, it rewrites the formula transforming all the
        GenericNumbers to the given type.

        The function uses the map self.ft_memoization as storage

        :returns The rewritten formula
        """
        assert ty is not None
        assert ty in [REAL, INT]

        stack = [formula]

        while len(stack) > 0:
            expr = stack.pop()

            if (expr, ty) not in self.ft_memoization:
                # Phase 1: append all the children to the stack and
                # set memoization to None to go to phase 2
                self.ft_memoization[(expr, ty)] = None
                stack.append(expr)
                for x in expr.get_sons():
                    stack.append(x)
            elif self.ft_memoization[(expr, ty)] is None:
                # Phase 2: Do the rewriting (as all the children have
                # been processed already) and save the result in the
                # memoization map.
                res = None
                if self.is_generic_number(expr):
                    if ty == REAL:
                        res = expr.as_real(self.mgr)
                    else:
                        assert ty == INT
                        res = expr.as_int(self.mgr)
                else:
                    # Get all the rewritten childern and build the
                    # rewriting for 'formula' by calling the proper
                    # constructor
                    args = [self.ft_memoization[(s, ty)]
                            for s in expr.get_sons()]

                    # Simply rebuild the formula by exploiting the
                    # IdentityDagWalker functions
                    fun = self.identity.functions[expr.node_type()]
                    res = fun(expr, args)

                self.ft_memoization[(expr, ty)] = res
            else:
                # we already visited the node, nothing else to do
                pass

        return self.ft_memoization[(formula, ty)]


    def disambiguate(self, formula):
        """
        Takes a formula and replaces all the occurrencies of GenericNumber to
        proper instances of Real or Int, resolving the types
        accordingly.

        If self.create_toreal_on_demand is set to true, the function is allowed
        to introduce ToReal nodes to create a well typed formula (If it is
        set to false, a TypeError will be raised)
        """
        res = self._walk_disambiguate(formula)
        if self.get_operator_type(res) == NumberDisambiguator.GENERIC:
            raise TypeError("Unable to disambiguate the given formula")
        return res


    def _walk_disambiguate(self, formula):
        stack = [formula]

        while len(stack) > 0:
            expr = stack.pop()

            if expr not in self.memoization:
                # Phase 1: add all the children to the stack
                self.memoization[expr] = None
                stack.append(expr)
                for x in expr.get_sons():
                    stack.append(x)
            elif self.memoization[expr] is None:
                args = [self.memoization[x] for x in expr.get_sons()]
                types = [self.get_operator_type(x) for x in args]
                res = None

                if self.is_generic_number(expr) or expr.is_constant():
                    res = expr

                elif expr.is_ite():
                    gt = self.get_most_specific_type(types[1:])
                    if gt != NumberDisambiguator.GENERIC:
                        if types[1] == NumberDisambiguator.GENERIC:
                            args[1] = self.force_type(args[1], gt)
                        if types[2] == NumberDisambiguator.GENERIC:
                            args[2] = self.force_type(args[2], gt)

                    res = self.mgr.Ite(args[0], args[1], args[2])

                elif expr.is_function_application():
                    fun = expr.function_name()
                    funty = fun.symbol_type()
                    for i, t in enumerate(types):
                        if t == NumberDisambiguator.GENERIC:
                            args[i] = self.force_type(args[i],
                                                      funty.param_types[i])
                        elif funty.param_types[i] == REAL and t == INT:
                            if self.create_toreal_on_demand:
                                args[i] = self.mgr.ToReal(args[i])
                            else:
                                raise TypeError("The input formula is not well "\
                                                "formed, an integer is passed " \
                                                "to function " + str(fun) + \
                                                " where a real is required.")

                    # simply rebuild the formula
                    res = self.mgr.Function(fun, args)

                else:
                    gt = self.get_most_specific_type(types)
                    if len(types) > 0 and gt is None:
                        # We found a conflict in a non-leaf node
                        if self.create_toreal_on_demand and \
                           INT in types and REAL in types:
                            gt = REAL
                            for i, t in enumerate(types):
                                if t == INT:
                                    types[i] = REAL
                                    args[i] = self.mgr.ToReal(args[i])
                                elif t == NumberDisambiguator.GENERIC:
                                    types[i] = REAL
                                    args[i] = self.force_type(args[i], REAL)
                                else:
                                    assert t == REAL
                        else:
                            print types, gt
                            raise TypeError("The input formula is not well formed.")
                    else:
                        if (expr.is_le() or expr.is_lt() or expr.is_equals()) \
                           and (gt == NumberDisambiguator.GENERIC):
                            # If we are in a relation and both the
                            # sons are genreic, we can interpret them
                            # as either reals or integers:
                            # e.g. (> (ite cond 2 4) 1)
                            gt = REAL

                        # It is a leaf or it has no conflicts in the types
                        # We force the most generic type to every child
                        if gt != NumberDisambiguator.GENERIC:
                            for i, t in enumerate(types):
                                if t == NumberDisambiguator.GENERIC:
                                    args[i] = self.force_type(args[i], gt)

                    # simply rebuild the formula
                    fun = self.identity.functions[expr.node_type()]
                    res = fun(expr, args)

                self.memoization[expr] = res
            else:
                # we already visited the node, nothing else to do
                pass

        return self.memoization[formula]
