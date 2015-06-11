#
# This file is part of pySMT.
#
#   Copyright 2015 Andrea Micheli and Marco Gario
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
"""This module provides classes used to analyze and determine
properties of formulae.

 * QuantifierOracle says whether a formula is quantifier free
 * TheoryOracle says which logic is used in the formula.
 * FreeVarsOracle says which variables are free in the formula
"""

import pysmt.walkers
import pysmt.operators as op
import pysmt.environment

from pysmt import typing as types

from pysmt.logics import Logic, Theory, get_closer_pysmt_logic


class SizeOracle(pysmt.walkers.DagWalker):
    """Evaluates the size of a formula"""

    # Counting type can be:
    # - TREE_NODES : counts the number of nodes in the formula seen as a tree
    # - DAG_NODES  : counts the number of nodes in the formula seen as a DAG
    # - LEAVES     : counts the number of leaves in the formula seen as a tree
    # - DEPTH      : counts the maximum number of levels in the formula
    # - SYMBOLS    : counts the number of different symbols occurring in the formula
    (MEASURE_TREE_NODES,
     MEASURE_DAG_NODES,
     MEASURE_LEAVES,
     MEASURE_DEPTH,
     MEASURE_SYMBOLS) = range(5)

    def __init__(self, env=None):
        pysmt.walkers.DagWalker.__init__(self, env=env)

        self.measure_to_fun = \
                        {SizeOracle.MEASURE_TREE_NODES: self.walk_count_tree,
                         SizeOracle.MEASURE_DAG_NODES: self.walk_count_dag,
                         SizeOracle.MEASURE_LEAVES: self.walk_count_leaves,
                         SizeOracle.MEASURE_DEPTH: self.walk_count_depth,
                         SizeOracle.MEASURE_SYMBOLS: self.walk_count_symbols}


    def set_walking_measure(self, measure):
        if measure not in self.measure_to_fun:
            raise NotImplementedError

        self.functions.clear()
        for elem in op.ALL_TYPES:
            self.functions[elem] = self.measure_to_fun[measure]

        # Check that no operator in undefined
        assert self.is_complete(verbose=True)


    def _get_key(self, formula, measure, **kwargs):
        # Memoize using a tuple (measure, formula)
        return (measure, formula)


    def get_size(self, formula, measure=None):
        if measure is None:
            # By default, count tree nodes
            measure = SizeOracle.MEASURE_TREE_NODES

        self.set_walking_measure(measure)
        res = self.walk(formula, measure=measure)

        if measure == SizeOracle.MEASURE_DAG_NODES or \
           measure == SizeOracle.MEASURE_SYMBOLS:
            return len(res)
        return res


    def walk_count_tree(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return 1 + sum(args)

    def walk_count_dag(self, formula, args, measure, **kwargs):
        #pylint: disable=unused-argument
        return frozenset([formula]) | frozenset([x for s in args for x in s])

    def walk_count_leaves(self, formula, args, measure, **kwargs):
        #pylint: disable=unused-argument
        is_leaf = (len(args) == 0)
        return (1 if is_leaf else 0) + sum(args)

    def walk_count_depth(self, formula, args, measure, **kwargs):
        #pylint: disable=unused-argument
        is_leaf = (len(args) == 0)
        return 1 + (0 if is_leaf else max(args))

    def walk_count_symbols(self, formula, args, measure, **kwargs):
        #pylint: disable=unused-argument
        is_sym = formula.is_symbol()
        a_res = frozenset([x for s in args for x in s])
        if is_sym:
            return frozenset([formula]) | a_res
        return a_res



class QuantifierOracle(pysmt.walkers.DagWalker):
    def __init__(self, env=None):
        pysmt.walkers.DagWalker.__init__(self, env=env)

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


class TheoryOracle(pysmt.walkers.DagWalker):
    def __init__(self, env=None):
        pysmt.walkers.DagWalker.__init__(self, env=env)

        self.functions[op.AND] = self.walk_combine
        self.functions[op.OR] = self.walk_combine
        self.functions[op.NOT] = self.walk_combine
        self.functions[op.IMPLIES] = self.walk_combine
        self.functions[op.IFF] = self.walk_combine
        self.functions[op.LE] = self.walk_combine
        self.functions[op.LT] = self.walk_combine
        self.functions[op.FORALL] = self.walk_combine
        self.functions[op.EXISTS] = self.walk_combine
        self.functions[op.MINUS] = self.walk_combine
        self.functions[op.ITE] = self.walk_combine

        self.functions[op.REAL_CONSTANT] = self.walk_constant
        self.functions[op.SYMBOL] = self.walk_symbol
        self.functions[op.FUNCTION] = self.walk_function
        self.functions[op.BOOL_CONSTANT] = self.walk_constant
        self.functions[op.INT_CONSTANT] = self.walk_constant
        self.functions[op.TOREAL] = self.walk_lira
        self.functions[op.TIMES] = self.walk_times
        self.functions[op.PLUS] = self.walk_plus
        self.functions[op.EQUALS] = self.walk_equals

        for o in op.BV_OPERATORS:
            # Just propagate BV
            self.functions[o] = self.walk_combine

        # This needs to be handled differently
        self.functions[op.BV_CONSTANT] = self.walk_constant


    def walk_combine(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """Combines the current theory value of the children"""
        if len(args) == 1:
            return args[0].copy()

        theory_out = args[0]
        for t in args[1:]:
            theory_out = theory_out.combine(t)
        return theory_out

    def walk_constant(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """Returns a new theory object with the type of the constant."""
        if formula.is_real_constant():
            theory_out = Theory(real_arithmetic=True, real_difference=True)
        elif formula.is_int_constant():
            theory_out = Theory(integer_arithmetic=True, integer_difference=True)
        elif formula.is_bv_constant():
            theory_out = Theory(bit_vectors=True)
        else:
            assert formula.is_bool_constant()
            theory_out = Theory()

        return theory_out

    def walk_symbol(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """Returns a new theory object with the type of the symbol."""
        f_type = formula.symbol_type()
        if f_type.is_real_type():
            theory_out = Theory(real_arithmetic=True, real_difference=True)
        elif f_type.is_int_type():
            theory_out = Theory(integer_arithmetic=True, integer_difference=True)
        elif f_type.is_bool_type():
            theory_out = Theory()
        elif f_type.is_bv_type():
            theory_out = Theory(bit_vectors=True)
        else:
            assert f_type.is_function_type()
            theory_out = Theory(uninterpreted=True)

        return theory_out

    def walk_function(self, formula, args, **kwargs):
        """Extends the Theory with UF."""
        if len(args) == 1:
            theory_out = args[0].copy()
        elif len(args) > 1:
            theory_out = args[0]
            for t in args[1:]:
                theory_out = theory_out.combine(t)
        else:
            theory_out = Theory()

        theory_out.uninterpreted = True
        return theory_out

    def walk_lira(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """Extends the Theory with LIRA."""
        theory_out = args[0].copy()
        theory_out = theory_out.set_lira()
        return theory_out

    def walk_times(self, formula, args, **kwargs):
        """Extends the Theory with Non-Linear, if needed."""
        if len(args) == 1:
            theory_out = args[0].copy()
        else:
            theory_out = args[0]
            for t in args[1:]:
                theory_out = theory_out.combine(t)
        # Check for non linear?
        theory_out = theory_out.set_difference_logic(False)
        return theory_out

    def walk_plus(self, formula, args, **kwargs):
        theory_out = args[0]
        for t in args[1:]:
            theory_out = theory_out.combine(t)
        theory_out = theory_out.set_difference_logic(value=False)
        assert not theory_out.real_difference
        assert not theory_out.integer_difference
        return theory_out

    def walk_equals(self, formula, args, **kwargs):
        return self.walk_combine(formula, args)

    def get_theory(self, formula):
        """Returns the thoery for the formula."""
        return self.walk(formula)

# EOC TheoryOracle


# Operators for which Args is an FNode
DEPENDENCIES_SIMPLE_ARGS = (set(op.ALL_TYPES) - \
                           (set([op.SYMBOL, op.FUNCTION]) | op.QUANTIFIERS | op.CONSTANTS))

class FreeVarsOracle(pysmt.walkers.DagWalker):
    def __init__(self, env=None):
        pysmt.walkers.DagWalker.__init__(self, env=env)

        # Clear the mapping function
        self.functions.clear()

        # We have only few categories for this walker.
        #
        # - Simple Args simply need to combine the cone/dependencies
        #   of the children.
        # - Quantifiers need to exclude bounded variables
        # - Constants have no impact
        #
        for elem in op.ALL_TYPES:
            if elem in DEPENDENCIES_SIMPLE_ARGS:
                self.functions[elem] = self.walk_simple_args
            elif elem in op.QUANTIFIERS:
                self.functions[elem] = self.walk_quantifier
            elif elem in op.CONSTANTS:
                self.functions[elem] = self.walk_constant
            else:
                self.functions[elem] = self.walk_error

        # These are the only 2 cases that can introduce elements.
        self.functions[op.SYMBOL] = self.walk_symbol
        self.functions[op.FUNCTION] = self.walk_function

        # Check that no operator in undefined
        assert self.is_complete(verbose=True)


    def get_free_variables(self, formula):
        """Returns the set of Symbols appearing free in the formula."""
        return self.walk(formula)

    def walk_simple_args(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        res = set()
        for arg in args:
            res.update(arg)
        return frozenset(res)

    def walk_quantifier(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return args[0].difference(formula.quantifier_vars())

    def walk_symbol(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return frozenset([formula])

    def walk_constant(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return frozenset()

    def walk_function(self, formula, args, **kwargs):
        res = set([formula.function_name()])
        for arg in args:
            res.update(arg)
        return frozenset(res)

# EOC FreeVarsOracle

class AtomsOracle(pysmt.walkers.DagWalker):
    """This class returns the set of Boolean atoms involved in a formula
    A boolean atom is either a boolean variable or a theory atom
    """
    def __init__(self, env=None):
        pysmt.walkers.DagWalker.__init__(self, env=env)

        # Clear the mapping function
        self.functions.clear()

        # We have teh following categories for this walker.
        #
        # - Boolean operators, e.g. and, or, not...
        # - Theory operators, e.g. +, -, bvshift
        # - Theory relations, e.g. ==, <=
        # - ITE terms
        # - Symbols
        # - Constants
        #
        for elem in op.ALL_TYPES:
            if elem in op.BOOL_CONNECTIVES or elem in op.QUANTIFIERS:
                self.functions[elem] = self.walk_bool_op
            elif elem in op.CONSTANTS:
                self.functions[elem] = self.walk_constant
            elif elem in op.RELATIONS:
                self.functions[elem] = self.walk_theory_relation
            elif elem in op.BV_OPERATORS or elem in op.LIRA_OPERATORS:
                self.functions[elem] = self.walk_theory_op
            else:
                self.functions[elem] = self.walk_error

        self.functions[op.SYMBOL] = self.walk_symbol
        self.functions[op.FUNCTION] = self.walk_theory_op
        self.functions[op.ITE] = self.walk_ite

        # Check that no operator in undefined
        assert self.is_complete(verbose=True)


    def get_atoms(self, formula):
        """Returns the set of atoms appearing in the formula."""
        return self.walk(formula)

    def walk_bool_op(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return frozenset(x for a in args for x in a)

    def walk_theory_relation(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return frozenset([formula])

    def walk_theory_op(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return None

    def walk_symbol(self, formula, **kwargs):
        if formula.is_symbol(types.BOOL):
            return frozenset([formula])
        return None

    def walk_constant(self, formula, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_bool_constant():
            return frozenset()
        return None

    def walk_ite(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if any(a is None for a in args):
            # Theory ITE
            return None
        else:
            return frozenset(x for a in args for x in a)



def get_logic(formula, env=None):
    if env is None:
        env = pysmt.environment.get_env()
    # Get Quantifier Information
    qf = env.qfo.is_qf(formula)
    theory = env.theoryo.get_theory(formula)
    logic = Logic(name="Detected Logic", description="",
                  quantifier_free=qf, theory=theory)
    # Return a logic supported by PySMT that is close to the one computed
    return get_closer_pysmt_logic(logic)
