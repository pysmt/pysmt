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

 * SizeOracle provides metrics about the formula
 * QuantifierOracle says whether a formula is quantifier free
 * TheoryOracle says which logic is used in the formula.
 * FreeVarsOracle provides variables that are free in the formula
 * AtomsOracle provides the set of boolean atoms in the formula
 * TypesOracle provides the list of types in the formula
"""

import pysmt
import pysmt.walkers as walkers
import pysmt.operators as op

from pysmt import typing

from pysmt.logics import Logic, Theory, get_closer_pysmt_logic


class SizeOracle(walkers.DagWalker):
    """Evaluates the size of a formula"""

    # Counting type can be:
    # - TREE_NODES : counts the number of nodes in the formula seen as a tree
    # - DAG_NODES  : counts the number of nodes in the formula seen as a DAG
    # - LEAVES     : counts the number of leaves in the formula seen as a tree
    # - DEPTH      : counts the maximum number of levels in the formula
    # - SYMBOLS    : counts the number of different symbols occurring in the formula
    # - BOOL_DAG   : counts the dag size by considering theory atoms as leaf
    (MEASURE_TREE_NODES,
     MEASURE_DAG_NODES,
     MEASURE_LEAVES,
     MEASURE_DEPTH,
     MEASURE_SYMBOLS,
     MEASURE_BOOL_DAG) = range(6)

    def __init__(self, env=None):
        walkers.DagWalker.__init__(self, env=env)

        self.measure_to_fun = \
                        {SizeOracle.MEASURE_TREE_NODES: self.walk_count_tree,
                         SizeOracle.MEASURE_DAG_NODES: self.walk_count_dag,
                         SizeOracle.MEASURE_LEAVES: self.walk_count_leaves,
                         SizeOracle.MEASURE_DEPTH: self.walk_count_depth,
                         SizeOracle.MEASURE_SYMBOLS: self.walk_count_symbols,
                         SizeOracle.MEASURE_BOOL_DAG: self.walk_count_bool_dag,
                        }


    def set_walking_measure(self, measure):
        if measure not in self.measure_to_fun:
            raise NotImplementedError
        self.set_function(self.measure_to_fun[measure], *op.ALL_TYPES)

    def _get_key(self, formula, measure, **kwargs):
        """Memoize using a tuple (measure, formula)."""
        return (measure, formula)

    def get_size(self, formula, measure=None):
        """Return the size of the formula according to the specified measure.

        The default measure is MEASURE_TREE_NODES.
        """
        if measure is None:
            # By default, count tree nodes
            measure = SizeOracle.MEASURE_TREE_NODES

        self.set_walking_measure(measure)
        res = self.walk(formula, measure=measure)

        if measure == SizeOracle.MEASURE_DAG_NODES or \
           measure == SizeOracle.MEASURE_SYMBOLS or \
           measure == SizeOracle.MEASURE_BOOL_DAG :
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

    def walk_count_bool_dag(self, formula, args, measure, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_theory_relation():
            return frozenset([formula])
        return frozenset([formula]) | frozenset([x for s in args for x in s])


class QuantifierOracle(walkers.DagWalker):
    def is_qf(self, formula):
        """ Returns whether formula is Quantifier Free. """
        return self.walk(formula)

    # Propagate truth value, but force False if a Quantifier is found.
    @walkers.handles(set(op.ALL_TYPES) - op.QUANTIFIERS)
    def walk_all(self, formula, args, **kwargs):
        return walkers.DagWalker.walk_all(self, formula, args, **kwargs)

    @walkers.handles(op.QUANTIFIERS)
    def walk_false(self, formula, args, **kwargs):
        return walkers.DagWalker.walk_false(self, formula, args, **kwargs)

# EOC QuantifierOracle


class TheoryOracle(walkers.DagWalker):

    def get_theory(self, formula):
        """Returns the thoery for the formula."""
        return self.walk(formula)

    def _theory_from_type(self, ty):
        theory = Theory()
        if ty.is_real_type():
            theory.real_arithmetic = True
            theory.real_difference = True
        elif ty.is_int_type():
            theory.integer_arithmetic = True
            theory.integer_difference = True
        elif ty.is_bool_type():
            pass
        elif ty.is_bv_type():
            theory.bit_vectors = True
        elif ty.is_array_type():
            theory.arrays = True
            theory = theory.combine(self._theory_from_type(ty.index_type))
            theory = theory.combine(self._theory_from_type(ty.elem_type))
        elif ty.is_string_type():
            theory.strings = True
        elif ty.is_custom_type():
            theory.custom_type = True
        else:
            # ty is either a function type
            theory.uninterpreted = True
        return theory

    @walkers.handles(op.RELATIONS)
    @walkers.handles(op.BOOL_OPERATORS)
    @walkers.handles(op.BV_OPERATORS)
    @walkers.handles(op.STR_OPERATORS -\
                     set([op.STR_LENGTH, op.STR_INDEXOF, op.STR_TO_INT]))
    @walkers.handles(op.ITE, op.ARRAY_SELECT, op.ARRAY_STORE, op.MINUS)
    def walk_combine(self, formula, args, **kwargs):
        """Combines the current theory value of the children"""
        #pylint: disable=unused-argument
        if len(args) == 1:
            return args[0].copy()
        theory_out = args[0]
        for t in args[1:]:
            theory_out = theory_out.combine(t)
        return theory_out

    @walkers.handles(op.REAL_CONSTANT, op.BOOL_CONSTANT)
    @walkers.handles(op.INT_CONSTANT, op.BV_CONSTANT)
    @walkers.handles(op.ALGEBRAIC_CONSTANT)
    @walkers.handles(op.STR_CONSTANT)
    def walk_constant(self, formula, args, **kwargs):
        """Returns a new theory object with the type of the constant."""
        #pylint: disable=unused-argument
        theory_out = Theory()
        if formula.is_real_constant() or formula.is_algebraic_constant():
            theory_out.real_arithmetic = True
            theory_out.real_difference = True
        elif formula.is_int_constant():
            theory_out.integer_arithmetic = True
            theory_out.integer_difference = True
        elif formula.is_bv_constant():
            theory_out.bit_vectors = True
        elif formula.is_string_constant():
            theory_out.strings = True
        else:
            assert formula.is_bool_constant()
        return theory_out

    def walk_symbol(self, formula, args, **kwargs):
        """Returns a new theory object with the type of the symbol."""
        #pylint: disable=unused-argument
        f_type = formula.symbol_type()
        theory_out = self._theory_from_type(f_type)
        return theory_out

    def walk_function(self, formula, args, **kwargs):
        """Extends the Theory with UF."""
        #pylint: disable=unused-argument
        if len(args) == 1:
            theory_out = args[0].copy()
        elif len(args) > 1:
            theory_out = args[0]
            for t in args[1:]:
                theory_out = theory_out.combine(t)
        else:
            theory_out = Theory()
        # Extend Theory with function return type
        rtype = formula.function_name().symbol_type().return_type
        theory_out = theory_out.combine(self._theory_from_type(rtype))
        theory_out.uninterpreted = True
        return theory_out

    def walk_toreal(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """Extends the Theory with LIRA."""
        theory_out = args[0].set_lira() # This makes a copy of args[0]
        return theory_out
        rtype = formula.symbol_name()

    @walkers.handles([op.STR_LENGTH, op.STR_INDEXOF, op.STR_TO_INT])
    def walk_str_int(self, formula, args, **kwargs):
        theory_out = self.walk_combine(formula, args, **kwargs)
        theory_out.integer_arithmetic = True
        theory_out.integer_difference = True
        return theory_out

    def walk_bv_tonatural(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        """Extends the Theory with Integer."""
        theory_out = args[0].copy()
        theory_out.integer_arithmetic = True
        theory_out.integer_difference = True
        return theory_out

    def walk_times(self, formula, args, **kwargs):
        """Extends the Theory with Non-Linear, if needed."""
        theory_out = args[0]
        for t in args[1:]:
            theory_out = theory_out.combine(t)
        # Check for non-linear counting the arguments having at least
        # one free variable
        if sum(1 for x in formula.args() if x.get_free_variables()) > 1:
            theory_out = theory_out.set_linear(False)
        # This is  not in DL anymore
        theory_out = theory_out.set_difference_logic(False)
        return theory_out

    def walk_pow(self, formula, args, **kwargs):
        return args[0].set_linear(False)

    def walk_plus(self, formula, args, **kwargs):
        theory_out = args[0]
        for t in args[1:]:
            theory_out = theory_out.combine(t)
        theory_out = theory_out.set_difference_logic(value=False)
        assert not theory_out.real_difference
        assert not theory_out.integer_difference
        return theory_out

    def walk_strings(self, formula, args, **kwargs):
        """Extends the Theory with Strings."""
        #pylint: disable=unused-argument
        if formula.is_string_constant():
            theory_out = Theory(strings=True)
        else:
            theory_out = args[0].set_strings() # This makes a copy of args[0]
        return theory_out

    def walk_array_value(self, formula, args, **kwargs):
        # First, we combine all the theories of all the indexes and values
        theory_out = self.walk_combine(formula, args)

        # We combine the index-type theory
        i_type = formula.array_value_index_type()
        idx_theory = self._theory_from_type(i_type)
        theory_out = theory_out.combine(idx_theory)

        # Finally, we add the array theory
        theory_out.arrays = True
        theory_out.arrays_const = True
        return theory_out

    def walk_div(self, formula, args, **kwargs):
        """Extends the Theory with Non-Linear, if needed."""
        assert len(args) == 2
        theory_out = args[0]
        for t in args[1:]:
            theory_out = theory_out.combine(t)
        # Check for non-linear
        left, right = formula.args()
        if len(left.get_free_variables()) != 0 and \
           len(right.get_free_variables()) != 0:
            theory_out = theory_out.set_linear(False)
        elif formula.arg(1).is_zero():
            # DivBy0 is non-linear
            theory_out = theory_out.set_linear(False)
        else:
            theory_out = theory_out.combine(args[1])
        return theory_out

        # This is  not in DL anymore
        theory_out = theory_out.set_difference_logic(False)
        return theory_out

# EOC TheoryOracle


# Operators for which Args is an FNode
DEPENDENCIES_SIMPLE_ARGS = (set(op.ALL_TYPES) - \
                           (set([op.SYMBOL, op.FUNCTION]) | op.QUANTIFIERS | op.CONSTANTS))


class FreeVarsOracle(walkers.DagWalker):
    # We have only few categories for this walker.
    #
    # - Simple Args simply need to combine the cone/dependencies
    #   of the children.
    # - Quantifiers need to exclude bounded variables
    # - Constants have no impact

    def get_free_variables(self, formula):
        """Returns the set of Symbols appearing free in the formula."""
        return self.walk(formula)

    @walkers.handles(DEPENDENCIES_SIMPLE_ARGS)
    def walk_simple_args(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        res = set()
        for arg in args:
            res.update(arg)
        return frozenset(res)

    @walkers.handles(op.QUANTIFIERS)
    def walk_quantifier(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return args[0].difference(formula.quantifier_vars())

    def walk_symbol(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return frozenset([formula])

    @walkers.handles(op.CONSTANTS)
    def walk_constant(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return frozenset()

    def walk_function(self, formula, args, **kwargs):
        res = set([formula.function_name()])
        for arg in args:
            res.update(arg)
        return frozenset(res)

# EOC FreeVarsOracle


class AtomsOracle(walkers.DagWalker):
    """This class returns the set of Boolean atoms involved in a formula
    A boolean atom is either a boolean variable or a theory atom
    """
    # We have the following categories for this walker.
    #
    # - Boolean operators, e.g. and, or, not...
    # - Theory operators, e.g. +, -, bvshift
    # - Theory relations, e.g. ==, <=
    # - ITE terms
    # - Symbols
    # - Constants
    # - Array select, e.g. a[x] because such term could be of Boolean type
    #

    def get_atoms(self, formula):
        """Returns the set of atoms appearing in the formula."""
        return self.walk(formula)

    @walkers.handles(op.BOOL_CONNECTIVES)
    @walkers.handles(op.QUANTIFIERS)
    def walk_bool_op(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        return frozenset(x for a in args for x in a)

    @walkers.handles(op.RELATIONS)
    def walk_theory_relation(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return frozenset([formula])

    @walkers.handles(op.THEORY_OPERATORS - {op.ARRAY_SELECT})
    def walk_theory_op(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return None

    def walk_array_select(self, formula, **kwargs):
        #pylint: disable=unused-argument
        if self.env.stc.get_type(formula).is_bool_type():
            return frozenset([formula])
        return None

    @walkers.handles(op.CONSTANTS)
    def walk_constant(self, formula, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_bool_constant():
            return frozenset()
        return None

    def walk_symbol(self, formula, **kwargs):
        if formula.is_symbol(typing.BOOL):
            return frozenset([formula])
        return None

    def walk_function(self, formula, **kwargs):
        if formula.function_name().symbol_type().return_type.is_bool_type():
            return frozenset([formula])
        return None

    def walk_ite(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if any(a is None for a in args):
            # Theory ITE
            return None
        else:
            return frozenset(x for a in args for x in a)

# EOC AtomsOracle


class TypesOracle(walkers.DagWalker):

    def get_types(self, formula, custom_only=False):
        """Returns the types appearing in the formula.

        custom_only: filter the result by excluding base SMT-LIB types.
        """
        types = self.walk(formula)
        # types is a frozen set
        # exp_types is a list
        exp_types = self.expand_types(types)
        assert len(types) <= len(exp_types)
        # Base types filtering
        if custom_only:
            exp_types = [x for x in exp_types
                         if not x.is_bool_type() and
                         not x.is_int_type() and
                         not x.is_real_type() and
                         not x.is_bv_type() and
                         not x.is_array_type() and
                         not x.is_string_type()
            ]
        return exp_types

    def expand_types(self, types):
        """Recursively look into composite types.

        Note: This returns a list. The list is ordered (by
        construction) by having simpler types first)
        """
        all_types = set()
        expanded = []
        stack = list(types)
        while stack:
            t = stack.pop()
            if t not in all_types:
                expanded.append(t)
                all_types.add(t)
            if t.arity > 0:
                for subtype in t.args:
                    if subtype not in all_types:
                        expanded.append(subtype)
                        all_types.add(subtype)
                        stack.append(subtype)
        expanded.reverse()
        return expanded

    @walkers.handles(set(op.ALL_TYPES) - \
                     set([op.SYMBOL, op.FUNCTION]) -\
                     op.QUANTIFIERS - op.CONSTANTS)
    def walk_combine(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        res = set()
        for arg in args:
            res.update(arg)
        return frozenset(res)

    @walkers.handles(op.SYMBOL)
    def walk_symbol(self, formula, **kwargs):
        return frozenset([formula.symbol_type()])

    @walkers.handles(op.FUNCTION)
    def walk_function(self, formula, **kwargs):
        ftype = formula.function_name().symbol_type()
        return frozenset([ftype.return_type] + list(ftype.param_types))

    @walkers.handles(op.QUANTIFIERS)
    def walk_quantifier(self, formula, args, **kwargs):
        return frozenset([x.symbol_type()
                          for x in formula.quantifier_vars()]) | args[0]

    @walkers.handles(op.CONSTANTS)
    def walk_constant(self, formula, args, **kwargs):
        return frozenset([formula.constant_type()])

# EOC TypesOracle


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
