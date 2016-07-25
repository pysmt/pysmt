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
import pysmt.typing as types
import pysmt.operators as op
from pysmt.walkers import DagWalker


def prenex_normal_form(formula, environment=None):
    """Converts the given formula in NNF"""
    normalizer = PrenexNormalizer(environment)
    return normalizer.normalize(formula)


class PrenexNormalizer(DagWalker):
    """
    This class traverses a formula and rebuilds it in prenex normal form.
    """

    def __init__(self, env=None, invalidate_memoization=None):
        DagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager
        self.check_symbol = self.mgr.FreshSymbol(types.BOOL)

        # The walker returns a pair (L, m) where m is a
        # quantifier-free formula (the matrix) and L is a list of
        # pairs (Q, vars) where Q is either mgr.Exists or mgr.ForAll
        # and vars is a frozenset of variables.  The semantics is that
        # the input formula is equivalent to res computed as follows:
        # res = m
        # for Q, vars in L:
        #    res = Q(vars, res)
        self.set_function(self.walk_error, *op.ALL_TYPES)
        self.set_function(self.walk_quantifier, *op.QUANTIFIERS)
        self.set_function(self.walk_theory_op, *op.THEORY_OPERATORS)
        self.set_function(self.walk_constant, *op.CONSTANTS)
        self.set_function(self.walk_theory_relation, *op.RELATIONS)

        self.set_function(self.walk_symbol, op.SYMBOL)
        self.set_function(self.walk_function, op.FUNCTION)
        self.set_function(self.walk_ite, op.ITE)
        self.set_function(self.walk_conj_disj, op.AND, op.OR)
        self.set_function(self.walk_not, op.NOT)
        self.set_function(self.walk_iff, op.IFF)
        self.set_function(self.walk_implies, op.IMPLIES)


    def normalize(self, formula):
        quantifiers, matrix = self.walk(formula)
        res = matrix
        for Q, qvars in quantifiers:
            res = Q(qvars, res)
        return res

    def _invert_quantifier(self, Q):
        if Q == self.mgr.Exists:
            return self.mgr.ForAll
        return self.mgr.Exists

    def walk_symbol(self, formula, **kwargs):
        if formula.symbol_type().is_bool_type():
            return [],formula
        return None

    def walk_constant(self, formula, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_bool_constant():
            return [],formula
        return None

    def walk_conj_disj(self, formula, args, **kwargs):
        #pylint: disable=unused-argument

        # Hold the final result
        quantifiers = []
        matrix = []

        # A set of variables that are already reserved in the final
        # matrix. If we find a quantifier over a variable in this set
        # we need to alpha-rename before adding the quantifier to the
        # final list and accumulate the matrix.
        reserved = formula.get_free_variables()

        # We iterate to each argument, each could have a sequence of
        # quantifiers that we need to merge
        for sub_quantifiers, sub_matrix in args:
            # For each quantifier in the alternation
            for Q, q_vars in sub_quantifiers:
                # These are the variables that need alpha-renaming
                needs_rename = q_vars & reserved
                if len(needs_rename) > 0:
                    # we need alpha-renaming: prepare the substitution map
                    sub = dict((v,self.mgr.FreshSymbol(v.symbol_type()))
                               for v in needs_rename)
                    sub_matrix = sub_matrix.substitute(sub)

                    # The new variables for this quantifiers will be
                    # its old variables, minus the one needing
                    # renaming, that are renamed.
                    new_q_vars = (q_vars - needs_rename)
                    new_q_vars |= set(sub[x] for x in needs_rename)
                else:
                    # No need to alpha-rename this quantifier, we keep
                    # as it is the set of variables.
                    new_q_vars = set(q_vars)

                # Store this quantifier in the final result
                quantifiers.append((Q, new_q_vars))

                # The variables of this quantifier from now on are
                # reserved, if another quantifier uses any of them it
                # will need alpha-renaming even if this quantifier was
                # OK.
                reserved |= new_q_vars

            # Store the (possibly rewritten) sub_matrix
            matrix.append(sub_matrix)

        # Build and return the result
        if formula.is_and():
            return (quantifiers, self.mgr.And(matrix))
        if formula.is_or():
            return (quantifiers, self.mgr.Or(matrix))

    def walk_not(self, formula, args, **kwargs):
        quantifiers, matrix = args[0]

        nq = [(self._invert_quantifier(Q), qvars) for Q, qvars in quantifiers]
        return (nq, self.mgr.Not(matrix))

    def walk_iff(self, formula, args, **kwargs):
        a, b = formula.args()
        i1 = self.mgr.Implies(a, b)
        i2 = self.mgr.Implies(b, a)
        i1_args = self.walk_implies(i1, [args[0], args[1]])
        i2_args = self.walk_implies(i2, [args[1], args[0]])
        return self.walk_conj_disj(self.mgr.And(i1, i2), [i1_args, i2_args])

    def walk_implies(self, formula, args, **kwargs):
        a, b = formula.args()
        na = self.mgr.Not(a)
        na_arg = self.walk_not(na, [args[0]])
        return self.walk_conj_disj(self.mgr.Or(na, b), [na_arg, args[1]])

    def walk_ite(self, formula, args, **kwargs):
        if any(a is None for a in args):
            return None
        else:
            i, t, e = formula.args()
            i_args, t_args, e_args = args
            ni = self.mgr.Not(i)
            i1 = self.mgr.Implies(i, t)
            i2 = self.mgr.Implies(ni, e)
            ni_args = self.walk_not(ni, [i_args])
            i1_args = self.walk_implies(i1, [i_args, t_args])
            i2_args = self.walk_implies(i2, [ni_args, e_args])
            return self.walk_conj_disj(self.mgr.And(i1, i2), [i1_args, i2_args])

    def walk_theory_relation(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return [], formula

    def walk_quantifier(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        quantifiers, matrix = args[0]
        qvars = set(v for _, qv in quantifiers for v in qv)
        nq = set(formula.quantifier_vars()) - qvars

        # If nq is empty, it means that inner quantifiers shadow all
        # the variables of this quantifier. Hence this quantifier can
        # be removed.
        if len(nq) > 0:
            if formula.is_exists():
                return (quantifiers + [(self.mgr.Exists, nq)]), matrix
            else:
                return (quantifiers + [(self.mgr.ForAll, nq)]), matrix
        return quantifiers, matrix

    def walk_theory_op(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return None

    def walk_function(self, formula, **kwargs):
        if formula.function_name().symbol_type().return_type.is_bool_type():
            return [], formula
        return None

#EOC PrenexNormalizer
