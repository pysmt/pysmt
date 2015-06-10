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
"""
This module defines some rewritings for pySMT formulae.
"""

from pysmt.walkers.dag import DagWalker
import pysmt.typing as types
import pysmt.operators as op
import pysmt.environment

class CNFizer(DagWalker):

    THEORY_PLACEHOLDER = "__Placeholder__"

    TRUE_CNF = frozenset()
    FALSE_CNF = frozenset([frozenset()])

    def __init__(self, environment=None):
        DagWalker.__init__(self, environment)
        self.mgr = self.env.formula_manager
        self._introduced_variables = {}
        self._cnf_pieces = {}

    def _key_var(self, formula):
        if formula in self._introduced_variables:
            res = self._introduced_variables[formula]
        else:
            res = self.mgr.FreshSymbol()
            self._introduced_variables[formula] = res
        return res

    def convert(self, formula):
        """Convert formula into an Equisatisfiable CNF.

        Returns a set of clauses: a set of set of literals.
        """
        tl, _cnf = self.walk(formula)
        res = [frozenset([tl])]
        for clause in _cnf:
            if len(clause) == 0:
                return CNFizer.FALSE_CNF
            simp = []
            for lit in clause:
                if lit.is_true():
                    # Prune clauses that are trivially TRUE
                    simp = None
                    break
                elif not lit.is_false():
                    # Prune FALSE literals
                    simp.append(lit)
            if simp:
                res.append(frozenset(simp))
        return frozenset(res)

    def convert_as_formula(self, formula):
        """Convert formula into an Equisatisfiable CNF.

        Returns an FNode.
        """
        lsts = self.convert(formula)

        conj = []
        for clause in lsts:
            conj.append(self.mgr.Or(clause))
        return self.mgr.And(conj)

    def printer(self, _cnf):
        print(self.serialize(_cnf))
        return

    def serialize(self, _cnf):
        clauses = []
        for clause in _cnf:
            clauses +=[" { " + " ".join(str(lit) for lit in clause) + "} "]
        res = ["{"] + clauses + ["}"]
        return "".join(res)



    def walk_forall(self, formula, args, **kwargs):
        raise NotImplementedError("CNFizer does not support quantifiers")

    def walk_exists(self, formula, args, **kwargs):
        raise NotImplementedError("CNFizer does not support quantifiers")

    def walk_and(self, formula, args, **kwargs):
        if len(args) == 1:
            return args[0]

        k = self._key_var(formula)
        _cnf = [frozenset([k] + [self.mgr.Not(a).simplify() for a,_ in args])]
        for a,c in args:
            _cnf.append(frozenset([a, self.mgr.Not(k)]))
            for clause in c:
                _cnf.append(clause)
        return k, frozenset(_cnf)

    def walk_or(self, formula, args, **kwargs):
        if len(args) == 1:
            return args[0]
        k = self._key_var(formula)
        _cnf = [frozenset([self.mgr.Not(k)] + [a for a,_ in args])]
        for a,c in args:
            _cnf.append(frozenset([k, self.mgr.Not(a)]))
            for clause in c:
                _cnf.append(clause)
        return k, frozenset(_cnf)

    def walk_not(self, formula, args, **kwargs):
        a, _cnf = args[0]
        if a.is_true():
            return self.mgr.FALSE(), CNFizer.TRUE_CNF
        elif a.is_false():
            return self.mgr.TRUE(), CNFizer.TRUE_CNF
        else:
            k = self._key_var(formula)
            return k, _cnf | frozenset([frozenset([self.mgr.Not(k),
                                                  self.mgr.Not(a).simplify()]),
                                       frozenset([k, a])])

    def walk_implies(self, formula,  args, **kwargs):
        a, cnf_a = args[0]
        b, cnf_b = args[1]

        k = self._key_var(formula)
        not_a = self.mgr.Not(a).simplify()
        not_b = self.mgr.Not(b).simplify()

        return k, (cnf_a | cnf_b | frozenset([frozenset([not_a, b, k]),
                                              frozenset([a, k]),
                                              frozenset([not_b, k])]))

    def walk_iff(self, formula, args, **kwargs):
        a, cnf_a = args[0]
        b, cnf_b = args[1]

        k = self._key_var(formula)
        not_a = self.mgr.Not(a).simplify()
        not_b = self.mgr.Not(b).simplify()
        not_k = self.mgr.Not(k)

        return k, (cnf_a | cnf_b | frozenset([frozenset([not_a, not_b, k]),
                                              frozenset([not_a, b, not_k]),
                                              frozenset([a, not_b, not_k]),
                                              frozenset([a, b, k])]))

    def walk_symbol(self, formula, **kwargs):
        if formula.is_symbol(types.BOOL):
            return formula, CNFizer.TRUE_CNF
        else:
            return CNFizer.THEORY_PLACEHOLDER

    def walk_function(self, formula, **kwargs):
        ty = formula.function_symbol().symbol_type()
        if ty.return_type.is_bool_type():
            return formula, CNFizer.TRUE_CNF
        else:
            return CNFizer.THEORY_PLACEHOLDER

    def walk_real_constant(self, formula, **kwargs):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_bool_constant(self, formula, **kwargs):
        if formula.is_true():
            return formula, CNFizer.TRUE_CNF
        else:
            return formula, CNFizer.TRUE_CNF

    def walk_int_constant(self, formula, **kwargs):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_plus(self, formula, **kwargs):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_minus(self, formula, **kwargs):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_times(self, formula, **kwargs):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_equals(self, formula, args, **kwargs):
        assert all(a == CNFizer.THEORY_PLACEHOLDER for a in args)
        return formula, CNFizer.TRUE_CNF

    def walk_le(self, formula, args, **kwargs):
        assert all(a == CNFizer.THEORY_PLACEHOLDER for a in args)
        return formula, CNFizer.TRUE_CNF

    def walk_lt(self, formula, args, **kwargs):
        assert all(a == CNFizer.THEORY_PLACEHOLDER for a in args), str(args)
        return formula, CNFizer.TRUE_CNF

    def walk_ite(self, formula, args, **kwargs):
        if any(a == CNFizer.THEORY_PLACEHOLDER for a in args):
            return CNFizer.THEORY_PLACEHOLDER
        else:
            (i,cnf_i),(t,cnf_t),(e,cnf_e) = args
            k = self._key_var(formula)
            not_i = self.mgr.Not(i).simplify()
            not_t = self.mgr.Not(t).simplify()
            not_e = self.mgr.Not(e).simplify()
            not_k = self.mgr.Not(k)

            return k, (cnf_i | cnf_t | cnf_e |
                       frozenset([frozenset([not_i, not_t, k]),
                                  frozenset([not_i, t, not_k]),
                                  frozenset([i, not_e, k]),
                                  frozenset([i, e, not_k])]))

    def walk_toreal(self, formula, **kwargs):
        return CNFizer.THEORY_PLACEHOLDER


class NNFizer(object):

    def __init__(self, environment=None):
        if environment is None:
            # Avoids possible circular imports
            environment = pysmt.environment.get_env()

        self.env = environment
        self.memoization = {}
        self.manager = self.env.formula_manager


    def convert(self, formula):
        """ Converts the given formula in NNF """
        stack = [formula]
        while len(stack) > 0:
            current = stack.pop()
            if current not in self.memoization:
                self.memoization[current] = None
                stack.append(current)
                for son in self._get_children(current):
                    stack.append(son)

            elif self.memoization[current] is None:
                res = self._rebuild(current)
                self.memoization[current] = res
            else:
                # we already visited the node, nothing else to do
                pass
        return self.memoization[formula]


    def _get_children(self, formula):
        """Returns the arguments of the node on which an hypotetical recursion
        would be made, possibly negating them.
        """
        mgr = self.manager
        if formula.is_not():
            s = formula.arg(0)
            if s.is_not():
                return [s.arg(0)]
            elif s.is_and():
                return [mgr.Not(x) for x in s.args()]
            elif s.is_or():
                return [mgr.Not(x) for x in s.args()]
            elif s.is_implies():
                return [s.arg(0), mgr.Not(s.arg(1))]
            elif s.is_iff():
                return [s.arg(0), s.arg(1),
                        mgr.Not(s.arg(0)),
                        mgr.Not(s.arg(1))]
            elif s.is_quantifier():
                return [mgr.Not(s.arg(0))]
            else:
                return [s]

        elif formula.is_implies():
            return [mgr.Not(formula.arg(0)), formula.arg(1)]

        elif formula.is_iff():
            return [formula.arg(0), formula.arg(1),
                    mgr.Not(formula.arg(0)),
                    mgr.Not(formula.arg(1))]

        elif formula.is_and() or formula.is_or() or formula.is_quantifier():
            return formula.args()

        elif formula.is_ite():
            # This must be a boolean ITE as we do not recur within
            # theory atoms
            assert self.env.stc.get_type(formula).is_bool_type()
            i, t, e = formula.args()
            return [i, mgr.Not(i), t, e]

        elif formula.is_symbol():
            return []

        elif formula.is_bool_constant():
            return []

        else:
            # This is a theory atom
            assert formula.is_theory_relation(), str(formula)
            return []


    def _rebuild(self, formula):
        memo = self.memoization
        mgr = self.manager
        if formula.is_not():
            s = formula.arg(0)
            if s.is_symbol():
                return mgr.Not(s)
            elif s.is_not():
                return memo[s.arg(0)]
            elif s.is_and():
                return mgr.Or([memo[mgr.Not(x)] for x in s.args()])
            elif s.is_or():
                return mgr.And([memo[mgr.Not(x)] for x in s.args()])
            elif s.is_implies():
                return mgr.And(memo[s.arg(0)], memo[mgr.Not(s.arg(1))])
            elif s.is_iff():
                return mgr.Or(mgr.And(memo[s.arg(0)], memo[mgr.Not(s.arg(1))]),
                              mgr.And(memo[s.arg(1)], memo[mgr.Not(s.arg(0))]))
            elif s.is_forall():
                return mgr.Exists(s.quantifier_vars(), memo[mgr.Not(s.arg(0))])
            elif s.is_exists():
                return mgr.ForAll(s.quantifier_vars(), memo[mgr.Not(s.arg(0))])
            else:
                return mgr.Not(memo[s])

        elif formula.is_implies():
            return mgr.Or(memo[mgr.Not(formula.arg(0))], memo[formula.arg(1)])

        elif formula.is_iff():
            a, b = formula.args()
            na, nb = mgr.Not(a), mgr.Not(b)
            return mgr.And(mgr.Or(memo[na], memo[b]),
                           mgr.Or(memo[nb], memo[a]))

        elif formula.is_and():
            return mgr.And(memo[x] for x in formula.args())

        elif formula.is_or():
            return mgr.Or(memo[x] for x in formula.args())

        elif formula.is_ite():
            # This must be a boolean ITE as we do not recur within
            # theory atoms
            assert self.env.stc.get_type(formula).is_bool_type()
            i, t, e = formula.args()
            ni = mgr.Not(i)
            return mgr.And(mgr.Or(memo[ni], memo[t]),
                           mgr.Or(memo[i], memo[e]))

        elif formula.is_forall():
            return mgr.ForAll(formula.quantifier_vars(), memo[formula.arg(0)])

        elif formula.is_exists():
            return mgr.Exists(formula.quantifier_vars(), memo[formula.arg(0)])

        elif formula.is_symbol():
            return formula

        elif formula.is_bool_constant():
            return formula

        else:
            # This is a theory atom
            assert formula.is_theory_relation()
            return formula


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

        for elem in op.ALL_TYPES:
            if elem in op.QUANTIFIERS:
                self.functions[elem] = self.walk_quantifier
            elif elem in op.CONSTANTS:
                self.functions[elem] = self.walk_constant
            elif elem in op.RELATIONS:
                self.functions[elem] = self.walk_theory_relation
            elif elem in op.BV_OPERATORS or elem in op.LIRA_OPERATORS:
                self.functions[elem] = self.walk_theory_op
            else:
                self.functions[elem] = self.walk_error
        self.functions[op.SYMBOL] = self.walk_symbol
        self.functions[op.FUNCTION] = self.walk_function
        self.functions[op.ITE] = self.walk_ite
        self.functions[op.AND] = self.walk_conj_disj
        self.functions[op.OR] = self.walk_conj_disj
        self.functions[op.NOT] = self.walk_not
        self.functions[op.IFF] = self.walk_iff
        self.functions[op.IMPLIES] = self.walk_implies


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
                    sub = {v : self.mgr.FreshSymbol(v.symbol_type())
                           for v in needs_rename}
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


def nnf(formula, environment=None):
    """Converts the given formula in NNF"""
    nnfizer = NNFizer(environment)
    return nnfizer.convert(formula)

def cnf(formula, environment=None):
    """Converts the given formula in CNF represented as a formula"""
    cnfizer = CNFizer(environment)
    return cnfizer.convert_as_formula(formula)

def cnf_as_set(formula, environment=None):
    """Converts the given formula in CNF represented as a set of sets"""
    cnfizer = CNFizer(environment)
    return cnfizer.convert_as_formula(formula)

def prenex_normal_form(formula, environment=None):
    """Converts the given formula in NNF"""
    normalizer = PrenexNormalizer(environment)
    return normalizer.normalize(formula)


def conjunctive_partition(formula):
    """ Returns a generator over the top-level conjuncts of the given formula

    The result is such that for every formula phi, the following holds:
    phi <-> And(conjunctive_partition(phi))
    """
    to_process = [formula]
    seen = set()
    while to_process:
        cur = to_process.pop()
        if cur not in seen:
            seen.add(cur)
            if cur.is_and():
                to_process += cur.get_sons()
            else:
                yield cur


def disjunctive_partition(formula):
    """ Returns a generator over the top-level disjuncts of the given formula

    The result is such that for every formula phi, the following holds:
    phi <-> Or(conjunctive_partition(phi))
    """
    to_process = [formula]
    seen = set()
    while to_process:
        cur = to_process.pop()
        if cur not in seen:
            seen.add(cur)
            if cur.is_or():
                to_process += cur.get_sons()
            else:
                yield cur
