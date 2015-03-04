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
import pysmt.shortcuts as shortcuts
from pysmt.walkers import DagWalker
from pysmt.typing import BOOL

class CNFizer(DagWalker):

    THEORY_PLACEHOLDER = "__Placeholder__"

    TRUE_CNF = frozenset()
    FALSE_CNF = frozenset([frozenset()])

    def __init__(self, environment=None):
        DagWalker.__init__(self)
        self.env = environment if environment else shortcuts.get_env()
        self.mgr = self.env.formula_manager
        self._introduced_variables = {}
        self._current_cone = None

    def _get_symbol(self, cnf):
        if len(cnf) != 1:
            return None

        clause = next(iter(cnf))
        if len(clause) != 1:
            return None

        el = next(iter(clause))
        if el.is_symbol():
            return el
        else:
            return None

    def _is_false(self, cnf):
        if len(cnf) == 0:
            return False
        return all(len(x) == 0 for x in cnf)

    def _is_true(self, cnf):
        return len(cnf) == 0

    def _key_var(self, cnf):
        sy = self._get_symbol(cnf)
        if sy is not None:
            return sy

        if cnf in self._introduced_variables:
            res = self._introduced_variables[cnf]
        else:
            res = self.mgr.FreshSymbol()
            self._introduced_variables[cnf] = res
        self._current_cone.add((res, cnf))
        return res

    def convert(self, formula):
        self._current_cone = set()
        tl = self.walk(formula)
        add_clauses = []
        for k, cnf in self._current_cone:
            add_clauses += [frozenset([self.mgr.Not(k)] + list(c)) for c in cnf]
        res = frozenset(list(tl) + add_clauses)
        self._current_cone = None
        return res

    def convert_as_formula(self, formula):
        lsts = self.convert(formula)

        conj = []
        for clause in lsts:
            if len(clause) == 0:
                return self.mgr.FALSE()
            elif len(clause) == 1:
                conj.append(next(iter(clause)))
            else:
                conj.append(self.mgr.Or(clause))

        if len(conj) == 0:
            return self.mgr.TRUE()
        elif len(conj) == 1:
            return conj[0]
        else:
            return self.mgr.And(conj)

    def walk_forall(self, formula, args):
        raise NotImplementedError("CNFizer does not support quantifiers")

    def walk_exists(self, formula, args):
        raise NotImplementedError("CNFizer does not support quantifiers")

    def walk_and(self, formula, args):
        res = []
        for a in args:
            if self._is_false(a):
                return CNFizer.FALSE_CNF
            elif not self._is_true(a):
                res += list(a)
        return frozenset(res)

    def walk_or(self, formula, args):
        res = []
        for a in args:
            if self._is_true(a):
                return CNFizer.TRUE_CNF
            elif not self._is_false(a):
                res.append(self._key_var(a))
        return frozenset([frozenset(res)])

    def walk_not(self, formula, args):
        a = args[0]
        if len(a) == 1:
            na = next(iter(a))
            return frozenset(frozenset([self.mgr.Not(x)]) for x in na)

        k = self._key_var(a)
        return frozenset([frozenset([self.mgr.Not(k)])])

    def walk_implies(self, formula,  args):
        not_a = self.mgr.Not(formula.arg(0))
        r_not_a = self.walk_not(not_a, [args[0]])
        return self.walk_or(self.mgr.Or(not_a, formula.arg(1)),
                            [r_not_a, args[1]])

    def walk_iff(self, formula,  args):
        a = formula.arg(0)
        b = formula.arg(1)
        not_a = self.mgr.Not(a)
        not_b = self.mgr.Not(b)

        rw = self.mgr.And(self.mgr.Or(not_a, b), self.mgr.Or(not_b, a))
        return self.walk(rw)

    def walk_symbol(self, formula,  args):
        if formula.is_symbol(BOOL):
            return frozenset([frozenset([formula])])
        else:
            return CNFizer.THEORY_PLACEHOLDER

    def walk_function(self, formula,  args):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_real_constant(self, formula,  args):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_bool_constant(self, formula,  args):
        if formula.is_true():
            return frozenset()
        else:
            return frozenset([frozenset()])

    def walk_int_constant(self, formula,  args):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_plus(self, formula,  args):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_minus(self, formula,  args):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_times(self, formula,  args):
        return CNFizer.THEORY_PLACEHOLDER

    def walk_equals(self, formula, args):
        assert all(a == CNFizer.THEORY_PLACEHOLDER for a in args)
        return frozenset([frozenset([formula])])

    def walk_le(self, formula, args):
        assert all(a == CNFizer.THEORY_PLACEHOLDER for a in args)
        return frozenset([frozenset([formula])])

    def walk_lt(self, formula, args):
        assert all(a == CNFizer.THEORY_PLACEHOLDER for a in args), str(args)
        return frozenset([frozenset([formula])])

    def walk_ite(self, formula, args):
        if any(a == CNFizer.THEORY_PLACEHOLDER for a in args):
            return CNFizer.THEORY_PLACEHOLDER
        else:
            i,t,e = formula.args()
            f = self.mgr.And(self.mgr.Iff(i, t),
                             self.mgr.Iff(self.mgr.Not(i), e))
            return self.walk(f)

    def walk_toreal(self, formula, args):
        return CNFizer.THEORY_PLACEHOLDER
