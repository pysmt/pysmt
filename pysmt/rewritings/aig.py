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
import pysmt.operators as op
from pysmt.walkers import DagWalker


def aig(formula, environment=None):
    """Converts the given formula in AIG"""
    aiger = AIGer(environment)
    return aiger.convert(formula)


class AIGer(DagWalker):
    """Converts a formula into an And-Inverted-Graph."""

    def __init__(self, environment=None):
        DagWalker.__init__(self, env=environment)
        self.mgr = self.env.formula_manager
        self.set_function(self.walk_nop, *op.RELATIONS)
        self.set_function(self.walk_nop, *op.THEORY_OPERATORS)
        self.set_function(self.walk_nop, *op.CONSTANTS)
        self.set_function(self.walk_nop, op.SYMBOL, op.FUNCTION)
        self.set_function(self.walk_quantifier, *op.QUANTIFIERS)

    def convert(self, formula):
        """ Converts the given formula in AIG """
        return self.walk(formula)

    def walk_nop(self, formula, args, **kwargs):
        """We return the Theory subformulae without changes."""
        #pylint: disable=unused-argument
        return formula

    def walk_quantifier(self, formula, args, **kwargs):
        """Recreate the quantifiers, with the rewritten subformula."""
        #pylint: disable=unused-argument
        if formula.is_exists():
            return self.mgr.Exists(formula.quantifier_vars(),
                                   args[0])
        else:
            assert formula.is_forall()
            return self.mgr.ForAll(formula.quantifier_vars(),
                                   args[0])

    def walk_and(self, formula, args, **kwargs):
        return self.mgr.And(*args)

    def walk_not(self, formula, args, **kwargs):
        return self.mgr.Not(args[0])

    def walk_or(self, formula, args, **kwargs):
        """ a1 | ... | an = !( !a1 & ... & !an) """
        return self.mgr.Not(self.mgr.And(self.mgr.Not(s) for s in args))

    def walk_iff(self, formula, args, **kwargs):
        """ a <-> b =  (!a | b) & (!b | a) = !( a & !b ) & !(b & !a)"""
        lhs, rhs = args
        r1 = self.mgr.Not(self.mgr.And(lhs, self.mgr.Not(rhs)))
        r2 = self.mgr.Not(self.mgr.And(rhs, self.mgr.Not(lhs)))
        return self.mgr.And(r1,r2)

    def walk_implies(self, formula, args, **kwargs):
        """ a -> b = !(a & !b) """
        lhs, rhs = args
        return self.mgr.Not(self.mgr.And(lhs, self.mgr.Not(rhs)))

    def walk_ite(self, formula, args, **kwargs):
        """This rewrites only boolean ITE, not theory ones.

            x ? a: b  = (x -> a) & (!x -> b) = !(x & !a) & !(!x & !b)
        """
        i, t, e = args
        if self.env.stc.get_type(t).is_bool_type():
            r1 = self.mgr.Not(self.mgr.And(i, self.mgr.Not(t)))
            r2 = self.mgr.Not(self.mgr.And(self.mgr.Not(i),
                                           self.mgr.Not(e)))
            return self.mgr.And(r1, r2)
        else:
            return formula
