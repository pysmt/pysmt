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


def nnf(formula, environment=None):
    """Converts the given formula in NNF"""
    nnfizer = NNFizer(environment)
    return nnfizer.convert(formula)

class NNFizer(DagWalker):
    """Converts a formula into Negation Normal Form.

    The conversion to NNF is handled in 3 steps.

    1. The function _get_children is extended, so that for each
    expression inside a Not, it will return the effect of propagating
    the Not downwards. For example, for Not(And(a, b)), the function
    will return [Not(a), Not(b)].  For expressions that are not inside
    a Not, it is important to return the same type of arguments. See
    for example the case for Iff.

    2. The usual walk_* function is implemented to rebuild the
    expression. This is called only if the subformula was not negated.

    3. walk_not takes care of rebuilding all negated expressions. For
    example, for Not(And(a, b)), walk_not will return
    Or(Not(a), Not(b)). Notice that args in walk_not contains the
    subexpressions returned by _get_children.  In the above example,
    walk_not will be called with args=[Not(a), Not(b)]. Therefore,
    walk_not only need to change the And into a Not.

    """

    def __init__(self, environment=None):
        DagWalker.__init__(self, env=environment)
        self.mgr = self.env.formula_manager
        self.set_function(self.walk_constant, *op.CONSTANTS)
        self.set_function(self.walk_theory_op, *op.THEORY_OPERATORS)
        self.set_function(self.walk_theory_relation, *op.RELATIONS)

    def convert(self, formula):
        """ Converts the given formula in NNF """
        return self.walk(formula)

    def _get_children(self, formula):
        """Returns the arguments of the node on which an hypotetical recursion
        would be made, possibly negating them.
        """
        mgr = self.mgr
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

        else:
            assert formula.is_symbol() or \
                formula.is_function_application() or \
                formula.is_bool_constant() or \
                formula.is_theory_relation(), str(formula)
            return []

    def walk_not(self, formula, args, **kwargs):
        s = formula.arg(0)
        if s.is_symbol():
            return self.mgr.Not(s)
        elif s.is_not():
            return args[0]
        elif s.is_and():
            return self.mgr.Or(args)
        elif s.is_or():
            return self.mgr.And(args)
        elif s.is_implies():
            return self.mgr.And(args)
        elif s.is_iff():
            a, b, na, nb = args
            return self.mgr.Or(self.mgr.And(a, nb),
                          self.mgr.And(b, na))
        elif s.is_forall():
            return self.mgr.Exists(s.quantifier_vars(), args[0])
        elif s.is_exists():
            return self.mgr.ForAll(s.quantifier_vars(), args[0])
        else:
            return self.mgr.Not(args[0])

    def walk_implies(self, formula, args, **kwargs):
        return self.mgr.Or(args)

    def walk_iff(self, formula, args, **kwargs):
        a, b, na, nb = args
        return self.mgr.And(self.mgr.Or(na, b),
                       self.mgr.Or(nb, a))

    def walk_and(self, formula, args, **kwargs):
        return self.mgr.And(args)

    def walk_or(self, formula, args, **kwargs):
        return self.mgr.Or(args)

    def walk_ite(self, formula, args, **kwargs):
        # This must be a boolean ITE as we never add theory atoms in the stack
        # See self._get_children()
        assert self.env.stc.get_type(formula).is_bool_type()
        i, ni, t, e = args
        return self.mgr.And(self.mgr.Or(ni, t), self.mgr.Or(i, e))

    def walk_forall(self, formula, args, **kwargs):
        return self.mgr.ForAll(formula.quantifier_vars(), args[0])

    def walk_exists(self, formula, args, **kwargs):
        return self.mgr.Exists(formula.quantifier_vars(), args[0])

    def walk_symbol(self, formula, **kwargs):
        return formula

    def walk_function(self, formula, **kwargs):
        return formula

    def walk_constant(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return formula

    def walk_theory_relation(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return formula

    def walk_theory_op(self, formula, **kwargs):
        #pylint: disable=unused-argument
        return None

#EOC NNFizer
