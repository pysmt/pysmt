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
import pysmt.logics

from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.utils import all_assignments
from pysmt.exceptions import InternalSolverError


class QuantifierEliminator(object):

    def __init__(self):
        self._destroyed = False

    def eliminate_quantifiers(self, formula):
        """
        Returns a quantifier-free equivalent formula of the given
        formula

        If explicit_vars is specified, an explicit enumeration of all
        the possible models for such variables is computed and
        quantifier elimination is performed on each disjunct
        separately.
        """
        raise NotImplementedError

    def __enter__(self):
        """ Manage entering a Context (i.e., with statement) """
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """ Manage exiting from Context (i.e., with statement)

        The default behaviour is to explicitely destroy the qelim to free
        the associated resources.
        """
        self.exit()

    def exit(self):
        """Destroys the solver and closes associated resources."""
        if not self._destroyed:
            self._exit()
            self._destroyed = True

    def _exit(self):
        """Destroys the solver and closes associated resources."""
        raise NotImplementedError


class ShannonQuantifierEliminator(QuantifierEliminator, IdentityDagWalker):
    """Quantifier Elimination using Shannon Expansion."""

    LOGICS = [pysmt.logics.BOOL]

    def __init__(self, environment, logic=None):
        IdentityDagWalker.__init__(self, env=environment)
        QuantifierEliminator.__init__(self)
        self.logic = logic

    def eliminate_quantifiers(self, formula):
        return self.walk(formula)

    def _assert_vars_boolean(self, var_set):
        for v in var_set:
            if not v.symbol_type().is_bool_type():
                raise InternalSolverError(
                    "Shannon Quantifier Elimination only supports "\
                    "quantification over Boolean variables: "\
                    "(%s is %s)" % (v, v.symbol_type()))

    def _expand(self, formula, args):
        """Returns the list of elements from the Shannon expansion."""
        qvars = formula.quantifier_vars()
        self._assert_vars_boolean(qvars)
        res = []
        f = args[0]
        for subs in all_assignments(qvars, self.env):
            res.append(f.substitute(subs))
        return res

    def walk_forall(self, formula, args, **kwargs):
        return self.mgr.And(self._expand(formula, args))

    def walk_exists(self, formula, args, **kwargs):
        return self.mgr.Or(self._expand(formula, args))

    def _exit(self):
        pass

# EOC ShannonQuantifierEliminator

class SelfSubstitutionQuantifierEliminator(QuantifierEliminator, IdentityDagWalker):
    """Boolean Quantifier Elimination based on Self-Substitution.

    Described in :
     "BDD-Based Boolean Functional Synthesis",
     Dror Fried, Lucas M. Tabajara, and Moshe Y. Vardi,
     CAV 2016
    """
    LOGICS = [pysmt.logics.BOOL]

    def __init__(self, environment, logic=None):
        IdentityDagWalker.__init__(self, env=environment)
        QuantifierEliminator.__init__(self)
        self.logic = logic

    def eliminate_quantifiers(self, formula):
        return self.walk(formula)

    def self_substitute(self, formula, qvars, token):
        for v in qvars[::-1]:
            inner_sub = formula.substitute({v: token})
            formula = formula.substitute({v: inner_sub})
        return formula

    def walk_forall(self, formula, args, **kwargs):
        """Forall y . f(x, y) =>  f(x, f(x, 0))"""
        qvars = formula.quantifier_vars()
        f = args[0]
        token = self.env.formula_manager.FALSE()
        qf_f = self.self_substitute(f, qvars, token)
        return qf_f

    def walk_exists(self, formula, args, **kwargs):
        """Exists y . f(x, y) =>  f(x, f(x, 1))"""
        qvars = formula.quantifier_vars()
        f = args[0]
        token = self.env.formula_manager.TRUE()
        qf_f = self.self_substitute(f, qvars, token)
        return qf_f

    def _exit(self):
        pass
