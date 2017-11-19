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
import warnings

from six import iteritems

import pysmt.walkers
from pysmt.walkers.generic import handles
import pysmt.operators as op
from pysmt.exceptions import PysmtTypeError


class Substituter(pysmt.walkers.IdentityDagWalker):
    """Performs substitution of a set of terms within a formula.

    Let f be a formula ans subs be a map from formula to formula.
    Substitution returns a formula f' in which all occurrences of the
    keys of the map have been replaced by their value.

    There are a few considerations to take into account:
      - In which order to apply the substitution
      - How to deal with quantified subformulas

    The order in which we apply the substitutions gives raise to two
    different approaches: Most General Substitution and Most Specific
    Substitution. Lets consider the example:

      f = (a & b)
      subs = {a -> c, (c & b) -> d, (a & b) -> c}

    With the Most General Substitution (MGS) we obtain:
      f' = c
    with the Most Specific Substitution (MSS) we obtain:
      f' = d

    The default behavior before version 0.5 was MSS. However, this
    leads to unexpected results when dealing with literals, i.e.,
    substitutions in which both x and Not(x) appear, do not work as
    expected.  In case of doubt, it is recommended to issue two
    separate calls to the substitution procedure.
    """
    def __init__(self, env):
        pysmt.walkers.IdentityDagWalker.__init__(self, env=env, invalidate_memoization=True)
        self.manager = self.env.formula_manager
        if self.__class__ == Substituter:
            raise NotImplementedError(
                "Cannot instantiate abstract Substituter class directly. "
                "Use MSSubstituter or MGSubstituter instead.")

    def _get_key(self, formula, **kwargs):
        return formula

    def _push_with_children_to_stack(self, formula, **kwargs):
        """Add children to the stack."""

        # Deal with quantifiers
        if formula.is_quantifier():
            # 1. We create a new substitution in which we remove the
            #    bound variables from the substitution map
            substitutions = kwargs["substitutions"]
            new_subs = {}
            for k,v in iteritems(substitutions):
                # If at least one bound variable is in the cone of k,
                # we do not consider this substitution in the body of
                # the quantifier.
                if all(m not in formula.quantifier_vars()
                       for m in k.get_free_variables()):
                    new_subs[k] = v

            # 2. We apply the substitution on the quantifier body with
            #    the new 'reduced' map
            sub = self.__class__(self.env)
            res_formula = sub.substitute(formula.arg(0), new_subs)

            # 3. We invoke the relevant function (walk_exists or
            #    walk_forall) to compute the substitution
            fun = self.functions[formula.node_type()]
            res = fun(formula, args=[res_formula], **kwargs)

            # 4. We memoize the result
            key = self._get_key(formula, **kwargs)
            self.memoization[key] = res
        else:
            pysmt.walkers.IdentityDagWalker._push_with_children_to_stack(self,
                                                                         formula,
                                                                         **kwargs)

    def substitute(self, formula, subs):
        """Replaces any subformula in formula with the definition in subs."""

        # Check that formula is a term
        if not formula.is_term():
            raise PysmtTypeError("substitute() can only be used on terms.")

        for (i, k) in enumerate(subs):
            v = subs[k]
            # Check that substitutions are terms
            if not k.is_term():
                raise PysmtTypeError(
                    "Only terms should be provided as substitutions." +
                    " Non-term '%s' found." % k)
            if not v.is_term():
                raise PysmtTypeError(
                    "Only terms should be provided as substitutions." +
                    " Non-term '%s' found." % v)
            # Check that substitutions belong to the current formula manager
            if k not in self.manager:
                raise PysmtTypeError(
                    "Key %d does not belong to the Formula Manager." % i)
            if v not in self.manager:
                raise PysmtTypeError(
                    "Value %d does not belong to the Formula Manager." % i)

        res = self.walk(formula, substitutions=subs)
        return res


class MGSubstituter(Substituter):
    """Performs Most Generic Substitution.

    This is the default behavior since version 0.5
    """
    def __init__(self, env):
        Substituter.__init__(self, env=env)

    @handles(set(op.ALL_TYPES) - op.QUANTIFIERS)
    def walk_identity_or_replace(self, formula, args, **kwargs):
        """
        If the formula appears in the substitution, return the substitution.
        Otherwise, rebuild the formula by calling the IdentityWalker.
        """
        substitutions = kwargs['substitutions']
        if formula in substitutions:
            res = substitutions[formula]
        else:
            res = Substituter.super(self, formula, args=args, **kwargs)
        return res

    def walk_forall(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        if formula in substitutions:
            res = substitutions[formula]
        else:
            qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                     for v in formula.quantifier_vars()]
            res = self.mgr.ForAll(qvars, args[0])
        return res

    def walk_exists(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        if formula in substitutions:
            res = substitutions[formula]
        else:
            qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                     for v in formula.quantifier_vars()]
            res = self.mgr.Exists(qvars, args[0])
        return res


# EOC MGSubstituter


class MSSubstituter(Substituter):
    """Performs Most Specific Substitution.

    This was the default beahvior before version 0.5
    """

    def __init__(self, env):
        Substituter.__init__(self, env=env)

    def substitute(self, formula, subs):
        return Substituter.substitute(self, formula, subs)

    def _substitute(self, formula, substitutions):
        """Returns the substitution for formula, if one is defined, otherwise
        returns the formula unchanged.

        This is an helper function, to simplify the implementation of
        the walk_* functions.
        """
        return substitutions.get(formula, formula)

    @handles(set(op.ALL_TYPES) - op.QUANTIFIERS)
    def walk_replace(self, formula, args, **kwargs):
        new_f =  Substituter.super(self, formula, args=args, **kwargs)
        return self._substitute(new_f, kwargs['substitutions'])

    def walk_forall(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        new_f = self.mgr.ForAll(qvars, args[0])
        return self._substitute(new_f, substitutions)

    def walk_exists(self, formula, args, **kwargs):
        substitutions = kwargs['substitutions']
        qvars = [pysmt.walkers.IdentityDagWalker.walk_symbol(self, v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        new_f = self.mgr.Exists(qvars, args[0])
        return self._substitute(new_f, substitutions)

# EOC MSSSubstituter
