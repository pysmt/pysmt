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
from six import iteritems

import pysmt.walkers
import pysmt.operators as op

class Substituter(pysmt.walkers.DagWalker):

    def __init__(self, env):
        pysmt.walkers.DagWalker.__init__(self, env=env, invalidate_memoization=True)
        self.manager = self.env.formula_manager

        self.set_function(self.walk_identity, op.SYMBOL, op.REAL_CONSTANT,
                          op.INT_CONSTANT, op.BOOL_CONSTANT, op.BV_CONSTANT)


    def substitute(self, formula, subs):
        """Given a map ``subs`` of substitutions, replaces any subformula in
        formula with the corresponding definition in subs.
        """
        # Check that formula is a term
        if not formula.is_term():
            raise TypeError("substitute() can only be used on terms.")

        for (i, k) in enumerate(subs):
            v = subs[k]
            # Check that substitutions are terms
            if not k.is_term():
                raise TypeError(
                    "Only terms should be provided as substitutions." +
                    " Non-term '%s' found." % k)
            if not v.is_term():
                raise TypeError(
                    "Only terms should be provided as substitutions." +
                    " Non-term '%s' found." % v)
            # Check that substitutions belong to the current formula manager
            if k not in self.manager:
                raise TypeError(
                    "Key %d does not belong to the Formula Manager." % i)
            if v not in self.manager:
                raise TypeError(
                    "Value %d does not belong to the Formula Manager." % i)

        return self.walk(formula, substitutions=subs)


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
            sub = Substituter(self.env)
            res_formula = sub.substitute(formula.arg(0), new_subs)

            # 3. We invoke the relevant function (walk_exists or
            #    walk_forall) to compute the substitution
            fun = self.functions[formula.node_type()]
            res = fun(formula, args=[res_formula], **kwargs)

            # 4. We memoize the result
            key = self._get_key(formula, **kwargs)
            self.memoization[key] = res
        else:
            pysmt.walkers.DagWalker._push_with_children_to_stack(self,
                                                                 formula,
                                                                 **kwargs)


    def _substitute(self, formula, subs):
        """Returns the substitution for formula, if one is defined, otherwise
        it defaults to the identify (formula).

        This is an helper function, to simplify the implementation of
        the walk_* functions.
        """

        return subs.get(formula, formula)

    def walk_and(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.And(args), substitutions)

    def walk_or(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.Or(args), substitutions)

    def walk_not(self, formula, args, substitutions, **kwargs):
        assert len(args) == 1
        return self._substitute(self.manager.Not(args[0]), substitutions)

    def walk_equals(self, formula, args, substitutions, **kwargs):
        assert len(args) == 2
        sl = args[0]
        sr = args[1]
        return self._substitute(self.manager.Equals(sl, sr),
                               substitutions)

    def walk_iff(self, formula, args, substitutions, **kwargs):
        assert len(args) == 2
        sl = args[0]
        sr = args[1]
        return self._substitute(self.manager.Iff(sl, sr),
                               substitutions)

    def walk_implies(self, formula, args, substitutions, **kwargs):
        assert len(args) == 2
        sl = args[0]
        sr = args[1]
        return self._substitute(self.manager.Implies(sl, sr),
                               substitutions)

    def walk_ite(self, formula, args, substitutions, **kwargs):
        assert len(args) == 3
        si = args[0]
        st = args[1]
        se = args[2]
        return self._substitute(self.manager.Ite(si, st, se),
                               substitutions)

    def walk_le(self, formula, args, substitutions, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        return  self._substitute(self.manager.LE(sl, sr),
                                substitutions)

    def walk_lt(self, formula, args, substitutions, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        return self._substitute(self.manager.LT(sl, sr),
                               substitutions)


    def walk_plus(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.Plus(args),
                                substitutions)

    def walk_times(self, formula, args, substitutions, **kwargs):
        assert len(args) == 2
        sl = args[0]
        sr = args[1]

        return self._substitute(self.manager.Times(sl, sr), substitutions)

    def walk_minus(self, formula, args, substitutions, **kwargs):
        assert len(args) == 2

        sl = args[0]
        sr = args[1]

        return self._substitute(self.manager.Minus(sl, sr), substitutions)

    def walk_toreal(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.ToReal(args[0]),
                                substitutions)

    def walk_identity(self, formula, args, substitutions, **kwargs):
        assert len(args) == 0
        return self._substitute(formula, substitutions)

    def walk_forall(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.ForAll(formula.quantifier_vars(),
                                                    args[0]),
                                substitutions)

    def walk_exists(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.Exists(formula.quantifier_vars(),
                                                    args[0]),
                                substitutions)

    def walk_function(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.Function(formula.function_name(),
                                                      args),
                                substitutions)

    def walk_bv_not(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVNot(args[0]), substitutions)

    def walk_bv_and(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVAnd(args[0], args[1]),
                                substitutions)

    def walk_bv_or(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVOr(args[0], args[1]),
                                substitutions)

    def walk_bv_xor(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVXor(args[0]), substitutions)

    def walk_bv_concat(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVConcat(args[0], args[1]),
                                substitutions)

    def walk_bv_extract(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVExtract(args[0],
                                                       start=formula.bv_extract_start(),
                                                       end=formula.bv_extract_end()),
                                substitutions)

    def walk_bv_ult(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVULT(args[0], args[1]),
                                substitutions)

    def walk_bv_ule(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVULE(args[0], args[1]),
                                substitutions)

    def walk_bv_neg(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVNeg(args[0]), substitutions)

    def walk_bv_add(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVAdd(args[0], args[1]), substitutions)

    def walk_bv_mul(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVMul(args[0], args[1]), substitutions)

    def walk_bv_udiv(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVUDiv(args[0], args[1]), substitutions)

    def walk_bv_urem(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVURem(args[0], args[1]), substitutions)

    def walk_bv_lshl(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVLShl(args[0], args[1]),
                                substitutions)

    def walk_bv_lshr(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVLShr(args[0], args[1]),
                                substitutions)

    def walk_bv_rol(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVRol(args[0],
                                                   formula.bv_rotation_step()),
                                substitutions)

    def walk_bv_ror(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVRor(args[0],
                                                   formula.bv_rotation_step()),
                                substitutions)

    def walk_bv_zext(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVZExt(args[0],
                                                    formula.bv_extend_step()),
                                substitutions)

    def walk_bv_sext(self, formula, args, substitutions, **kwargs):
        return self._substitute(self.manager.BVSExt(args[0],
                                                    formula.bv_extend_step()),
                                substitutions)


# EOC Substituter
