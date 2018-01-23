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
from pysmt.walkers.dag import DagWalker

class IdentityDagWalker(DagWalker):
    """This class traverses a formula and rebuilds it recursively
    identically.

    This could be useful when only some nodes needs to be rewritten
    but the structure of the formula has to be kept.

    """

    def __init__(self, env=None, invalidate_memoization=None):
        DagWalker.__init__(self,
                           env=env,
                           invalidate_memoization=invalidate_memoization)
        self.mgr = self.env.formula_manager

    def walk_symbol(self, formula, args, **kwargs):
        return self.mgr.Symbol(formula.symbol_name(),
                               formula.symbol_type())

    def walk_real_constant(self, formula, args, **kwargs):
        return self.mgr.Real(formula.constant_value())

    def walk_int_constant(self, formula, args, **kwargs):
        return self.mgr.Int(formula.constant_value())

    def walk_bool_constant(self, formula, args, **kwargs):
        return self.mgr.Bool(formula.constant_value())

    def walk_str_constant(self, formula, **kwargs):
        return self.mgr.String(formula.constant_value())

    def walk_and(self, formula, args, **kwargs):
        return self.mgr.And(args)

    def walk_or(self, formula, args, **kwargs):
        return self.mgr.Or(args)

    def walk_not(self, formula, args, **kwargs):
        return self.mgr.Not(args[0])

    def walk_iff(self, formula, args, **kwargs):
        return self.mgr.Iff(args[0], args[1])

    def walk_implies(self, formula, args, **kwargs):
        return self.mgr.Implies(args[0], args[1])

    def walk_equals(self, formula, args, **kwargs):
        return self.mgr.Equals(args[0], args[1])

    def walk_ite(self, formula, args, **kwargs):
        return self.mgr.Ite(args[0], args[1], args[2])

    def walk_le(self, formula, args, **kwargs):
        return self.mgr.LE(args[0], args[1])

    def walk_lt(self, formula, args, **kwargs):
        return self.mgr.LT(args[0], args[1])

    def walk_forall(self, formula, args, **kwargs):
        qvars = [self.walk_symbol(v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        return self.mgr.ForAll(qvars, args[0])

    def walk_exists(self, formula, args, **kwargs):
        qvars = [self.walk_symbol(v, args, **kwargs)
                 for v in formula.quantifier_vars()]
        return self.mgr.Exists(qvars, args[0])

    def walk_plus(self, formula, args, **kwargs):
        return self.mgr.Plus(args)

    def walk_times(self, formula, args, **kwargs):
        return self.mgr.Times(args)

    def walk_pow(self, formula, args, **kwargs):
        return self.mgr.Pow(args[0], args[1])

    def walk_minus(self, formula, args, **kwargs):
        return self.mgr.Minus(args[0], args[1])

    def walk_function(self, formula, args, **kwargs):
        # We re-create the symbol name
        old_name = formula.function_name()
        new_name = self.walk_symbol(old_name, args, **kwargs)
        return self.mgr.Function(new_name, args)

    def walk_toreal(self, formula, args, **kwargs):
        return self.mgr.ToReal(args[0])

    def walk_bv_constant(self, formula, **kwargs):
        return self.mgr.BV(formula.constant_value(), formula.bv_width())

    def walk_bv_and(self, formula, args, **kwargs):
        return self.mgr.BVAnd(args[0], args[1])

    def walk_bv_not(self, formula, args, **kwargs):
        return self.mgr.BVNot(args[0])

    def walk_bv_neg(self, formula, args, **kwargs):
        return self.mgr.BVNeg(args[0])

    def walk_bv_or(self, formula, args, **kwargs):
        return self.mgr.BVOr(args[0], args[1])

    def walk_bv_xor(self, formula, args, **kwargs):
        return self.mgr.BVXor(args[0], args[1])

    def walk_bv_add(self, formula, args, **kwargs):
        return self.mgr.BVAdd(args[0], args[1])

    def walk_bv_sub(self, formula, args, **kwargs):
        return self.mgr.BVSub(args[0], args[1])

    def walk_bv_mul(self, formula, args, **kwargs):
        return self.mgr.BVMul(args[0], args[1])

    def walk_bv_udiv(self, formula, args, **kwargs):
        return self.mgr.BVUDiv(args[0], args[1])

    def walk_bv_urem(self, formula, args, **kwargs):
        return self.mgr.BVURem(args[0], args[1])

    def walk_bv_ult(self, formula, args, **kwargs):
        return self.mgr.BVULT(args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        return self.mgr.BVULE(args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        return self.mgr.BVExtract(args[0],
                                  start=formula.bv_extract_start(),
                                  end=formula.bv_extract_end())

    def walk_bv_ror(self, formula, args, **kwargs):
        return self.mgr.BVRor(args[0], formula.bv_rotation_step())

    def walk_bv_rol(self, formula, args, **kwargs):
        return self.mgr.BVRol(args[0], formula.bv_rotation_step())

    def walk_bv_sext(self, formula, args, **kwargs):
        return self.mgr.BVSExt(args[0], formula.bv_extend_step())

    def walk_bv_zext(self, formula, args, **kwargs):
        return self.mgr.BVZExt(args[0], formula.bv_extend_step())

    def walk_bv_concat(self, formula, args, **kwargs):
        return self.mgr.BVConcat(args[0], args[1])

    def walk_bv_lshl(self, formula, args, **kwargs):
        return self.mgr.BVLShl(args[0], args[1])

    def walk_bv_lshr(self, formula, args, **kwargs):
        return self.mgr.BVLShr(args[0], args[1])

    def walk_bv_ashr(self, formula, args, **kwargs):
        return self.mgr.BVAShr(args[0], args[1])

    def walk_bv_comp(self, formula, args, **kwargs):
        return self.mgr.BVComp(args[0], args[1])

    def walk_bv_slt(self, formula, args, **kwargs):
        return self.mgr.BVSLT(args[0], args[1])

    def walk_bv_sle(self, formula, args, **kwargs):
        return self.mgr.BVSLE(args[0], args[1])

    def walk_bv_sdiv(self, formula, args, **kwargs):
        return self.mgr.BVSDiv(args[0], args[1])

    def walk_bv_srem(self, formula, args, **kwargs):
        return self.mgr.BVSRem(args[0], args[1])

    def walk_str_length(self, formula, args, **kwargs):
        return self.mgr.StrLength(args[0])

    def walk_str_concat(self, formula, args, **kwargs):
        return self.mgr.StrConcat(args)

    def walk_str_contains(self, formula, args, **kwargs):
        return self.mgr.StrContains(args[0], args[1])

    def walk_str_indexof(self, formula, args, **kwargs):
        return self.mgr.StrIndexOf(args[0], args[1], args[2])

    def walk_str_replace(self, formula, args, **kwargs):
        return self.mgr.StrReplace(args[0], args[1], args[2])

    def walk_str_substr(self, formula, args, **kwargs):
        return self.mgr.StrSubstr(args[0], args[1], args[2])

    def walk_str_prefixof(self, formula, args, **kwargs):
        return self.mgr.StrPrefixOf(args[0], args[1])

    def walk_str_suffixof(self, formula, args, **kwargs):
        return self.mgr.StrSuffixOf(args[0], args[1])

    def walk_str_to_int(self, formula, args, **kwargs):
        return self.mgr.StrToInt(args[0])

    def walk_int_to_str(self, formula, args, **kwargs):
        return self.mgr.IntToStr(args[0])

    def walk_str_charat(self, formula, args, **kwargs):
        return self.mgr.StrCharAt(args[0], args[1])

    def walk_bv_tonatural(self, formula, args, **kwargs):
        return self.mgr.BVToNatural(args[0])

    def walk_array_select(self, formula, args, **kwargs):
        return self.mgr.Select(args[0], args[1])

    def walk_array_store(self, formula, args, **kwargs):
        return self.mgr.Store(args[0], args[1], args[2])

    def walk_array_value(self, formula, args, **kwargs):
        assign = dict(zip(args[1::2], args[2::2]))
        return self.mgr.Array(formula.array_value_index_type(),
                              args[0],
                              assign)

    def walk_div(self, formula, args, **kwargs):
        return self.mgr.Div(args[0], args[1])
