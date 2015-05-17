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

    def walk_symbol(self, formula, args):
        return self.mgr.Symbol(formula.symbol_name(),
                                               formula.symbol_type())

    def walk_real_constant(self, formula, args):
        return self.mgr.Real(formula.constant_value())

    def walk_int_constant(self, formula, args):
        return self.mgr.Int(formula.constant_value())

    def walk_bool_constant(self, formula, args):
        return self.mgr.Bool(formula.constant_value())

    def walk_and(self, formula, args):
        return self.mgr.And(args)

    def walk_or(self, formula, args):
        return self.mgr.Or(args)

    def walk_not(self, formula, args):
        return self.mgr.Not(*args)

    def walk_iff(self, formula, args):
        return self.mgr.Iff(*args)

    def walk_implies(self, formula, args):
        return self.mgr.Implies(*args)

    def walk_equals(self, formula, args):
        return self.mgr.Equals(*args)

    def walk_ite(self, formula, args):
        return self.mgr.Ite(*args)

    def walk_ge(self, formula, args):
        return self.mgr.GE(*args)

    def walk_le(self, formula, args):
        return self.mgr.LE(*args)

    def walk_gt(self, formula, args):
        return self.mgr.GT(*args)

    def walk_lt(self, formula, args):
        return self.mgr.LT(*args)

    def walk_forall(self, formula, args):
        qvars = [self.walk_symbol(v, None) for v in formula.quantifier_vars()]
        return self.mgr.ForAll(qvars, *args)

    def walk_exists(self, formula, args):
        qvars = [self.walk_symbol(v, None) for v in formula.quantifier_vars()]
        return self.mgr.Exists(qvars, *args)

    def walk_plus(self, formula, args):
        return self.mgr.Plus(args)

    def walk_times(self, formula, args):
        return self.mgr.Times(*args)

    def walk_minus(self, formula, args):
        return self.mgr.Minus(*args)

    def walk_function(self, formula, args):
        return self.mgr.Function(formula.function_name(), args)

    def walk_toreal(self, formula, args):
        return self.mgr.ToReal(*args)

    def walk_bv_constant(self, formula, args):
        return self.mgr.BV(formula.constant_value(), formula.bv_width())

    def walk_bv_and(self, formula, args):
        return self.mgr.BVAnd(*args)

    def walk_bv_not(self, formula, args):
        return self.mgr.BVNot(*args)

    def walk_bv_neg(self, formula, args):
        return self.mgr.BVNeg(*args)

    def walk_bv_or(self, formula, args):
        return self.mgr.BVOr(*args)

    def walk_bv_xor(self, formula, args):
        return self.mgr.BVXor(*args)

    def walk_bv_add(self, formula, args):
        return self.mgr.BVAdd(*args)

    def walk_bv_mul(self, formula, args):
        return self.mgr.BVMul(*args)

    def walk_bv_udiv(self, formula, args):
        return self.mgr.BVUDiv(*args)

    def walk_bv_urem(self, formula, args):
        return self.mgr.BVURem(*args)

    def walk_bv_ult(self, formula, args):
        return self.mgr.BVULT(*args)

    def walk_bv_ule(self, formula, args):
        return self.mgr.BVULE(*args)

    def walk_bv_extract(self, formula, args):
        return self.mgr.BVExtract(args[0],
                                  start=formula.bv_extract_start(),
                                  end=formula.bv_extract_end())

    def walk_bv_ror(self, formula, args):
        return self.mgr.BVRor(args[0], formula.bv_rotation_step())

    def walk_bv_rol(self, formula, args):
        return self.mgr.BVRol(args[0], formula.bv_rotation_step())

    def walk_bv_sext(self, formula, args):
        return self.mgr.BVSExt(args[0], formula.bv_extend_step())

    def walk_bv_zext(self, formula, args):
        return self.mgr.BVZExt(args[0], formula.bv_extend_step())

    def walk_bv_concat(self, formula, args):
        return self.mgr.BVConcat(*args)

    def walk_bv_lshl(self, formula, args):
        return self.mgr.BVLShl(*args)

    def walk_bv_lshr(self, formula, args):
        return self.mgr.BVLShr(*args)
