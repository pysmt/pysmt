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
import re

from warnings import warn
from fractions import Fraction
from six.moves import xrange

from pysmt.exceptions import SolverAPINotFound

try:
    import opensmt
except ImportError:
    raise SolverAPINotFound

from pysmt.logics import (QF_UF, QF_BV, QF_RDL, QF_IDL, QF_LRA, QF_LIA, QF_UFIDL,
                          QF_UFLRA, QF_BOOL)
from pysmt.oracles import get_logic

import pysmt.operators as op
from pysmt import typing as types
from pysmt.solvers.solver import Solver, Converter
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.walkers import DagWalker
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              SolverNotConfiguredForUnsatCoresError,
                              SolverStatusError,
                              InternalSolverError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.solvers.qelim import QuantifierEliminator
from pysmt.solvers.interpolation import Interpolator
from pysmt.walkers.identitydag import IdentityDagWalker


class OSmtContext(object):
    """A wrapper for the osmt_context object.

    Objects within pySMT should only reference the opensmt context
    through this object. When calling a function from the underlying
    wrapper, the inner instance of osmt_ctx needs to be used.
    This is done using the __call__ method: e.g.,
       ctx = OSmtContext()
       osmt.function(ctx())
    """
    __slots__ = ['osmt_context']

    def __init__(self, osmt_logic=None):
        if osmt_logic is None:
            osmt_logic = opensmt.qf_uf
        self.osmt_context = opensmt.mkContext(osmt_logic)

    def __del__(self):
        opensmt.osmt_del_context(self.osmt_context)

    def __call__(self):
        return self.osmt_context


class OpenSMT2Solver(Solver, SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = [QF_BOOL]

    def __init__(self, environment, logic, **options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        **options)
        #MG: TODO: Properly convert the logic
        if logic == QF_BOOL:
            logic = opensmt.qf_uf
        self.osmt_ctx = OSmtContext(logic)
        self.mgr = environment.formula_manager
        self.converter = OSmtConverter(environment,
                                       self.osmt_ctx)

    @clear_pending_pop
    def _reset_assertions(self):
        opensmt.osmt_reset(self.osmt_ctx())

    @clear_pending_pop
    def declare_variable(self, var):
        self.converter.declare_variable(var)

    @clear_pending_pop
    def add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        assert named is None, "Named assertions are not implemented"
        term = self.converter.convert(formula)
        # MG: It would be better if push would return errors instead of void
        opensmt.push(self.osmt_ctx(), term)
        opensmt.printTerm(self.osmt_ctx(), term)

    @clear_pending_pop
    def solve(self, assumptions=None):
        if assumptions is not None:
            assumption = self.mgr.And(assumptions)
            self.add_assertion(assumption)
            self.push()
            self.pending_pop = True
        res = opensmt.check(self.osmt_ctx())

        assert res in [opensmt.l_true, opensmt.l_false, opensmt.l_undef]
        if res == opensmt.l_undef:
            raise SolverReturnedUnknownResultError
        if res == opensmt.l_true:
            print("Formula is True")
            return True
        else:
            return False

    @clear_pending_pop
    def push(self, levels=1):
        true_ = opensmt.mkTrue(self.osmt_ctx())
        for _ in xrange(levels):
            opensmt.push(self.osmt_ctx(), true_)

    @clear_pending_pop
    def pop(self, levels=1):
        for _ in xrange(levels):
            opensmt.pop(self.osmt_ctx())

    def print_model(self, name_filter=None):
        if name_filter is not None:
            raise NotImplementedError
        for v in self.converter.symbol_to_decl.keys():
            var = self.mgr.Symbol(v)
            assert var is not None
            print("%s = %s", (v, self.get_value(var)))

    def get_value(self, item):
        self._assert_no_function_type(item)

        titem = self.converter.convert(item)
        tval = opensmt.osmt_get_value(self.osmt_ctx(), titem)
        # MG: Back conversion of constants is missing
        raise NotImplementedError

    def get_model(self):
        #MG: Need to look into osmt_get_model, or use EagerModel
        raise NotImplementedError()

    def _exit(self):
        del self.osmt_ctx


class OSmtConverter(Converter, DagWalker):

    def __init__(self, environment, osmt_ctx):
        DagWalker.__init__(self, environment)

        self.osmt_ctx = osmt_ctx
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type

        # Maps a Symbol into the corresponding osmt_decl instance in the osmt_ctx
        self.symbol_to_decl = {}
        # Maps a osmt_decl instance inside the osmt_ctx into the corresponding
        # Symbol
        self.decl_to_symbol = {}
        self.back_memoization = {}

    def back(self, expr):
        return self._walk_back(expr, self.mgr)

    # def _most_generic(self, ty1, ty2):
    #     """Returns the most generic, yet compatible type between ty1 and ty2"""
    #     if ty1 == ty2:
    #         return ty1

    #     assert ty1 in [types.REAL, types.INT]
    #     assert ty2 in [types.REAL, types.INT]
    #     return types.REAL

    # def _get_signature(self, term, args):
    #     """Returns the signature of the given term.
    #     For example:
    #     - a term x & y returns a function type Bool -> Bool -> Bool,
    #     - a term 14 returns Int
    #     - a term x ? 13 : 15.0 returns Bool -> Real -> Real -> Real
    #     """
    #     res = None

    #     if term_is_true(self.osmt_ctx(), term) or \
    #         term_is_false(self.osmt_ctx(), term) or \
    #         term_is_boolean_constant(self.osmt_ctx(), term):
    #         res = types.BOOL

    #     elif term_is_number(self.osmt_ctx(), term):
    #         ty = term_get_type(term)
    #         if is_integer_type(self.osmt_ctx(), ty):
    #             res = types.INT
    #         elif is_rational_type(self.osmt_ctx(), ty):
    #             res = types.REAL
    #         else:
    #             assert "_" in str(term), "Unrecognized type for '%s'" % str(term)
    #             width = int(str(term).split("_")[1])
    #             res = types.BVType(width)

    #     elif term_is_and(self.osmt_ctx(), term) or \
    #          term_is_or(self.osmt_ctx(), term) or \
    #          term_is_iff(self.osmt_ctx(), term):
    #         res = types.FunctionType(types.BOOL, [types.BOOL, types.BOOL])

    #     elif term_is_not(self.osmt_ctx(), term):
    #         res = types.FunctionType(types.BOOL, [types.BOOL])

    #     elif term_is_term_ite(self.osmt_ctx(), term):
    #         t1 = self.env.stc.get_type(args[1])
    #         t2 = self.env.stc.get_type(args[2])
    #         t = self._most_generic(t1, t2)
    #         res = types.FunctionType(t, [types.BOOL, t, t])

    #     elif term_is_equal(self.osmt_ctx(), term) or \
    #          term_is_leq(self.osmt_ctx(), term):
    #         t1 = self.env.stc.get_type(args[0])
    #         t2 = self.env.stc.get_type(args[1])
    #         t = self._most_generic(t1, t2)
    #         res = types.FunctionType(types.BOOL, [t, t])

    #     elif term_is_plus(self.osmt_ctx(), term) or \
    #          term_is_times(self.osmt_ctx(), term):
    #         t1 = self.env.stc.get_type(args[0])
    #         t2 = self.env.stc.get_type(args[1])
    #         t = self._most_generic(t1, t2)
    #         res = types.FunctionType(t, [t, t])

    #     elif term_is_constant(self.osmt_ctx(), term):
    #         ty = term_get_type(term)
    #         return self._osmt_type_to_type(ty)

    #     elif term_is_uf(self.osmt_ctx(), term):
    #         d = term_get_decl(term)
    #         fun = self.get_symbol_from_declaration(d)
    #         res = fun.symbol_type()

    #     elif term_is_bv_times(self.osmt_ctx(), term) or \
    #          term_is_bv_plus(self.osmt_ctx(), term) or \
    #          term_is_bv_minus(self.osmt_ctx(), term) or \
    #          term_is_bv_or(self.osmt_ctx(), term) or \
    #          term_is_bv_and(self.osmt_ctx(), term) or \
    #          term_is_bv_lshl(self.osmt_ctx(), term) or \
    #          term_is_bv_lshr(self.osmt_ctx(), term) or \
    #          term_is_bv_ashr(self.osmt_ctx(), term) or \
    #          term_is_bv_xor(self.osmt_ctx(), term) or \
    #          term_is_bv_urem(self.osmt_ctx(), term) or \
    #          term_is_bv_udiv(self.osmt_ctx(), term) or \
    #          term_is_bv_sdiv(self.osmt_ctx(), term) or \
    #          term_is_bv_srem(self.osmt_ctx(), term) or \
    #          term_is_bv_concat(self.osmt_ctx(), term):
    #         t = self.env.stc.get_type(args[0])
    #         res = types.FunctionType(t, [t, t])

    #     elif term_is_bv_not(self.osmt_ctx(), term) or \
    #          term_is_bv_neg(self.osmt_ctx(), term):
    #         t = self.env.stc.get_type(args[0])
    #         res = types.FunctionType(t, [t])

    #     elif term_is_bv_ult(self.osmt_ctx(), term) or \
    #          term_is_bv_slt(self.osmt_ctx(), term) or \
    #          term_is_bv_uleq(self.osmt_ctx(), term) or \
    #          term_is_bv_sleq(self.osmt_ctx(), term):
    #         t = self.env.stc.get_type(args[0])
    #         res = types.FunctionType(types.BOOL, [t, t])

    #     elif term_is_bv_comp(self.osmt_ctx(), term):
    #         t = self.env.stc.get_type(args[0])
    #         res = types.FunctionType(types.BVType(1), [t, t])

    #     elif term_is_bv_rol(self.osmt_ctx(), term)[0] or \
    #          term_is_bv_ror(self.osmt_ctx(), term)[0]:
    #         t = self.env.stc.get_type(args[0])
    #         res = types.FunctionType(t, [t])

    #     elif term_is_bv_sext(self.osmt_ctx(), term)[0]:
    #         _, amount = term_is_bv_sext(self.osmt_ctx(), term)
    #         t = self.env.stc.get_type(args[0])
    #         res = types.FunctionType(types.BVType(amount + t.width), [t])

    #     elif term_is_bv_zext(self.osmt_ctx(), term)[0]:
    #         _, amount = term_is_bv_zext(self.osmt_ctx(), term)
    #         t = self.env.stc.get_type(args[0])
    #         res = types.FunctionType(types.BVType(amount + t.width), [t])

    #     elif term_is_bv_extract(self.osmt_ctx(), term)[0]:
    #         _, msb, lsb = term_is_bv_extract(self.osmt_ctx(), term)
    #         t = self.env.stc.get_type(args[0])
    #         res = types.FunctionType(types.BVType(msb - lsb + 1), [t])

    #     elif term_is_array_read(self.osmt_ctx(), term):
    #         t1 = self.env.stc.get_type(args[0])
    #         t2 = self.env.stc.get_type(args[1])
    #         t = t1.elem_type
    #         res = types.FunctionType(t, [t1, t2])

    #     elif term_is_array_write(self.osmt_ctx(), term):
    #         t1 = self.env.stc.get_type(args[0])
    #         t2 = self.env.stc.get_type(args[1])
    #         t3 = self.env.stc.get_type(args[2])
    #         res = types.FunctionType(t1, [t1, t2, t3])

    #     elif term_is_array_const(self.osmt_ctx(), term):
    #         ty = term_get_type(term)
    #         pyty = self._osmt_type_to_type(ty)
    #         return types.FunctionType(pyty, [self.env.stc.get_type(args[0])])

    #     else:
    #         raise TypeError("Unsupported expression:",
    #                         term_repr(term))
    #     return res

    # def _back_single_term(self, term, mgr, args):
    #     """Builds the pysmt formula given a term and the list of formulae
    #     obtained by converting the term children.

    #     :param term: The Opensmt term to be transformed in pysmt formulae
    #     :type term: Opensmt term

    #     :param mgr: The formula manager to be sued to build the
    #     formulae, it should allow for type unsafety.
    #     :type mgr: Formula manager

    #     :param args: List of the pysmt formulae obtained by converting
    #     all the args (obtained by term_get_arg()) to
    #     pysmt formulae
    #     :type args: List of pysmt formulae

    #     :returns The pysmt formula representing the given term
    #     :rtype Pysmt formula
    #     """
    #     res = None
    #     arity = len(args)

    #     if term_is_true(self.osmt_ctx(), term):
    #         res = mgr.TRUE()

    #     elif term_is_false(self.osmt_ctx(), term):
    #         res = mgr.FALSE()

    #     elif term_is_number(self.osmt_ctx(), term):
    #         ty = term_get_type(term)
    #         if is_integer_type(self.osmt_ctx(), ty):
    #             res = mgr.Int(int(term_repr(term)))
    #         elif is_rational_type(self.osmt_ctx(), ty):
    #             res = mgr.Real(Fraction(term_repr(term)))
    #         else:
    #             assert "_" in str(term), "Unsupported type for '%s'" % str(term)
    #             val, width = str(term).split("_")
    #             val = int(val)
    #             width = int(width)
    #             res = mgr.BV(val, width)

    #     elif term_is_and(self.osmt_ctx(), term):
    #         res = mgr.And(args)

    #     elif term_is_or(self.osmt_ctx(), term):
    #         res = mgr.Or(args)

    #     elif term_is_not(self.osmt_ctx(), term):
    #         assert arity == 1
    #         res = mgr.Not(args[0])

    #     elif term_is_iff(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.Iff(args[0], args[1])

    #     elif term_is_term_ite(self.osmt_ctx(), term):
    #         assert arity == 3
    #         res = mgr.Ite(args[0], args[1], args[2])

    #     elif term_is_equal(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.Equals(args[0], args[1])

    #     elif term_is_leq(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.LE(args[0], args[1])

    #     elif term_is_plus(self.osmt_ctx(), term):
    #         res = mgr.Plus(args)

    #     elif term_is_times(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.Times(args[0], args[1])

    #     elif term_is_boolean_constant(self.osmt_ctx(), term):
    #         rep = term_repr(term)
    #         res = mgr.Symbol(rep, types.BOOL)

    #     elif term_is_constant(self.osmt_ctx(), term):
    #         rep = term_repr(term)

    #         ty = term_get_type(term)
    #         if is_rational_type(self.osmt_ctx(), ty):
    #             res = mgr.Symbol(rep, types.REAL)
    #         elif is_integer_type(self.osmt_ctx(), ty):
    #             res = mgr.Symbol(rep, types.INT)
    #         else:
    #             check_arr, idx_type, val_type = is_array_type(self.osmt_ctx(), ty)
    #             if check_arr:
    #                 i = self._osmt_type_to_type(idx_type)
    #                 e = self._osmt_type_to_type(val_type)
    #                 res = mgr.Symbol(rep, types.ArrayType(i, e))
    #             else:
    #                 _, width = is_bv_type(self.osmt_ctx(), ty)
    #                 assert width is not None, "Unsupported variable type for '%s'"%str(term)
    #                 res = mgr.Symbol(rep, types.BVType(width))

    #     elif term_is_uf(self.osmt_ctx(), term):
    #         d = term_get_decl(term)
    #         fun = self.get_symbol_from_declaration(d)
    #         res = mgr.Function(fun, args)

    #     elif term_is_bv_times(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVMul(args[0], args[1])

    #     elif term_is_bv_plus(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVAdd(args[0], args[1])

    #     elif term_is_bv_udiv(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVUDiv(args[0], args[1])

    #     elif term_is_bv_urem(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVURem(args[0], args[1])

    #     elif term_is_bv_extract(self.osmt_ctx(), term)[0]:
    #         assert arity == 1
    #         res, msb, lsb = term_is_bv_extract(self.osmt_ctx(), term)
    #         assert res
    #         res = mgr.BVExtract(args[0], lsb, msb)

    #     elif term_is_bv_concat(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVConcat(args[0], args[1])

    #     elif term_is_bv_or(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVOr(args[0], args[1])

    #     elif term_is_bv_xor(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVXor(args[0], args[1])

    #     elif term_is_bv_and(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVAnd(args[0], args[1])

    #     elif term_is_bv_not(self.osmt_ctx(), term):
    #         assert arity == 1
    #         res = mgr.BVNot(args[0])

    #     elif term_is_bv_minus(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVSub(args[0], args[1])

    #     elif term_is_bv_neg(self.osmt_ctx(), term):
    #         assert arity == 1
    #         res = mgr.BVSub(args[0])

    #     elif term_is_bv_srem(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVSRem(args[0], args[1])

    #     elif term_is_bv_sdiv(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVSDiv(args[0], args[1])

    #     elif term_is_bv_ult(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVULT(args[0], args[1])

    #     elif term_is_bv_slt(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVSLT(args[0], args[1])

    #     elif term_is_bv_uleq(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVULE(args[0], args[1])

    #     elif term_is_bv_sleq(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVSLE(args[0], args[1])

    #     elif term_is_bv_lshl(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVLShl(args[0], args[1])

    #     elif term_is_bv_lshr(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVLShr(args[0], args[1])

    #     elif term_is_bv_ashr(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVAShr(args[0], args[1])

    #     elif term_is_bv_comp(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.BVComp(args[0], args[1])

    #     elif term_is_bv_zext(self.osmt_ctx(), term)[0]:
    #         assert arity == 2
    #         res, amount = term_is_bv_zext(self.osmt_ctx(), term)
    #         assert res
    #         res = mgr.BVZExt(args[0], amount)

    #     elif term_is_bv_sext(self.osmt_ctx(), term)[0]:
    #         assert arity == 2
    #         res, amount = term_is_bv_sext(self.osmt_ctx(), term)
    #         assert res
    #         res = mgr.BVSExt(args[0], amount)

    #     elif term_is_bv_rol(self.osmt_ctx(), term)[0]:
    #         assert arity == 2
    #         res, amount = term_is_bv_ror(self.osmt_ctx(), term)
    #         assert res
    #         res = mgr.BVRol(args[0], amount)

    #     elif term_is_bv_ror(self.osmt_ctx(), term)[0]:
    #         assert arity == 2
    #         res, amount = term_is_bv_ror(self.osmt_ctx(), term)
    #         assert res
    #         res = mgr.BVRor(args[0], amount)

    #     elif term_is_array_read(self.osmt_ctx(), term):
    #         assert arity == 2
    #         res = mgr.Select(args[0], args[1])

    #     elif term_is_array_write(self.osmt_ctx(), term):
    #         assert arity == 3
    #         res = mgr.Store(args[0], args[1], args[2])

    #     elif term_is_array_const(self.osmt_ctx(), term):
    #         ty = term_get_type(term)
    #         pyty = self._osmt_type_to_type(ty)
    #         res = mgr.Array(pyty.index_type, args[0])

    #     else:
    #         raise TypeError("Unsupported expression:",
    #                         term_repr(term))
    #     return res

    def get_symbol_from_declaration(self, decl):
        return self.decl_to_symbol[decl_id(decl)]

    # def _walk_back(self, term, mgr):
    #     stack = [term]

    #     while len(stack) > 0:
    #         current = stack.pop()
    #         arity = term_arity(current)
    #         if current not in self.back_memoization:
    #             self.back_memoization[current] = None
    #             stack.append(current)
    #             for i in xrange(arity):
    #                 son = term_get_arg(current, i)
    #                 stack.append(son)
    #         elif self.back_memoization[current] is None:
    #             args=[self.back_memoization[term_get_arg(current,i)]
    #                   for i in xrange(arity)]

    #             signature = self._get_signature(current, args)
    #             new_args = []
    #             for i, a in enumerate(args):
    #                 t = self.env.stc.get_type(a)
    #                 if t != signature.param_types[i]:
    #                     a = mgr.ToReal(a)
    #                 new_args.append(a)
    #             res = self._back_single_term(current, mgr, new_args)
    #             self.back_memoization[current] = res
    #         else:
    #             # we already visited the node, nothing else to do
    #             pass
    #     return self.back_memoization[term]

    @catch_conversion_error
    def convert(self, formula):
        """Convert a PySMT formula into a OpenSMT Term.

        This function might throw a InternalSolverError exception if
        an error during conversion occurs.
        """
        return self.walk(formula)

    def walk_and(self, formula, args, **kwargs):
        return opensmt.mkAnd(self.osmt_ctx(), args)

    def walk_or(self, formula, args, **kwargs):
        return opensmt.mkOr(self.osmt_ctx(), args)

    def walk_not(self, formula, args, **kwargs):
        return opensmt.mkNot(self.osmt_ctx(), args[0])

    def walk_symbol(self, formula, **kwargs):
        if not formula.is_symbol(): raise TypeError(formula)
        ty = formula.symbol_type()
        if ty.is_bool_type():
            return opensmt.mkBool(self.osmt_ctx(), formula.symbol_name())
        elif ty.is_real_type():
            return opensmt.mkReal(self.osmt_ctx(), formula.symbol_name())
        elif ty.is_int_type():
            raise NotImplementedError

    def walk_le(self, formula, args, **kwargs):
        return opensmt.mkLeq(self.osmt_ctx(), args[0], args[1])

    def walk_lt(self, formula, args, **kwargs):
        return opensmt.mkLt(self.osmt_ctx(), args[1], args[0])

    def walk_ite(self, formula, args, **kwargs):
        i = args[0]
        t = args[1]
        e = args[2]
        return opensmt.mkIte(self.osmt_ctx(), i, t, e)

    def walk_real_constant(self, formula, **kwargs):
        assert type(formula.constant_value()) == Fraction
        frac = formula.constant_value()
        return opensmt.mkNum(self.osmt_ctx(), frac)

    def walk_int_constant(self, formula, **kwargs):
        assert type(formula.constant_value()) == int or \
            type(formula.constant_value()) == long
        rep = str(formula.constant_value())
        return opensmt.mkNum(self.osmt_ctx(), rep)

    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return opensmt.mkTrue(self.osmt_ctx())
        else:
            return opensmt.mkFalse(self.osmt_ctx())

    def walk_plus(self, formula, args, **kwargs):
        res = args[0]
        for a in args[1:]:
            res = opensmt.mkPlus(self.osmt_ctx(), res, a)
        return res

    def walk_minus(self, formula, args, **kwargs):
        return opensmt.mkMinus(self.osmt_ctx(), args[0], args[1])

    def walk_equals(self, formula, args, **kwargs):
        return opensmt.mkEq(self.osmt_ctx(), args[0], args[1])

    def walk_iff(self, formula, args, **kwargs):
        return opensmt.mkEq(self.osmt_ctx(), args[0], args[1])

    def walk_implies(self, formula, args, **kwargs):
        return opensmt.mkImpl(self.osmt_ctx(), args[0], args[1])

    def walk_times(self, formula, args, **kwargs):
        return opensmt.mkTimes(self.osmt_ctx(), args[0], args[1])

    def walk_function(self, formula, args, **kwargs):
        raise NotImplementedError
