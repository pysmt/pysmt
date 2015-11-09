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
from __future__ import absolute_import

from pysmt.exceptions import SolverAPINotFound

try:
    import z3
except ImportError:
    raise SolverAPINotFound

from fractions import Fraction
from six.moves import xrange

from pysmt.solvers.solver import (IncrementalTrackingSolver, UnsatCoreSolver,
                                  Model, Converter)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.qelim import QuantifierEliminator
from pysmt.solvers.interpolation import Interpolator

from pysmt.walkers import DagWalker
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              SolverNotConfiguredForUnsatCoresError,
                              SolverStatusError,
                              ConvertExpressionError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.logics import LRA, LIA, QF_UFLIA, QF_UFLRA, PYSMT_LOGICS
from pysmt.oracles import get_logic


# patch z3api
z3.is_ite = lambda x: z3.is_app_of(x, z3.Z3_OP_ITE)
z3.is_implies = lambda x: z3.is_app_of(x, z3.Z3_OP_IMPLIES)
z3.is_function = lambda x: z3.is_app_of(x, z3.Z3_OP_UNINTERPRETED)
z3.is_iff = lambda x: z3.is_app_of(x, z3.Z3_OP_IFF)
z3.is_uminus = lambda x: z3.is_app_of(x, z3.Z3_OP_UMINUS)
z3.is_xor = lambda x: z3.is_app_of(x, z3.Z3_OP_XOR)

z3.is_bv_and = lambda x: z3.is_app_of(x, z3.Z3_OP_BAND)
z3.is_bv_or = lambda x: z3.is_app_of(x, z3.Z3_OP_BOR)
z3.is_bv_xor = lambda x: z3.is_app_of(x, z3.Z3_OP_BXOR)
z3.is_bv_neg = lambda x: z3.is_app_of(x, z3.Z3_OP_BNEG)
z3.is_bv_not = lambda x: z3.is_app_of(x, z3.Z3_OP_BNOT)
z3.is_bv_concat = lambda x: z3.is_app_of(x, z3.Z3_OP_CONCAT)
z3.is_bv_slt = lambda x: z3.is_app_of(x, z3.Z3_OP_SLT)
z3.is_bv_sleq = lambda x: z3.is_app_of(x, z3.Z3_OP_SLEQ)
z3.is_bv_ult = lambda x: z3.is_app_of(x, z3.Z3_OP_ULT)
z3.is_bv_uleq = lambda x: z3.is_app_of(x, z3.Z3_OP_ULEQ)
z3.is_bv_sgt = lambda x: z3.is_app_of(x, z3.Z3_OP_SLT)
z3.is_bv_sgeq = lambda x: z3.is_app_of(x, z3.Z3_OP_SLEQ)
z3.is_bv_ugt = lambda x: z3.is_app_of(x, z3.Z3_OP_ULT)
z3.is_bv_ugeq = lambda x: z3.is_app_of(x, z3.Z3_OP_ULEQ)
z3.is_bv_extract = lambda x: z3.is_app_of(x, z3.Z3_OP_EXTRACT)
z3.is_bv_add = lambda x: z3.is_app_of(x, z3.Z3_OP_BADD)
z3.is_bv_mul = lambda x: z3.is_app_of(x, z3.Z3_OP_BMUL)
z3.is_bv_udiv = lambda x: z3.is_app_of(x, z3.Z3_OP_BUDIV)
z3.is_bv_sdiv = lambda x: z3.is_app_of(x, z3.Z3_OP_BSDIV)
z3.is_bv_urem = lambda x: z3.is_app_of(x, z3.Z3_OP_BUREM)
z3.is_bv_srem = lambda x: z3.is_app_of(x, z3.Z3_OP_BSREM)
z3.is_bv_lshl = lambda x: z3.is_app_of(x, z3.Z3_OP_BSHL)
z3.is_bv_lshr = lambda x: z3.is_app_of(x, z3.Z3_OP_BLSHR)
z3.is_bv_ashr = lambda x: z3.is_app_of(x, z3.Z3_OP_BASHR)
z3.is_bv_sub = lambda x: z3.is_app_of(x, z3.Z3_OP_BSUB)
z3.is_bv_rol = lambda x: z3.is_app_of(x, z3.Z3_OP_ROTATE_LEFT)
z3.is_bv_ror = lambda x: z3.is_app_of(x, z3.Z3_OP_ROTATE_RIGHT)
z3.is_bv_ext_rol = lambda x: z3.is_app_of(x, z3.Z3_OP_EXT_ROTATE_LEFT)
z3.is_bv_ext_ror = lambda x: z3.is_app_of(x, z3.Z3_OP_EXT_ROTATE_RIGHT)
z3.is_bv_zext = lambda x: z3.is_app_of(x, z3.Z3_OP_ZERO_EXT)
z3.is_bv_sext = lambda x: z3.is_app_of(x, z3.Z3_OP_SIGN_EXT)

z3.get_payload = lambda node,i : z3.Z3_get_decl_int_parameter(node.ctx.ref(),
                                                              node.decl().ast, i)


class AstRefKey:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return self.n.hash()
    def __eq__(self, other):
        return self.n.eq(other.n)

def askey(n):
    assert isinstance(n, z3.AstRef)
    return AstRefKey(n)



class Z3Model(Model):

    def __init__(self, environment, z3_model):
        Model.__init__(self, environment)
        self.z3_model = z3_model
        self.converter = Z3Converter(environment)

    def get_value(self, formula, model_completion=True):
        titem = self.converter.convert(formula)
        z3_res = self.z3_model.eval(titem, model_completion=model_completion)
        return self.converter.back(z3_res)

    def iterator_over(self, language):
        for x in language:
            yield x, self.get_value(x, model_completion=True)

    def __iter__(self):
        """Overloading of iterator from Model.  We iterate only on the
        variables defined in the assignment.
        """
        for d in self.z3_model.decls():
            if d.arity() == 0:
                try:
                    pysmt_d = self.converter.back(d())
                    yield pysmt_d, self.get_value(pysmt_d)
                except ConvertExpressionError:
                    # avoids problems with symbols generated by z3
                    pass

    def __contains__(self, x):
        """Returns whether the model contains a value for 'x'."""
        return x in (v for v, _ in self)



class Z3Solver(IncrementalTrackingSolver, UnsatCoreSolver,
               SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = PYSMT_LOGICS

    def __init__(self, environment, logic, user_options):
        IncrementalTrackingSolver.__init__(self,
                                           environment=environment,
                                           logic=logic,
                                           user_options=user_options)
        # Here we could use:
        # self.z3 = z3.SolverFor(str(logic))
        # But it seems to have problems with quantified formulae
        self.z3 = z3.Solver()

        if self.options.unsat_cores_mode is not None:
            self.z3.set(unsat_core=True)

        self.declarations = set()
        self.converter = Z3Converter(environment)
        self.mgr = environment.formula_manager

        self._name_cnt = 0
        return

    @clear_pending_pop
    def _reset_assertions(self):
        self.z3.reset()

    @clear_pending_pop
    def declare_variable(self, var):
        self.declarations.add(var)
        return

    @clear_pending_pop
    def _add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)

        if self.options.unsat_cores_mode is not None:
            key = self.mgr.FreshSymbol(template="_assertion_%d")
            tkey = self.converter.convert(key)
            self.z3.assert_and_track(term, tkey)
            return (key, named, formula)
        else:
            self.z3.add(term)
            return formula

    def get_model(self):
        return Z3Model(self.environment, self.z3.model())

    @clear_pending_pop
    def _solve(self, assumptions=None):
        if assumptions is not None:
            bool_ass = []
            other_ass = []
            for x in assumptions:
                if x.is_literal():
                    bool_ass.append(self.converter.convert(x))
                else:
                    other_ass.append(x)

            if len(other_ass) > 0:
                self.push()
                self.add_assertion(self.mgr.And(other_ass))
                self.pending_pop = True
            #pylint: disable=star-args
            res = self.z3.check(*bool_ass)
        else:
            res = self.z3.check()

        sres = str(res)
        assert sres in ['unknown', 'sat', 'unsat']
        if sres == 'unknown':
            raise SolverReturnedUnknownResultError
        return (sres == 'sat')

    def get_unsat_core(self):
        """After a call to solve() yielding UNSAT, returns the unsat core as a
        set of formulae"""
        return self.get_named_unsat_core().values()

    def _named_assertions_map(self):
        if self.options.unsat_cores_mode is not None:
            return dict((t[0], (t[1],t[2])) for t in self.assertions)
        return None

    def get_named_unsat_core(self):
        """After a call to solve() yielding UNSAT, returns the unsat core as a
        dict of names to formulae"""
        if self.options.unsat_cores_mode is None:
            raise SolverNotConfiguredForUnsatCoresError

        if self.last_result is not False:
            raise SolverStatusError("The last call to solve() was not" \
                                    " unsatisfiable")

        if self.last_command != "solve":
            raise SolverStatusError("The solver status has been modified by a" \
                                    " '%s' command after the last call to" \
                                    " solve()" % self.last_command)

        assumptions = self.z3.unsat_core()
        pysmt_assumptions = set(self.converter.back(t) for t in assumptions)

        res = {}
        n_ass_map = self._named_assertions_map()
        cnt = 0
        for key in pysmt_assumptions:
            if key in n_ass_map:
                (name, formula) = n_ass_map[key]
                if name is None:
                    name = "_a_%d" % cnt
                    cnt += 1
                res[name] = formula
        return res


    @clear_pending_pop
    def all_sat(self, important, callback):
        raise NotImplementedError

    @clear_pending_pop
    def _push(self, levels=1):
        for _ in xrange(levels):
            self.z3.push()

    @clear_pending_pop
    def _pop(self, levels=1):
        for _ in xrange(levels):
            self.z3.pop()

    def print_model(self, name_filter=None):
        for var in self.declarations:
            if name_filter is None or not var.symbol_name().startswith(name_filter):
                print("%s = %s" % (var.symbol_name(), self.get_value(var)))


    def get_value(self, item):
        self._assert_no_function_type(item)

        titem = self.converter.convert(item)
        res = self.z3.model().eval(titem, model_completion=True)
        r = self.converter.back(res)
        return r

    def _exit(self):
        del self.z3


class Z3Converter(Converter, DagWalker):

    def __init__(self, environment):
        DagWalker.__init__(self, environment)
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type
        self._back_memoization = {}
        return

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    def back(self, expr):
        stack = [expr]
        while len(stack) > 0:
            current = stack.pop()
            key = askey(current)
            if key not in self._back_memoization:
                self._back_memoization[key] = None
                stack.append(current)
                for child in current.children():
                    stack.append(child)
            elif self._back_memoization[key] is None:
                args = [self._back_memoization[askey(c)]
                        for c in current.children()]
                res = self._back_single_term(current, args)
                self._back_memoization[key] = res
            else:
                # we already visited the node, nothing else to do
                pass
        return self._back_memoization[askey(expr)]


    def _back_single_term(self, expr, args):
        assert z3.is_expr(expr)

        if z3.is_quantifier(expr):
            raise NotImplementedError(
                "Quantified back conversion is currently not supported")

        res = None
        if z3.is_and(expr):
            res = self.mgr.And(args)
        elif z3.is_or(expr):
            res = self.mgr.Or(args)
        elif z3.is_add(expr):
            res = self.mgr.Plus(args)
        elif z3.is_div(expr):
            res = self.mgr.Div(args[0], args[1])
        elif z3.is_eq(expr):
            if self._get_type(args[0]).is_bool_type():
                res = self.mgr.Iff(args[0], args[1])
            else:
                res = self.mgr.Equals(args[0], args[1])
        elif z3.is_iff(expr):
            res = self.mgr.Iff(args[0], args[1])
        elif z3.is_xor(expr):
            res = self.mgr.Xor(args[0], args[1])
        elif z3.is_false(expr):
            res = self.mgr.FALSE()
        elif z3.is_true(expr):
            res = self.mgr.TRUE()
        elif z3.is_gt(expr):
            res = self.mgr.GT(args[0], args[1])
        elif z3.is_ge(expr):
            res = self.mgr.GE(args[0], args[1])
        elif z3.is_lt(expr):
            res = self.mgr.LT(args[0], args[1])
        elif z3.is_le(expr):
            res = self.mgr.LE(args[0], args[1])
        elif z3.is_mul(expr):
            res = self.mgr.Times(args[0], args[1])
        elif z3.is_uminus(expr):
            tp = self._get_type(args[0])
            if tp.is_real_type():
                minus_one = self.mgr.Real(-1)
            else:
                assert tp.is_int_type()
                minus_one = self.mgr.Int(-1)
            res = self.mgr.Times(args[0], minus_one)
        elif z3.is_sub(expr):
            res = self.mgr.Minus(args[0], args[1])
        elif z3.is_not(expr):
            res = self.mgr.Not(args[0])
        elif z3.is_implies(expr):
            res = self.mgr.Implies(args[0], args[1])
        elif z3.is_quantifier(expr):
            raise NotImplementedError
        elif z3.is_const(expr):
            if z3.is_rational_value(expr):
                n = expr.numerator_as_long()
                d = expr.denominator_as_long()
                f = Fraction(n, d)
                res = self.mgr.Real(f)
            elif z3.is_int_value(expr):
                n = expr.as_long()
                res = self.mgr.Int(n)
            elif z3.is_bv_value(expr):
                n = expr.as_long()
                w = expr.size()
                res = self.mgr.BV(n, w)
            else:
                # it must be a symbol
                res = self.mgr.get_symbol(str(expr))
        elif z3.is_ite(expr):
            res = self.mgr.Ite(args[0], args[1], args[2])
        elif z3.is_function(expr):
            res = self.mgr.Function(self.mgr.get_symbol(expr.decl().name()), args)
        elif z3.is_to_real(expr):
            res = self.mgr.ToReal(args[0])
        elif z3.is_bv_and(expr):
            res = self.mgr.BVAnd(args[0], args[1])
        elif z3.is_bv_or(expr):
            res = self.mgr.BVOr(args[0], args[1])
        elif z3.is_bv_xor(expr):
            res = self.mgr.BVXor(args[0], args[1])
        elif z3.is_bv_not(expr):
            res = self.mgr.BVNot(args[0])
        elif z3.is_bv_neg(expr):
            res = self.mgr.BVNeg(args[0])
        elif z3.is_bv_concat(expr):
            res = self.mgr.BVConcat(args[0], args[1])
        elif z3.is_bv_ult(expr):
            res = self.mgr.BVULT(args[0], args[1])
        elif z3.is_bv_uleq(expr):
            res = self.mgr.BVULE(args[0], args[1])
        elif z3.is_bv_slt(expr):
            res = self.mgr.BVSLT(args[0], args[1])
        elif z3.is_bv_sleq(expr):
            res = self.mgr.BVSLE(args[0], args[1])
        elif z3.is_bv_ugt(expr):
            res = self.mgr.BVUGT(args[0], args[1])
        elif z3.is_bv_ugeq(expr):
            res = self.mgr.BVUGE(args[0], args[1])
        elif z3.is_bv_sgt(expr):
            res = self.mgr.BVSGT(args[0], args[1])
        elif z3.is_bv_sgeq(expr):
            res = self.mgr.BVSGE(args[0], args[1])
        elif z3.is_bv_extract(expr):
            end = z3.get_payload(expr, 0)
            start = z3.get_payload(expr, 1)
            res = self.mgr.BVExtract(args[0], start, end)
        elif z3.is_bv_add(expr):
            res = self.mgr.BVAdd(args[0], args[1])
        elif z3.is_bv_mul(expr):
            res = self.mgr.BVMul(args[0], args[1])
        elif z3.is_bv_udiv(expr):
            res = self.mgr.BVUDiv(args[0], args[1])
        elif z3.is_bv_sdiv(expr):
            res = self.mgr.BVSDiv(args[0], args[1])
        elif z3.is_bv_urem(expr):
            res = self.mgr.BVURem(args[0], args[1])
        elif z3.is_bv_srem(expr):
            res = self.mgr.BVSRem(args[0], args[1])
        elif z3.is_bv_lshl(expr):
            res = self.mgr.BVLShl(args[0], args[1])
        elif z3.is_bv_lshr(expr):
            res = self.mgr.BVLShr(args[0], args[1])
        elif z3.is_bv_ashr(expr):
            res = self.mgr.BVAShr(args[0], args[1])
        elif z3.is_bv_sub(expr):
            res = self.mgr.BVSub(args[0], args[1])
        elif z3.is_bv_rol(expr):
            amount = z3.get_payload(expr, 0)
            res = self.mgr.BVRol(args[0], amount)
        elif z3.is_bv_ror(expr):
            amount = z3.get_payload(expr, 0)
            res = self.mgr.BVRor(args[0], amount)
        elif z3.is_bv_ext_rol(expr):
            amount = args[1].bv_unsigned_value()
            res = self.mgr.BVRol(args[0], amount)
        elif z3.is_bv_ext_ror(expr):
            amount = args[1].bv_unsigned_value()
            res = self.mgr.BVRor(args[0], amount)
        elif z3.is_bv_sext(expr):
            amount = z3.get_payload(expr, 0)
            res = self.mgr.BVSExt(args[0], amount)
        elif z3.is_bv_zext(expr):
            amount = z3.get_payload(expr, 0)
            res = self.mgr.BVZExt(args[0], amount)

        if res is None:
            raise ConvertExpressionError(message=("Unsupported expression: %s" %
                                                   str(expr)),
                                         expression=expr)
        return res


    def walk_and(self, formula, args, **kwargs):
        #pylint: disable=star-args
        return z3.And(*args)

    def walk_or(self, formula, args, **kwargs):
        #pylint: disable=star-args
        return z3.Or(*args)

    def walk_not(self, formula, args, **kwargs):
        return z3.Not(args[0])

    def walk_symbol(self, formula, **kwargs):
        symbol_type = formula.symbol_type()
        if symbol_type.is_bool_type():
            res = z3.Bool(formula.symbol_name())
        elif symbol_type.is_real_type():
            res = z3.Real(formula.symbol_name())
        elif symbol_type.is_int_type():
            res = z3.Int(formula.symbol_name())
        else:
            assert symbol_type.is_bv_type()
            res = z3.BitVec(formula.symbol_name(),
                            formula.bv_width())
        return res

    def walk_iff(self, formula, args, **kwargs):
        return (args[0] == args[1])

    def walk_implies(self, formula, args, **kwargs):
        return z3.Implies(args[0], args[1])

    def walk_le(self, formula, args, **kwargs):
        return (args[0] <= args[1])

    def walk_lt(self, formula, args, **kwargs):
        return (args[0] < args[1])

    def walk_ite(self, formula, args, **kwargs):
        i = args[0]
        t = args[1]
        e = args[2]

        if self._get_type(formula).is_bool_type():
            return z3.And(z3.Implies(i, t), z3.Implies(z3.Not(i), e))
        else:
            return z3.If(i, t, e)

    def walk_real_constant(self, formula, **kwargs):
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        return z3.RealVal(rep)

    def walk_int_constant(self, formula, **kwargs):
        assert type(formula.constant_value()) == int or \
            type(formula.constant_value()) == long
        return z3.IntVal(formula.constant_value())

    def walk_bool_constant(self, formula, **kwargs):
        return z3.BoolVal(formula.constant_value())

    def walk_exists(self, formula, args, **kwargs):
        return z3.Exists([self.walk_symbol(x)
                          for x in formula.quantifier_vars()],
                         args[0])

    def walk_forall(self, formula, args, **kwargs):
        return z3.ForAll([self.walk_symbol(x)
                          for x in formula.quantifier_vars()],
                         args[0])

    def walk_plus(self, formula, args, **kwargs):
        #pylint: disable=star-args
        return z3.Sum(*args)

    def walk_minus(self, formula, args, **kwargs):
        return (args[0] - args[1])

    def walk_equals(self, formula, args, **kwargs):
        return (args[0] == args[1])

    def walk_times(self, formula, args, **kwargs):
        return (args[0] * args[1])

    def walk_toreal(self, formula, args, **kwargs):
        return z3.ToReal(args[0])

    def walk_function(self, formula, args, **kwargs):
        #pylint: disable=star-args
        f = formula.function_name()
        tp = f.symbol_type()
        sig = [self._type_to_z3(x) for x in tp.param_types]
        sig.append(self._type_to_z3(tp.return_type))
        z3_f = z3.Function(f.symbol_name(), *sig)
        return z3_f(*args)

    def walk_bv_constant(self, formula, **kwargs):
        value = formula.constant_value()
        width = formula.bv_width()
        return z3.BitVecVal(value, width)

    def walk_bv_ult(self, formula, args, **kwargs):
        return z3.ULT(args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        return z3.ULE(args[0], args[1])

    def walk_bv_concat(self, formula, args, **kwargs):
        return z3.Concat(args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        return z3.Extract(formula.bv_extract_end(),
                          formula.bv_extract_start(),
                          args[0])

    def walk_bv_or(self, formula, args, **kwargs):
        return args[0] | args[1]

    def walk_bv_not(self, formula, args, **kwargs):
        return ~args[0]

    def walk_bv_and(self, formula, args, **kwargs):
        return args[0] & args[1]

    def walk_bv_xor(self, formula, args, **kwargs):
        return args[0] ^ args[1]

    def walk_bv_add(self, formula, args, **kwargs):
        return args[0] + args[1]

    def walk_bv_sub(self, formula, args, **kwargs):
        return args[0] - args[1]

    def walk_bv_neg(self, formula, args, **kwargs):
        return -args[0]

    def walk_bv_mul(self, formula, args, **kwargs):
        return args[0]*args[1]

    def walk_bv_udiv(self, formula, args, **kwargs):
        return z3.UDiv(args[0], args[1])

    def walk_bv_urem(self, formula, args, **kwargs):
        return z3.URem(args[0], args[1])

    def walk_bv_lshl(self, formula, args, **kwargs):
        return args[0] << args[1]

    def walk_bv_lshr(self, formula, args, **kwargs):
        return z3.LShR(args[0], args[1])

    def walk_bv_rol(self, formula, args, **kwargs):
        return z3.RotateLeft(args[0],
                             formula.bv_rotation_step())

    def walk_bv_ror(self, formula, args, **kwargs):
        return z3.RotateRight(args[0],
                             formula.bv_rotation_step())

    def walk_bv_zext(self, formula, args, **kwargs):
        return z3.ZeroExt(formula.bv_extend_step(), args[0])

    def walk_bv_sext (self, formula, args, **kwargs):
        return z3.SignExt(formula.bv_extend_step(), args[0])

    def walk_bv_slt(self, formula, args, **kwargs):
        return args[0] < args[1]

    def walk_bv_sle (self, formula, args, **kwargs):
        return args[0] <= args[1]

    def walk_bv_comp (self, formula, args, **kwargs):
        return z3.If(args[0] == args[1], z3.BitVecVal(1, 1), z3.BitVecVal(0, 1))

    def walk_bv_sdiv (self, formula, args, **kwargs):
        return args[0] / args[1]

    def walk_bv_srem (self, formula, args, **kwargs):
        return z3.SRem(args[0], args[1])

    def walk_bv_ashr (self, formula, args, **kwargs):
        return args[0] >> args[1]

    def _type_to_z3(self, tp):
        if tp.is_bool_type():
            return z3.BoolSort()
        elif tp.is_real_type():
            return z3.RealSort()
        elif tp.is_int_type():
            return z3.IntSort()
        else:
            assert tp.is_bv_type() , "Unsupported type '%s'" % tp
            return z3.BitVecSort(tp.width)


class Z3QuantifierEliminator(QuantifierEliminator):

    LOGICS = [LIA, LRA]

    def __init__(self, environment, logic=None):
        QuantifierEliminator.__init__(self)
        self.environment = environment
        self.logic = logic
        self.converter = Z3Converter(environment)

    def eliminate_quantifiers(self, formula):
        logic = get_logic(formula, self.environment)
        if not logic <= LRA and not logic <= LIA:
            raise NotImplementedError("Z3 quantifier elimination only "\
                                      "supports LRA or LIA without combination."\
                                      "(detected logic is: %s)" % str(logic))

        simplifier = z3.Tactic('simplify')
        eliminator = z3.Tactic('qe')

        f = self.converter.convert(formula)
        s = simplifier(f, elim_and=True,
                       pull_cheap_ite=True,
                       ite_extra_rules=True).as_expr()
        res = eliminator(s, eliminate_variables_as_block=True).as_expr()

        pysmt_res = None
        try:
            pysmt_res = self.converter.back(res)
        except ConvertExpressionError:
            if logic <= LRA:
                raise
            raise ConvertExpressionError(message=("Unable to represent" \
                "expression %s in pySMT: the quantifier elimination for " \
                "LIA is incomplete as it requires the modulus. You can " \
                "find the Z3 expression representing the quantifier " \
                "elimination as the attribute 'expression' of this " \
                "exception object" % str(res)),
                                          expression=res)

        return pysmt_res

    def _exit(self):
        pass


class Z3Interpolator(Interpolator):

    LOGICS = [QF_UFLIA, QF_UFLRA]

    def __init__(self, environment, logic=None):
        Interpolator.__init__(self)
        self.environment = environment
        self.logic = logic
        self.converter = Z3Converter(environment)

    def _check_logic(self, formulas):
        for f in formulas:
            logic = get_logic(f, self.environment)
            ok = any(logic <= l for l in self.LOGICS)
            if not ok:
                raise NotImplementedError(
                    "Logic not supported by Z3 interpolation."
                    "(detected logic is: %s)" % str(logic))

    def binary_interpolant(self, a, b):
        self._check_logic([a, b])

        a = self.converter.convert(a)
        b = self.converter.convert(b)

        try:
            itp = z3.binary_interpolant(a, b)
            pysmt_res = self.converter.back(itp)
        except z3.ModelRef:
            pysmt_res = None

        return pysmt_res

    def sequence_interpolant(self, formulas):
        self._check_logic(formulas)

        zf = [self.converter.convert(f) for f in formulas]
        try:
            itp = z3.sequence_interpolant(zf)
            pysmt_res = [self.converter.back(f) for f in itp]
        except z3.ModelRef:
            pysmt_res = None

        return pysmt_res

    def _exit(self):
        pass
