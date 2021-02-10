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
from warnings import warn

from pysmt.exceptions import SolverAPINotFound
from pysmt.constants import Fraction, is_pysmt_fraction, is_pysmt_integer

try:
    import mathsat
except ImportError:
    raise SolverAPINotFound

from pysmt.logics import LRA, LIA, QF_UFLIA, QF_UFLRA, QF_BV, PYSMT_QF_LOGICS
from pysmt.oracles import get_logic

import pysmt.operators as op
from pysmt import typing as types
from pysmt.solvers.solver import (IncrementalTrackingSolver, UnsatCoreSolver,
                                  Model, Converter, SolverOptions)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.walkers import DagWalker
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              SolverNotConfiguredForUnsatCoresError,
                              SolverStatusError,
                              InternalSolverError,
                              NonLinearError, PysmtValueError, PysmtTypeError,
                              ConvertExpressionError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.solvers.qelim import QuantifierEliminator
from pysmt.solvers.interpolation import Interpolator
from pysmt.walkers.identitydag import IdentityDagWalker


class MSatEnv(object):
    """A wrapper for the msat_env object.

    Objects within pySMT should only reference the msat_environment
    through this object. When calling a function from the underlying
    wrapper, the inner instance of msat_env needs to be used.
    This is done using the __call__ method: e.g.,
       env = MSatEnv()
       mathsat.function(env())
    """
    __slots__ = ['msat_env']

    def __init__(self, msat_config=None):
        if msat_config is None:
            self.msat_env = mathsat.msat_create_env()
        else:
            self.msat_env = mathsat.msat_create_env(msat_config)

    def __del__(self):
        mathsat.msat_destroy_env(self.msat_env)

    def __call__(self):
        return self.msat_env


class MathSAT5Model(Model):
    """Stand-alone model"""

    def __init__(self, environment, msat_env):
        Model.__init__(self, environment)
        self.msat_env = msat_env
        self.converter = MSatConverter(environment, self.msat_env)
        self.msat_model = None

        msat_model = mathsat.msat_get_model(self.msat_env())
        if mathsat.MSAT_ERROR_MODEL(msat_model):
            msat_msg = mathsat.msat_last_error_message(self.msat_env())
            raise InternalSolverError(msat_msg)
        self.msat_model = msat_model

    def __del__(self):
        if self.msat_model is not None:
            mathsat.msat_destroy_model(self.msat_model)
        del self.msat_env

    def get_value(self, formula, model_completion=True):
        titem = self.converter.convert(formula)
        msat_res = mathsat.msat_model_eval(self.msat_model, titem)
        if mathsat.MSAT_ERROR_TERM(msat_res):
            raise InternalSolverError("get model value")
        val = self.converter.back(msat_res)
        if self.environment.stc.get_type(formula).is_real_type() and \
               val.is_int_constant():
            val = self.environment.formula_manager.Real(val.constant_value())
        return val

    def iterator_over(self, language):
        for x in language:
            yield x, self.get_value(x, model_completion=True)

    def __iter__(self):
        """Overloading of iterator from Model.  We iterate only on the
        variables defined in the assignment.
        """
        it = mathsat.msat_model_create_iterator(self.msat_model)
        if mathsat.MSAT_ERROR_MODEL_ITERATOR(it):
            raise InternalSolverError("model iteration")

        while mathsat.msat_model_iterator_has_next(it):
            t, v = mathsat.msat_model_iterator_next(it)
            if mathsat.msat_term_is_constant(self.msat_env(), t):
                pt = self.converter.back(t)
                pv = self.converter.back(v)
                if self.environment.stc.get_type(pt).is_real_type() and \
                       pv.is_int_constant():
                    pv = self.environment.formula_manager.Real(
                        pv.constant_value())
                yield (pt, pv)

        mathsat.msat_destroy_model_iterator(it)

    def __contains__(self, x):
        """Returns whether the model contains a value for 'x'."""
        return x in (v for v, _ in self)

# EOC MathSAT5Model


class MathSATOptions(SolverOptions):

    def __init__(self, **base_options):
        SolverOptions.__init__(self, **base_options)

    @staticmethod
    def _set_option(msat_config, name, value):
        """Sets the given option. Might raise a ValueError."""
        check = mathsat.msat_set_option(msat_config, name, value)
        if check != 0:
            raise PysmtValueError("Error setting the option '%s=%s'" % (name,value))

    def __call__(self, solver):
        if self.generate_models:
            self._set_option(solver.msat_config, "model_generation", "true")

        if self.unsat_cores_mode is not None:
            self._set_option(solver.msat_config, "unsat_core_generation", "1")

        if self.random_seed is not None:
            self._set_option(solver.msat_config,
                             "random_seed", str(self.random_seed))

        for k,v in self.solver_options.items():
            self._set_option(solver.msat_config, str(k), str(v))

        if "debug.api_call_trace_filename" in self.solver_options:
            self._set_option(solver.msat_config, "debug.api_call_trace", "1")

        # Force semantics of division by 0
        self._set_option(solver.msat_config, "theory.bv.div_by_zero_mode", "0")

# EOC MathSATOptions


class MathSAT5Solver(IncrementalTrackingSolver, UnsatCoreSolver,
                     SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = PYSMT_QF_LOGICS -\
             set(l for l in PYSMT_QF_LOGICS \
                 if not l.theory.linear or l.theory.strings)

    OptionsClass = MathSATOptions

    def __init__(self, environment, logic, **options):
        IncrementalTrackingSolver.__init__(self,
                                           environment=environment,
                                           logic=logic,
                                           **options)

        self.msat_config = mathsat.msat_create_default_config(str(logic))
        self.options(self)
        self.msat_env = MSatEnv(self.msat_config)
        mathsat.msat_destroy_config(self.msat_config)
        self.converter = MSatConverter(environment, self.msat_env)

        # Shortcuts
        self.realType = mathsat.msat_get_rational_type(self.msat_env())
        self.intType = mathsat.msat_get_integer_type(self.msat_env())
        self.boolType = mathsat.msat_get_bool_type(self.msat_env())
        self.mgr = environment.formula_manager

    @clear_pending_pop
    def _reset_assertions(self):
        mathsat.msat_reset_env(self.msat_env())

    @clear_pending_pop
    def declare_variable(self, var):
        raise NotImplementedError

    @clear_pending_pop
    def _add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)

        result = formula
        if self.options.unsat_cores_mode == "named":
            # If we want named unsat cores, we need to rewrite the
            # formulae as implications
            key = self.mgr.FreshSymbol(template="_assertion_%d")
            result = (key, named, formula)
            formula = self.mgr.Implies(key, formula)

        term = self.converter.convert(formula)
        res = mathsat.msat_assert_formula(self.msat_env(), term)

        if res != 0:
            msat_msg = mathsat.msat_last_error_message(self.msat_env())
            raise InternalSolverError(msat_msg)

        return result

    def _named_assertions(self):
        if self.options.unsat_cores_mode == "named":
            return [t[0] for t in self.assertions]
        return None

    def _named_assertions_map(self):
        if self.options.unsat_cores_mode == "named":
            return dict((t[0], (t[1],t[2])) for t in self.assertions)
        return None

    @clear_pending_pop
    def _solve(self, assumptions=None):
        res = None

        n_ass = self._named_assertions()
        if n_ass is not None and len(n_ass) > 0:
            if assumptions is None:
                assumptions = n_ass
            else:
                assumptions += n_ass

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

            if len(bool_ass) > 0:
                res = mathsat.msat_solve_with_assumptions(self.msat_env(), bool_ass)
            else:
                res = mathsat.msat_solve(self.msat_env())

        else:
            res = mathsat.msat_solve(self.msat_env())

        assert res in [mathsat.MSAT_UNKNOWN,mathsat.MSAT_SAT,mathsat.MSAT_UNSAT]
        if res == mathsat.MSAT_UNKNOWN:
            msat_msg = mathsat.msat_last_error_message(self.msat_env())
            raise SolverReturnedUnknownResultError(msat_msg)

        return (res == mathsat.MSAT_SAT)

    def get_unsat_core(self):
        """After a call to solve() yielding UNSAT, returns the unsat core as a
        set of formulae"""
        self._check_unsat_core_config()
        if self.options.unsat_cores_mode == "all":

            terms = mathsat.msat_get_unsat_core(self.msat_env())
            if terms is None:
                raise InternalSolverError(
                    mathsat.msat_last_error_message(self.msat_env()))
            return set(self.converter.back(t) for t in terms)
        else:
            return self.get_named_unsat_core().values()

    def get_named_unsat_core(self):
        """After a call to solve() yielding UNSAT, returns the unsat core as a
        dict of names to formulae"""
        self._check_unsat_core_config()
        if self.options.unsat_cores_mode == "named":

            assumptions = mathsat.msat_get_unsat_assumptions(self.msat_env())
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

        else:
            return dict(("_a%d" % i, f)
                        for i,f in enumerate(self.get_unsat_core()))

    @clear_pending_pop
    def all_sat(self, important, callback):
        self.push()
        mathsat.msat_all_sat(self.msat_env(),
                             [self._var2term(x) for x in important],
                             callback)
        self.pop()

    @clear_pending_pop
    def _push(self, levels=1):
        for _ in range(levels):
            mathsat.msat_push_backtrack_point(self.msat_env())

    @clear_pending_pop
    def _pop(self, levels=1):
        for _ in range(levels):
            mathsat.msat_pop_backtrack_point(self.msat_env())

    def _var2term(self, var):
        decl = mathsat.msat_find_decl(self.msat_env(), var.symbol_name())
        titem = mathsat.msat_make_term(self.msat_env(), decl, [])
        return titem

    def set_preferred_var(self, var, val=None):
        tvar = self.converter.convert(var)
        mval = mathsat.MSAT_UNDEF
        if val is not None:
            mval = mathsat.MSAT_TRUE if val==True else mathsat.MSAT_FALSE
        mathsat.msat_add_preferred_for_branching(self.msat_env(), tvar, mval)
        return

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
        tval = mathsat.msat_get_model_value(self.msat_env(), titem)
        val = self.converter.back(tval)
        if self.environment.stc.get_type(item).is_real_type() and \
               val.is_int_constant():
            val = self.mgr.Real(val.constant_value())
        return val

    def get_model(self):
        return MathSAT5Model(self.environment, self.msat_env)

    def _exit(self):
        del self.msat_env


class MSatConverter(Converter, DagWalker):

    def __init__(self, environment, msat_env):
        DagWalker.__init__(self, environment)

        self.msat_env = msat_env
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type

        # Maps a Symbol into the corresponding msat_decl instance in the msat_env
        self.symbol_to_decl = {}
        # Maps a msat_decl instance inside the msat_env into the corresponding
        # Symbol
        self.decl_to_symbol = {}

        self.boolType = mathsat.msat_get_bool_type(self.msat_env())
        self.realType = mathsat.msat_get_rational_type(self.msat_env())
        self.intType = mathsat.msat_get_integer_type(self.msat_env())

        # Back Conversion
        self.back_memoization = {}
        self.back_fun = {
            mathsat.MSAT_TAG_TRUE: lambda term, args: self.mgr.TRUE(),
            mathsat.MSAT_TAG_FALSE:lambda term, args: self.mgr.FALSE(),
            mathsat.MSAT_TAG_AND: self._back_adapter(self.mgr.And),
            mathsat.MSAT_TAG_OR:  self._back_adapter(self.mgr.Or),
            mathsat.MSAT_TAG_NOT: self._back_adapter(self.mgr.Not),
            mathsat.MSAT_TAG_IFF: self._back_adapter(self.mgr.Iff),
            mathsat.MSAT_TAG_ITE: self._back_adapter(self.mgr.Ite),
            mathsat.MSAT_TAG_EQ:  self._back_adapter(self.mgr.Equals),
            mathsat.MSAT_TAG_LEQ: self._back_adapter(self.mgr.LE),
            mathsat.MSAT_TAG_PLUS: self._back_adapter(self.mgr.Plus),
            mathsat.MSAT_TAG_TIMES: self._back_adapter(self.mgr.Times),
            mathsat.MSAT_TAG_BV_MUL: self._back_adapter(self.mgr.BVMul),
            mathsat.MSAT_TAG_BV_ADD: self._back_adapter(self.mgr.BVAdd),
            mathsat.MSAT_TAG_BV_UDIV: self._back_adapter(self.mgr.BVUDiv),
            mathsat.MSAT_TAG_BV_UREM: self._back_adapter(self.mgr.BVURem),
            mathsat.MSAT_TAG_BV_CONCAT: self._back_adapter(self.mgr.BVConcat),
            mathsat.MSAT_TAG_BV_OR: self._back_adapter(self.mgr.BVOr),
            mathsat.MSAT_TAG_BV_XOR:self._back_adapter(self.mgr.BVXor),
            mathsat.MSAT_TAG_BV_AND:self._back_adapter(self.mgr.BVAnd),
            mathsat.MSAT_TAG_BV_NOT:self._back_adapter(self.mgr.BVNot),
            mathsat.MSAT_TAG_BV_SUB:self._back_adapter(self.mgr.BVSub),
            mathsat.MSAT_TAG_BV_NEG:self._back_adapter(self.mgr.BVNeg),
            mathsat.MSAT_TAG_BV_SREM:self._back_adapter(self.mgr.BVSRem),
            mathsat.MSAT_TAG_BV_SDIV:self._back_adapter(self.mgr.BVSDiv),
            mathsat.MSAT_TAG_BV_ULT: self._back_adapter(self.mgr.BVULT),
            mathsat.MSAT_TAG_BV_SLT: self._back_adapter(self.mgr.BVSLT),
            mathsat.MSAT_TAG_BV_ULE: self._back_adapter(self.mgr.BVULE),
            mathsat.MSAT_TAG_BV_SLE: self._back_adapter(self.mgr.BVSLE),
            mathsat.MSAT_TAG_BV_LSHL: self._back_adapter(self.mgr.BVLShl),
            mathsat.MSAT_TAG_BV_LSHR: self._back_adapter(self.mgr.BVLShr),
            mathsat.MSAT_TAG_BV_ASHR: self._back_adapter(self.mgr.BVAShr),
            mathsat.MSAT_TAG_BV_COMP: self._back_adapter(self.mgr.BVComp),
            mathsat.MSAT_TAG_INT_FROM_UBV: self._back_adapter(self.mgr.BVToNatural),
            mathsat.MSAT_TAG_ARRAY_READ: self._back_adapter(self.mgr.Select),
            mathsat.MSAT_TAG_ARRAY_WRITE: self._back_adapter(self.mgr.Store),
            # Slightly more complex conversion
            mathsat.MSAT_TAG_BV_EXTRACT: self._back_bv_extract,
            mathsat.MSAT_TAG_BV_ZEXT: self._back_bv_zext,
            mathsat.MSAT_TAG_BV_SEXT: self._back_bv_sext,
            mathsat.MSAT_TAG_BV_ROL: self._back_bv_rol,
            mathsat.MSAT_TAG_BV_ROR: self._back_bv_ror,
            mathsat.MSAT_TAG_ARRAY_CONST: self._back_array_const,
            # Symbols, Constants and UFs have TAG_UNKNOWN
            mathsat.MSAT_TAG_UNKNOWN: self._back_tag_unknown,
        }

        # Handling of UF bool args
        self._ufrewriter = MSatBoolUFRewriter(environment)

        # Signature Computation
        self.term_sig = {
            mathsat.MSAT_TAG_TRUE: lambda term, args: types.BOOL,
            mathsat.MSAT_TAG_FALSE: lambda term, args: types.BOOL,
            mathsat.MSAT_TAG_AND: lambda term, args:\
                types.FunctionType(types.BOOL, [types.BOOL, types.BOOL]),
            mathsat.MSAT_TAG_OR: lambda term, args:\
                types.FunctionType(types.BOOL, [types.BOOL, types.BOOL]),
            mathsat.MSAT_TAG_NOT: lambda term, args:\
                types.FunctionType(types.BOOL, [types.BOOL]),
            mathsat.MSAT_TAG_IFF: lambda term, args:\
                types.FunctionType(types.BOOL, [types.BOOL, types.BOOL]),
            mathsat.MSAT_TAG_ITE: self._sig_ite,
            mathsat.MSAT_TAG_EQ: self._sig_most_generic_bool_binary,
            mathsat.MSAT_TAG_LEQ: self._sig_most_generic_bool_binary,
            mathsat.MSAT_TAG_PLUS:  self._sig_most_generic_bool_binary,
            mathsat.MSAT_TAG_TIMES: self._sig_most_generic_bool_binary,
            mathsat.MSAT_TAG_BV_MUL: self._sig_binary,
            mathsat.MSAT_TAG_BV_ADD: self._sig_binary,
            mathsat.MSAT_TAG_BV_UDIV:self._sig_binary,
            mathsat.MSAT_TAG_BV_UREM:self._sig_binary,
            mathsat.MSAT_TAG_BV_CONCAT: self._sig_bv_concat,
            mathsat.MSAT_TAG_BV_OR:  self._sig_binary,
            mathsat.MSAT_TAG_BV_XOR: self._sig_binary,
            mathsat.MSAT_TAG_BV_AND: self._sig_binary,
            mathsat.MSAT_TAG_BV_NOT:  self._sig_unary,
            mathsat.MSAT_TAG_BV_SUB: self._sig_binary,
            mathsat.MSAT_TAG_BV_NEG:  self._sig_unary,
            mathsat.MSAT_TAG_BV_SREM: self._sig_binary,
            mathsat.MSAT_TAG_BV_SDIV: self._sig_binary,
            mathsat.MSAT_TAG_BV_ULT:  self._sig_bool_binary,
            mathsat.MSAT_TAG_BV_SLT:  self._sig_bool_binary,
            mathsat.MSAT_TAG_BV_ULE:  self._sig_bool_binary,
            mathsat.MSAT_TAG_BV_SLE:  self._sig_bool_binary,
            mathsat.MSAT_TAG_BV_LSHL: self._sig_binary,
            mathsat.MSAT_TAG_BV_LSHR: self._sig_binary,
            mathsat.MSAT_TAG_BV_ASHR: self._sig_binary,
            mathsat.MSAT_TAG_BV_ROL: self._sig_binary,
            mathsat.MSAT_TAG_BV_ROR:  self._sig_binary,
            mathsat.MSAT_TAG_BV_EXTRACT: self._sig_bv_extract,
            mathsat.MSAT_TAG_BV_ZEXT: self._sig_bv_zext,
            mathsat.MSAT_TAG_BV_SEXT: self._sig_bv_sext,
            mathsat.MSAT_TAG_BV_COMP: self._sig_bv_comp,
            mathsat.MSAT_TAG_ARRAY_READ: self._sig_array_read,
            mathsat.MSAT_TAG_ARRAY_WRITE: self._sig_array_write,
            mathsat.MSAT_TAG_ARRAY_CONST: self._sig_array_const,
            ## Symbols, Constants and UFs have TAG_UNKNOWN
            mathsat.MSAT_TAG_UNKNOWN: self._sig_unknown,
        }

        return

    def back(self, expr):
        return self._walk_back(expr, self.mgr)

    def _most_generic(self, ty1, ty2):
        """Returns the most generic, yet compatible type between ty1 and ty2"""
        if ty1 == ty2:
            return ty1

        assert ty1 in [types.REAL, types.INT], str(ty1)
        assert ty2 in [types.REAL, types.INT], str(ty2)
        return types.REAL

    def _get_signature(self, term, args):
        """Returns the signature of the given term.
        For example:
        - a term x & y returns a function type Bool -> Bool -> Bool,
        - a term 14 returns Int
        - a term x ? 13 : 15.0 returns Bool -> Real -> Real -> Real
        """
        decl = mathsat.msat_term_get_decl(term)
        tag = mathsat.msat_decl_get_tag(self.msat_env(), decl)
        try:
            return self.term_sig[tag](term, args)
        except KeyError:
            raise ConvertExpressionError("Unsupported expression:",
                                         mathsat.msat_term_repr(term))

    def _sig_binary(self, term, args):
        t = self.env.stc.get_type(args[0])
        return types.FunctionType(t, [t, t])

    def _sig_bool_binary(self, term, args):
        t = self.env.stc.get_type(args[0])
        return types.FunctionType(types.BOOL, [t, t])

    def _sig_most_generic_bool_binary(self, term, args):
        t1 = self.env.stc.get_type(args[0])
        t2 = self.env.stc.get_type(args[1])
        t = self._most_generic(t1, t2)
        return types.FunctionType(types.BOOL, [t, t])

    def _sig_unary(self, term, args):
        t = self.env.stc.get_type(args[0])
        return types.FunctionType(t, [t])

    def _sig_ite(self, term, args):
        t1 = self.env.stc.get_type(args[1])
        t2 = self.env.stc.get_type(args[2])
        t = self._most_generic(t1, t2)
        return types.FunctionType(t, [types.BOOL, t, t])

    def _sig_bv_comp(self, term,  args):
        t = self.env.stc.get_type(args[0])
        return types.FunctionType(types.BVType(1), [t, t])

    def _sig_bv_sext(self, term, args):
        _, amount = mathsat.msat_term_is_bv_sext(self.msat_env(), term)
        t = self.env.stc.get_type(args[0])
        return types.FunctionType(types.BVType(amount + t.width), [t])

    def _sig_bv_zext(self, term, args):
        _, amount = mathsat.msat_term_is_bv_zext(self.msat_env(), term)
        t = self.env.stc.get_type(args[0])
        return types.FunctionType(types.BVType(amount + t.width), [t])

    def _sig_bv_extract(self, term, args):
        _, msb, lsb = mathsat.msat_term_is_bv_extract(self.msat_env(), term)
        t = self.env.stc.get_type(args[0])
        return types.FunctionType(types.BVType(msb - lsb + 1), [t])

    def _sig_bv_concat(self, term, args):
        t1 = self.env.stc.get_type(args[0])
        t2 = self.env.stc.get_type(args[1])
        return types.FunctionType(types.BVType(t1.width + t2.width), [t1, t2])

    def _sig_array_read(self, term, args):
        t1 = self.env.stc.get_type(args[0])
        t = t1.elem_type
        return types.FunctionType(t, [t1, t1.index_type])

    def _sig_array_write(self, term, args):
        ty = mathsat.msat_term_get_type(term)
        at = self._msat_type_to_type(ty)
        return types.FunctionType(at, [at, at.index_type, at.elem_type])

    def _sig_array_const(self, term,  args):
        ty = mathsat.msat_term_get_type(term)
        pyty = self._msat_type_to_type(ty)
        return types.FunctionType(pyty, [pyty.elem_type])

    def _sig_unknown(self, term, args):
        if mathsat.msat_term_is_boolean_constant(self.msat_env(), term):
            return types.BOOL
        elif mathsat.msat_term_is_number(self.msat_env(), term):
            ty = mathsat.msat_term_get_type(term)
            if mathsat.msat_is_integer_type(self.msat_env(), ty):
                res = types.INT
            elif mathsat.msat_is_rational_type(self.msat_env(), ty):
                res = types.REAL
            else:
                assert "_" in str(term), "Unrecognized type for '%s'" % str(term)
                width = int(str(term).split("_")[1])
                res = types.BVType(width)
            return res
        elif mathsat.msat_term_is_constant(self.msat_env(), term):
            ty = mathsat.msat_term_get_type(term)
            return self._msat_type_to_type(ty)
        elif mathsat.msat_term_is_uf(self.msat_env(), term):
            d = mathsat.msat_term_get_decl(term)
            fun = self.get_symbol_from_declaration(d)
            return fun.symbol_type()
        raise ConvertExpressionError("Unsupported expression:",
                                     mathsat.msat_term_repr(term))

    def _back_single_term(self, term, mgr, args):
        """Builds the pysmt formula given a term and the list of formulae
        obtained by converting the term children.

        :param term: The MathSAT term to be transformed in pysmt formulae
        :type term: MathSAT term

        :param mgr: The formula manager to be sued to build the
        formulae, it should allow for type unsafety.
        :type mgr: Formula manager

        :param args: List of the pysmt formulae obtained by converting
        all the args (obtained by mathsat.msat_term_get_arg()) to
        pysmt formulae
        :type args: List of pysmt formulae

        :returns The pysmt formula representing the given term
        :rtype Pysmt formula
        """
        decl = mathsat.msat_term_get_decl(term)
        tag = mathsat.msat_decl_get_tag(self.msat_env(), decl)

        try:
            return self.back_fun[tag](term, args)
        except KeyError:
            raise ConvertExpressionError("Unsupported expression:",
                                         mathsat.msat_term_repr(term))

    def _back_adapter(self, op):
        """Create a function that for the given op.

        This is used in the construction of back_fun, to simplify the code.
        """
        def back_apply(term, args):
            return op(*args)
        return back_apply

    def _back_bv_extract(self, term, args):
        res, msb, lsb = mathsat.msat_term_is_bv_extract(self.msat_env(), term)
        assert res
        return self.mgr.BVExtract(args[0], lsb, msb)

    def _back_bv_zext(self, term, args):
        is_zext, amount = mathsat.msat_term_is_bv_zext(self.msat_env(), term)
        assert is_zext
        return self.mgr.BVZExt(args[0], amount)

    def _back_bv_sext(self, term, args):
        is_sext, amount = mathsat.msat_term_is_bv_sext(self.msat_env(), term)
        assert is_sext
        return self.mgr.BVSExt(args[0], amount)

    def _back_bv_rol(self, term, args):
        is_rol, amount = mathsat.msat_term_is_bv_rol(self.msat_env(), term)
        assert is_rol
        return self.mgr.BVRol(args[0], amount)

    def _back_bv_ror(self, term, args):
        is_ror, amount = mathsat.msat_term_is_bv_ror(self.msat_env(), term)
        assert is_ror
        return self.mgr.BVRor(args[0], amount)

    def _back_array_const(self, term, args):
        msat_type = mathsat.msat_term_get_type(term)
        pysmt_type = self._msat_type_to_type(msat_type)
        return self.mgr.Array(pysmt_type.index_type, args[0])

    def _back_tag_unknown(self, term, args):
        """The TAG UNKNOWN is used to represent msat functions.

        This includes, Constants, Symbols and UFs.
        """
        if mathsat.msat_term_is_number(self.msat_env(), term):
            ty = mathsat.msat_term_get_type(term)
            if mathsat.msat_is_integer_type(self.msat_env(), ty):
                res = self.mgr.Int(int(mathsat.msat_term_repr(term)))
            elif mathsat.msat_is_rational_type(self.msat_env(), ty):
                res = self.mgr.Real(Fraction(mathsat.msat_term_repr(term)))
            else:
                assert "_" in str(term), "Unsupported type for '%s'" % str(term)
                val, width = str(term).split("_")
                val = int(val)
                width = int(width)
                res = self.mgr.BV(val, width)
        elif mathsat.msat_term_is_constant(self.msat_env(), term):
            rep = mathsat.msat_term_repr(term)
            ty = mathsat.msat_term_get_type(term)
            if mathsat.msat_term_is_boolean_constant(self.msat_env(), term):
                res = self.mgr.Symbol(rep, types.BOOL)
            elif mathsat.msat_is_rational_type(self.msat_env(), ty):
                res = self.mgr.Symbol(rep, types.REAL)
            elif mathsat.msat_is_integer_type(self.msat_env(), ty):
                res = self.mgr.Symbol(rep, types.INT)
            else:
                check_arr, idx_type, val_type = mathsat.msat_is_array_type(self.msat_env(), ty)
                if check_arr:
                    i = self._msat_type_to_type(idx_type)
                    e = self._msat_type_to_type(val_type)
                    res = self.mgr.Symbol(rep, types.ArrayType(i, e))
                else:
                    _, width = mathsat.msat_is_bv_type(self.msat_env(), ty)
                    assert width is not None, "Unsupported variable type for '%s'"%str(term)
                    res = self.mgr.Symbol(rep, types.BVType(width))

        elif mathsat.msat_term_is_uf(self.msat_env(), term):
            d = mathsat.msat_term_get_decl(term)
            fun = self.get_symbol_from_declaration(d)
            res = self.mgr.Function(fun, args)
        else:
            raise ConvertExpressionError("Unsupported expression:",
                                         mathsat.msat_term_repr(term))
        return res

    def get_symbol_from_declaration(self, decl):
        return self.decl_to_symbol[mathsat.msat_decl_id(decl)]

    def _walk_back(self, term, mgr):
        stack = [term]

        while len(stack) > 0:
            current = stack.pop()
            arity = mathsat.msat_term_arity(current)
            if current not in self.back_memoization:
                self.back_memoization[current] = None
                stack.append(current)
                for i in range(arity):
                    son = mathsat.msat_term_get_arg(current, i)
                    stack.append(son)
            elif self.back_memoization[current] is None:
                args=[self.back_memoization[mathsat.msat_term_get_arg(current,i)]
                      for i in range(arity)]

                signature = self._get_signature(current, args)
                new_args = []
                for i, a in enumerate(args):
                    t = self.env.stc.get_type(a)
                    if t != signature.param_types[i]:
                        a = mgr.ToReal(a)
                    new_args.append(a)
                res = self._back_single_term(current, mgr, new_args)
                self.back_memoization[current] = res
            else:
                # we already visited the node, nothing else to do
                pass
        return self.back_memoization[term]

    @catch_conversion_error
    def convert(self, formula):
        """Convert a PySMT formula into a MathSat Term.

        This function might throw a InternalSolverError exception if
        an error during conversion occurs.
        """
        # Rewrite to avoid UF with bool args
        rformula = self._ufrewriter.walk(formula)
        res = self.walk(rformula)
        if mathsat.MSAT_ERROR_TERM(res):
            msat_msg = mathsat.msat_last_error_message(self.msat_env())
            raise InternalSolverError(msat_msg)
        if rformula != formula:
            warn("MathSAT convert(): UF with bool arguments have been translated")
        return res

    def walk_and(self, formula, args, **kwargs):
        res = mathsat.msat_make_true(self.msat_env())
        for a in args:
            res = mathsat.msat_make_and(self.msat_env(), res, a)
        return res

    def walk_or(self, formula, args, **kwargs):
        res = mathsat.msat_make_false(self.msat_env())
        for a in args:
            res = mathsat.msat_make_or(self.msat_env(), res, a)
        return res

    def walk_not(self, formula, args, **kwargs):
        return mathsat.msat_make_not(self.msat_env(), args[0])

    def walk_symbol(self, formula, **kwargs):
        if formula not in self.symbol_to_decl:
            self.declare_variable(formula)
        decl = self.symbol_to_decl[formula]
        return mathsat.msat_make_constant(self.msat_env(), decl)

    def walk_le(self, formula, args, **kwargs):
        return mathsat.msat_make_leq(self.msat_env(), args[0], args[1])

    def walk_lt(self, formula, args, **kwargs):
        leq = mathsat.msat_make_leq(self.msat_env(), args[1], args[0])
        return mathsat.msat_make_not(self.msat_env(), leq)

    def walk_ite(self, formula, args, **kwargs):
        i = args[0]
        t = args[1]
        e = args[2]

        if self._get_type(formula).is_bool_type():
            impl = self.mgr.Implies(formula.arg(0), formula.arg(1))
            th = self.walk_implies(impl, [i,t])
            nif = self.mgr.Not(formula.arg(0))
            ni = self.walk_not(nif, [i])
            el = self.walk_implies(self.mgr.Implies(nif, formula.arg(2)), [ni,e])
            return mathsat.msat_make_and(self.msat_env(), th, el)
        else:
            return mathsat.msat_make_term_ite(self.msat_env(), i, t, e)

    def walk_real_constant(self, formula, **kwargs):
        assert is_pysmt_fraction(formula.constant_value())
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        return mathsat.msat_make_number(self.msat_env(), rep)

    def walk_int_constant(self, formula, **kwargs):
        assert is_pysmt_integer(formula.constant_value())
        rep = str(formula.constant_value())
        return mathsat.msat_make_number(self.msat_env(), rep)

    def walk_algebraic_constant(self, formula, **kwargs):
        val = formula.constant_value()
        if val.is_irrational():
            raise ConvertExpressionError("Cannot convert irrational constant")
        num, den = val.numerator(), val.denominator()
        rep = "{}/{}".format(str(num), str(den))
        return mathsat.msat_make_number(self.msat_env(), rep)

    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return mathsat.msat_make_true(self.msat_env())
        else:
            return mathsat.msat_make_false(self.msat_env())

    def walk_bv_constant(self, formula, **kwargs):
        rep = str(formula.constant_value())
        width = formula.bv_width()
        return mathsat.msat_make_bv_number(self.msat_env(),
                                           rep, width, 10)

    def walk_bv_ult(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_ult(self.msat_env(),
                                        args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_uleq(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_slt(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_slt(self.msat_env(),
                                        args[0], args[1])

    def walk_bv_sle(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_sleq(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_concat(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_concat(self.msat_env(),
                                           args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_extract(self.msat_env(),
                                            formula.bv_extract_end(),
                                            formula.bv_extract_start(),
                                            args[0])

    def walk_bv_or(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_or(self.msat_env(),
                                       args[0], args[1])

    def walk_bv_not(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_not(self.msat_env(), args[0])

    def walk_bv_and(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_and(self.msat_env(),
                                        args[0], args[1])

    def walk_bv_xor(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_xor(self.msat_env(),
                                        args[0], args[1])

    def walk_bv_add(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_plus(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_sub(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_minus(self.msat_env(),
                                          args[0], args[1])

    def walk_bv_neg(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_neg(self.msat_env(), args[0])

    def walk_bv_mul(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_times(self.msat_env(),
                                          args[0], args[1])

    def walk_bv_udiv(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_udiv(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_urem(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_urem(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_lshl(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_lshl(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_lshr(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_lshr(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_rol(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_rol(self.msat_env(),
                                        formula.bv_rotation_step(),
                                        args[0])

    def walk_bv_ror(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_ror(self.msat_env(),
                                        formula.bv_rotation_step(),
                                        args[0])

    def walk_bv_zext(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_zext(self.msat_env(),
                                         formula.bv_extend_step(),
                                         args[0])

    def walk_bv_sext(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_sext(self.msat_env(),
                                         formula.bv_extend_step(),
                                         args[0])

    def walk_bv_comp(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_comp(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_sdiv(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_sdiv(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_srem(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_srem(self.msat_env(),
                                         args[0], args[1])

    def walk_bv_ashr(self, formula, args, **kwargs):
        return mathsat.msat_make_bv_ashr(self.msat_env(),
                                         args[0], args[1])

    def walk_plus(self, formula, args, **kwargs):
        res = mathsat.msat_make_number(self.msat_env(), "0")
        for a in args:
            res = mathsat.msat_make_plus(self.msat_env(), res, a)
        return res

    def walk_minus(self, formula, args, **kwargs):
        n_one = mathsat.msat_make_number(self.msat_env(), "-1")
        n_s2 = mathsat.msat_make_times(self.msat_env(), n_one, args[1])
        return mathsat.msat_make_plus(self.msat_env(), args[0], n_s2)

    def walk_equals(self, formula, args, **kwargs):
        return mathsat.msat_make_equal(self.msat_env(), args[0], args[1])

    def walk_iff(self, formula, args, **kwargs):
        return mathsat.msat_make_iff(self.msat_env(), args[0], args[1])

    def walk_implies(self, formula, args, **kwargs):
        neg = self.walk_not(self.mgr.Not(formula.arg(0)), [args[0]])
        return mathsat.msat_make_or(self.msat_env(), neg, args[1])

    def walk_times(self, formula, args, **kwargs):
        res = args[0]
        nl_count = 0 if mathsat.msat_term_is_number(self.msat_env(), res) else 1
        for x in args[1:]:
            if not mathsat.msat_term_is_number(self.msat_env(), x):
                nl_count += 1
            if nl_count >= 2:
                raise NonLinearError(formula)
            else:
                res = mathsat.msat_make_times(self.msat_env(), res, x)
        return res

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()
        if name not in self.symbol_to_decl:
            self.declare_variable(name)
        decl = self.symbol_to_decl[name]
        return mathsat.msat_make_uf(self.msat_env(), decl, args)

    def walk_toreal(self, formula, args, **kwargs):
        # In mathsat toreal is implicit
        return args[0]

    def walk_bv_tonatural(self, formula, args, **kwargs):
        return mathsat.msat_make_int_from_ubv(self.msat_env(), args[0])

    def walk_array_select(self, formula, args, **kwargs):
        return mathsat.msat_make_array_read(self.msat_env(), args[0], args[1])

    def walk_array_store(self, formula, args, **kwargs):
        return mathsat.msat_make_array_write(self.msat_env(),
                                             args[0], args[1], args[2])

    def walk_array_value(self, formula, args, **kwargs):
        arr_type = self.env.stc.get_type(formula)
        rval = mathsat.msat_make_array_const(self.msat_env(),
                                             self._type_to_msat(arr_type),
                                             args[0])
        assert not mathsat.MSAT_ERROR_TERM(rval)
        for i,c in enumerate(args[1::2]):
            rval = mathsat.msat_make_array_write(self.msat_env(), rval,
                                                 c, args[(i*2)+2])
        return rval

    def _type_to_msat(self, tp):
        """Convert a pySMT type into a MathSAT type."""
        if tp.is_bool_type():
            return self.boolType
        elif tp.is_real_type():
            return self.realType
        elif tp.is_int_type():
            return self.intType
        elif tp.is_function_type():
            stps = [self._type_to_msat(x) for x in tp.param_types]
            rtp = self._type_to_msat(tp.return_type)
            msat_type = mathsat.msat_get_function_type(self.msat_env(),
                                                       stps,
                                                       rtp)
            if mathsat.MSAT_ERROR_TYPE(msat_type):
                msat_msg = mathsat.msat_last_error_message(self.msat_env())
                raise InternalSolverError(msat_msg)
            return msat_type
        elif tp.is_array_type():
            i = self._type_to_msat(tp.index_type)
            e = self._type_to_msat(tp.elem_type)
            msat_type = mathsat.msat_get_array_type(self.msat_env(), i, e)
            if mathsat.MSAT_ERROR_TYPE(msat_type):
                msat_msg = mathsat.msat_last_error_message(self.msat_env())
                raise InternalSolverError(msat_msg)
            return msat_type
        elif tp.is_bv_type():
            return mathsat.msat_get_bv_type(self.msat_env(), tp.width)
        elif tp.is_custom_type():
            return mathsat.msat_get_simple_type(self.msat_env(), str(tp))
        else:
            raise NotImplementedError("Usupported type for '%s'" % tp)


    def _msat_type_to_type(self, tp):
        """Converts a MathSAT type into a PySMT type."""
        if mathsat.msat_is_bool_type(self.msat_env(), tp):
            return types.BOOL
        elif mathsat.msat_is_rational_type(self.msat_env(), tp):
            return types.REAL
        elif mathsat.msat_is_integer_type(self.msat_env(), tp):
            return types.INT
        else:
            check_arr, idx_type, val_type = \
                    mathsat.msat_is_array_type(self.msat_env(), tp)
            if check_arr != 0:
                i = self._msat_type_to_type(idx_type)
                e = self._msat_type_to_type(val_type)
                return types.ArrayType(i, e)

            check_bv, bv_width = mathsat.msat_is_bv_type(self.msat_env(), tp)
            if check_bv != 0:
                return types.BVType(bv_width)

            # It must be a function type, currently unsupported
            raise NotImplementedError("Function types are unsupported")


    def declare_variable(self, var):
        if not var.is_symbol():
            raise PysmtTypeError("Trying to declare as a variable something "
                                 "that is not a symbol: %s" % var)
        if var.symbol_name() not in self.symbol_to_decl:
            tp = self._type_to_msat(var.symbol_type())
            decl = mathsat.msat_declare_function(self.msat_env(),
                                                 var.symbol_name(),
                                                 tp)
            if mathsat.MSAT_ERROR_DECL(decl):
                msat_msg = mathsat.msat_last_error_message(self.msat_env())
                raise InternalSolverError(msat_msg)
            self.symbol_to_decl[var] = decl
            self.decl_to_symbol[mathsat.msat_decl_id(decl)] = var


# Check if we are working on a version MathSAT supporting quantifier elimination
if hasattr(mathsat, "MSAT_EXIST_ELIM_ALLSMT_FM"):
    class MSatQuantifierEliminator(QuantifierEliminator, IdentityDagWalker):

        LOGICS = [LRA, LIA]

        def __init__(self, environment, logic=None, algorithm='lw'):
            """Initialize the Quantifier Eliminator using 'fm' or 'lw'.

            fm: Fourier-Motzkin (default)
            lw: Loos-Weisspfenning
            """
            if algorithm not in ['fm', 'lw']:
                raise PysmtValueError("Algorithm can be either 'fm' or 'lw'")

            if logic is not None and (not logic <= LRA and algorithm != "lw"):
                raise PysmtValueError("MathSAT quantifier elimination for LIA"\
                                      " only works with 'lw' algorithm")

            QuantifierEliminator.__init__(self)
            IdentityDagWalker.__init__(self, env=environment)
            self.msat_config = mathsat.msat_create_default_config("QF_LRA")
            self.msat_env = MSatEnv(self.msat_config)
            mathsat.msat_destroy_config(self.msat_config)

            self.set_function(self.walk_identity, op.SYMBOL, op.REAL_CONSTANT,
                              op.BOOL_CONSTANT, op.INT_CONSTANT)
            self.logic = logic

            self.algorithm = algorithm
            self.converter = MSatConverter(environment, self.msat_env)

        def eliminate_quantifiers(self, formula):
            """Returns a quantifier-free equivalent formula of `formula`."""
            return self.walk(formula)


        def exist_elim(self, variables, formula):
            logic = get_logic(formula, self.env)
            if not (logic <= LRA or logic <= LIA):
                raise PysmtValueError("MathSAT quantifier elimination only"\
                                      " supports LRA or LIA (detected logic " \
                                      "is: %s)" % str(logic))

            if not logic <= LRA and self.algorithm != "lw":
                raise PysmtValueError("MathSAT quantifier elimination for LIA"\
                                      " only works with 'lw' algorithm")


            fterm = self.converter.convert(formula)
            tvars = [self.converter.convert(x) for x in variables]

            algo = mathsat.MSAT_EXIST_ELIM_ALLSMT_FM
            if self.algorithm == 'lw':
                algo = mathsat.MSAT_EXIST_ELIM_VTS

            res = mathsat.msat_exist_elim(self.msat_env(), fterm, tvars, algo)

            try:
                return self.converter.back(res)
            except ConvertExpressionError:
                if logic <= LRA:
                    raise
                raise ConvertExpressionError(message=("Unable to represent" \
                      "expression %s in pySMT: the quantifier elimination for " \
                      "LIA is incomplete as it requires the modulus. You can " \
                      "find the MathSAT term representing the quantifier " \
                      "elimination as the attribute 'expression' of this " \
                      "exception object" % str(res)), expression=res)


        def walk_forall(self, formula, args, **kwargs):
            assert formula.is_forall()
            variables = formula.quantifier_vars()
            subf = self.env.formula_manager.Not(args[0])
            ex_res = self.exist_elim(variables, subf)
            return self.env.formula_manager.Not(ex_res)

        def walk_exists(self, formula, args, **kwargs):
            # Monolithic quantifier elimination
            assert formula.is_exists()
            variables = formula.quantifier_vars()
            subf = args[0]
            return self.exist_elim(variables, subf)

        def _exit(self):
            del self.msat_env

    class MSatFMQuantifierEliminator(MSatQuantifierEliminator):
        LOGICS = [LRA]
        def __init__(self, environment, logic=None):
            MSatQuantifierEliminator.__init__(self, environment,
                                              logic=logic, algorithm='fm')


    class MSatLWQuantifierEliminator(MSatQuantifierEliminator):
        LOGICS = [LRA, LIA]
        def __init__(self, environment, logic=None):
            MSatQuantifierEliminator.__init__(self, environment,
                                              logic=logic, algorithm='lw')


class MSatInterpolator(Interpolator):

    LOGICS = [QF_UFLIA, QF_UFLRA, QF_BV]

    def __init__(self, environment, logic=None):
        Interpolator.__init__(self)
        self.msat_env = MSatEnv()
        self.converter = MSatConverter(environment, self.msat_env)
        self.environment = environment
        self.logic = logic

    def _exit(self):
        del self.msat_env

    def _check_logic(self, formulas):
        for f in formulas:
            logic = get_logic(f, self.environment)
            ok = any(logic <= l for l in self.LOGICS)
            if not ok:
                raise PysmtValueError("Logic not supported by MathSAT "
                                      "interpolation. (detected logic is: %s)" \
                                      % str(logic))

    def binary_interpolant(self, a, b):
        res = self.sequence_interpolant([a, b])
        if res is not None:
            res = res[0]
        return res

    def sequence_interpolant(self, formulas):
        cfg, env = None, None
        try:
            self._check_logic(formulas)

            if len(formulas) < 2:
                raise PysmtValueError("interpolation needs at least 2 formulae")

            cfg = mathsat.msat_create_config()
            mathsat.msat_set_option(cfg, "interpolation", "true")
            if self.logic == QF_BV:
                mathsat.msat_set_option(cfg, "theory.bv.eager", "false")
                mathsat.msat_set_option(cfg, "theory.eq_propagaion", "false")
            env = mathsat.msat_create_env(cfg, self.msat_env())

            groups = []
            for f in formulas:
                f = self.converter.convert(f)
                g = mathsat.msat_create_itp_group(env)
                mathsat.msat_set_itp_group(env, g)
                groups.append(g)
                mathsat.msat_assert_formula(env, f)

            res = mathsat.msat_solve(env)
            if res == mathsat.MSAT_UNKNOWN:
                raise InternalSolverError("Error in mathsat interpolation: %s" %
                                          mathsat.msat_last_error_message(env))

            if res == mathsat.MSAT_SAT:
                return None

            pysmt_ret = []
            for i in range(1, len(groups)):
                itp = mathsat.msat_get_interpolant(env, groups[:i])
                f = self.converter.back(itp)
                pysmt_ret.append(f)

            return pysmt_ret
        finally:
            if cfg:
                mathsat.msat_destroy_config(cfg)
            if env:
                mathsat.msat_destroy_env(env)


class MSatBoolUFRewriter(IdentityDagWalker):
    """Rewrites an expression containing UF with boolean arguments into an
       equivalent one with only theory UF.

    This is needed because MathSAT does not support UF with boolean
    arguments. This class could implement different rewriting
    strategies. Eventually, we might consider integrating it into the
    Converter directly.
    """

    def __init__(self, environment):
        IdentityDagWalker.__init__(self, environment)
        self.get_type = self.env.stc.get_type
        self.mgr = self.env.formula_manager

    def walk_function(self, formula, args, **kwargs):
        from pysmt.typing import FunctionType
        # Separate arguments
        bool_args = []
        other_args = []
        for a in args:
            if self.get_type(a).is_bool_type():
                bool_args.append(a)
            else:
                other_args.append(a)

        if len(bool_args) == 0:
            # If no Bool Args, return as-is
            return IdentityDagWalker.walk_function(self, formula, args, **kwargs)

        # Build new function type
        rtype = formula.function_name().symbol_type().return_type
        ptype = [self.get_type(a) for a in other_args]
        if len(ptype) == 0:
            ftype = rtype
        else:
            ftype = FunctionType(rtype, ptype)

        # Base-case
        stack = []
        for i in range(2**len(bool_args)):
            fname = self.mgr.Symbol("%s#%i" % (formula.function_name(),i), ftype)
            if len(ptype) == 0:
                stack.append(fname)
            else:
                stack.append(self.mgr.Function(fname, tuple(other_args)))

        # Recursive case
        for b in bool_args:
            tmp = []
            while len(stack) > 0:
                lhs = stack.pop()
                rhs = stack.pop()
                # Simplify branches, if b is a constant
                if b.is_true():
                    tmp.append(lhs)
                elif b.is_false():
                    tmp.append(rhs)
                else:
                    ite = self.mgr.Ite(b, lhs, rhs)
                    tmp.append(ite)
            stack = tmp
        res = stack[0]
        return res

# EOC MSatBoolUFRewriter
