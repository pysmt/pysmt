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
import atexit
import ctypes

from fractions import Fraction
from six.moves import xrange

from pysmt.exceptions import SolverAPINotFound

try:
    import pyices.context
    import pyices.yices_lib as libyices
    import pyices.fix_env
    from pyices.yices_lib import String
except ImportError:
    raise SolverAPINotFound


from pysmt.solvers.eager import EagerModel
from pysmt.solvers.solver import Solver, Converter
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin

from pysmt.walkers import DagWalker
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.exceptions import InternalSolverError
from pysmt.decorators import clear_pending_pop, catch_conversion_error

import pysmt.logics


# Initialization
def init():
    if not getattr(init, 'initialized', False):
        libyices.yices_init()
    init.initialized = True

def reset_yices():
    libyices.yices_reset()

init()

@atexit.register
def cleanup():
    libyices.yices_exit()

# Yices constants
STATUS_UNKNOWN = 2
STATUS_SAT = 3
STATUS_UNSAT = 4


class YicesSolver(Solver, SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = pysmt.logics.PYSMT_QF_LOGICS

    def __init__(self, environment, logic, user_options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        user_options=user_options)

        self.declarations = set()

        self.yices = libyices.yices_new_context(None)
        self.converter = YicesConverter(environment)
        self.mgr = environment.formula_manager
        self.model = None
        return

    @clear_pending_pop
    def reset_assertions(self):
        raise NotImplementedError

    @clear_pending_pop
    def declare_variable(self, var):
        self.declarations.add(var)
        return

    @clear_pending_pop
    def add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        code = libyices.yices_assert_formula(self.yices, term)
        assert code == 0, "Yices returned non-zero code (" + str(code) + "): " + str(formula)

    def get_model(self):
        assignment = {}
        for s in self.environment.formula_manager.get_all_symbols():
            if s.is_term():
                v = self.get_value(s)
                assignment[s] = v
        return EagerModel(assignment=assignment, environment=self.environment)

    @clear_pending_pop
    def solve(self, assumptions=None):
        if assumptions is not None:
            self.push()
            self.add_assertion(self.mgr.And(assumptions))
            self.pending_pop = True

        out = libyices.yices_check_context(self.yices, None)

        if self.model is not None:
            libyices.yices_free_model(self.model)
            self.model = None

        assert out in [STATUS_SAT, STATUS_UNSAT, STATUS_UNKNOWN]
        if out == STATUS_UNKNOWN:
            raise SolverReturnedUnknownResultError()
        elif out == STATUS_SAT:
            self.model = libyices.yices_get_model(self.yices, 1)
            return True
        else:
            return False

    @clear_pending_pop
    def all_sat(self, important, callback):
        raise NotImplementedError

    @clear_pending_pop
    def push(self, levels=1):
        for _ in xrange(levels):
            c = libyices.yices_push(self.yices)
            assert c == 0

    @clear_pending_pop
    def pop(self, levels=1):
        for _ in xrange(levels):
            c = libyices.yices_pop(self.yices)
            assert c == 0

    def print_model(self, name_filter=None):
        for var in self.declarations:
            if name_filter is None or not var.symbol_name().startswith(name_filter):
                print("%s = %s", (var.symbol_name(), self.get_value(var)))


    def get_value(self, item):
        self._assert_no_function_type(item)

        titem = self.converter.convert(item)
        ty = self.environment.stc.get_type(item)
        if ty.is_bool_type():
            res = self._get_yices_value(titem, ctypes.c_bool(),
                                        libyices.yices_get_bool_value)
            return self.mgr.Bool(res)

        else:
            yval = libyices.yval_t()
            status = libyices.yices_get_value(self.model, titem,
                                              ctypes.byref(yval))
            assert status == 0, "Failed to read the variable from the model"

            if ty.is_int_type():
                if libyices.yices_val_is_int64(self.model,
                                               ctypes.byref(yval)) == 0:
                    raise NotImplementedError("Yices wrapper currently uses "\
                                              "finite-precision integers! "\
                                              "Your query required a non-"\
                                              "representable integer.")
                else:
                    res = self._get_yices_value(titem, ctypes.c_int64(),
                                                libyices.yices_get_int64_value)
                    return self.mgr.Int(res)

            elif ty.is_real_type():
                if libyices.yices_val_is_rational64(self.model,
                                                    ctypes.byref(yval)) == 0:
                    raise NotImplementedError("Yices wrapper currently uses "\
                                              "finite-precision rationals! "\
                                              "Your query required a non-"\
                                              "representable rational.")

                else:
                    res = self._get_yices_rational_value(titem)
                    return self.mgr.Real(res)

            elif ty.is_bv_type():
                width = ty.width
                res = (ctypes.c_int32 * width)()
                libyices.yices_val_get_bv(self.model, ctypes.byref(yval), res)
                str_val = "".join(str(x) for x in reversed(res))
                return self.mgr.BV("#b" + str_val)

            else:
                raise NotImplementedError()

    def _exit(self):
        libyices.yices_free_context(self.yices)

    def _get_yices_value(self, term, term_type, getter_func):
        status = getter_func(
            self.model,
            term,
            ctypes.byref(term_type)
        )
        assert status == 0, "Failed to read the variable from the model"
        return term_type.value

    def _get_yices_rational_value(self, term):
        n = ctypes.c_int64()
        d = ctypes.c_uint64()
        status = libyices.yices_get_rational64_value(
            self.model,
            term,
            ctypes.byref(n),
            ctypes.byref(d))
        assert status == 0, "Failed to read the variable from the model"
        return Fraction(n.value, d.value)


class YicesConverter(Converter, DagWalker):

    def __init__(self, environment):
        DagWalker.__init__(self, environment)
        self.backconversion = {}
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type

        # Maps a Symbol into the corresponding internal yices instance
        self.symbol_to_decl = {}
        # Maps an internal yices instance into the corresponding symbol
        self.decl_to_symbol = {}

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    def _to_term_array(self, arr):
        #pylint: disable=star-args
        return (libyices.term_t * len(arr))(*arr)

    def _check_term_result(self, res):
        if res == -1:
            err = str(libyices.yices_error_string())
            raise InternalSolverError("Yices returned an error: " + err)

    def walk_and(self, formula, args, **kwargs):
        res = libyices.yices_and(len(args), self._to_term_array(args))
        self._check_term_result(res)
        return res

    def walk_or(self, formula, args, **kwargs):
        res = libyices.yices_or(len(args),  self._to_term_array(args))
        self._check_term_result(res)
        return res

    def walk_not(self, formula, args, **kwargs):
        res = libyices.yices_not(args[0])
        self._check_term_result(res)
        return res

    def walk_symbol(self, formula, **kwargs):
        symbol_type = formula.symbol_type()
        var_type = self._type_to_yices(symbol_type)
        term = libyices.yices_new_uninterpreted_term(var_type)
        libyices.yices_set_term_name(term, String(formula.symbol_name()))
        self._check_term_result(term)
        return term

    def _bound_symbol(self, var):
        symbol_type = var.symbol_type()
        var_type = self._type_to_yices(symbol_type)
        term = libyices.yices_new_variable(var_type)
        libyices.yices_set_term_name(term, String(var.symbol_name()))
        return term

    def walk_iff(self, formula, args, **kwargs):
        res = libyices.yices_iff(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_implies(self, formula, args, **kwargs):
        res = libyices.yices_implies(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_le(self, formula, args, **kwargs):
        res = libyices.yices_arith_leq_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_lt(self, formula, args, **kwargs):
        res = libyices.yices_arith_lt_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_ite(self, formula, args, **kwargs):
        i, t, e = args
        res = libyices.yices_ite(i, t, e)
        self._check_term_result(res)
        return res

    def walk_real_constant(self, formula, **kwargs):
        assert type(formula.constant_value()) == Fraction
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        res = libyices.yices_parse_rational(String(rep))
        self._check_term_result(res)
        return res

    def walk_int_constant(self, formula, **kwargs):
        assert type(formula.constant_value()) == int or \
            type(formula.constant_value()) == long
        rep = str(formula.constant_value())
        res = libyices.yices_parse_rational(String(rep))
        self._check_term_result(res)
        return res

    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return libyices.yices_true()
        else:
            return libyices.yices_false()

    def walk_exists(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        arr = self._to_term_array(var_list)
        res = libyices.yices_exists(len(var_list), arr, bound_formula)
        self._check_term_result(res)
        return res

    def walk_forall(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        arr = self._to_term_array(var_list)
        res = libyices.yices_forall(len(var_list), arr, bound_formula)
        self._check_term_result(res)
        return res

    def _rename_bound_variables(self, formula, variables):
        """Bounds the variables in formula.

        Returns a tuple (new_formula, new_var_list) in which the old
        variables have been replaced by the new variables in the list.
        """
        new_vars = [self._bound_symbol(x) for x in variables]
        old_vars = [self.walk_symbol(x, []) for x in variables]
        arr_new = self._to_term_array(new_vars)
        arr_old = self._to_term_array(old_vars)
        new_formula = libyices.yices_subst_term(len(variables), arr_new,
                                                arr_old, formula)
        return (new_formula, new_vars)


    def walk_plus(self, formula, args, **kwargs):
        res = libyices.yices_sum(len(args), self._to_term_array(args))
        self._check_term_result(res)
        return res

    def walk_minus(self, formula, args, **kwargs):
        res = libyices.yices_sub(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_equals(self, formula, args, **kwargs):
        tp = self._get_type(formula.arg(0))
        res = None
        if tp.is_bv_type():
            res = libyices.yices_bveq_atom(args[0], args[1])
        else:
            assert tp.is_int_type() or tp.is_real_type()
            res = libyices.yices_arith_eq_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_times(self, formula, args, **kwargs):
        res = libyices.yices_mul(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_toreal(self, formula, args, **kwargs):
        return args[0]

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()
        if name not in self.symbol_to_decl:
            self.declare_variable(name)
        decl = self.symbol_to_decl[name]
        res = libyices.yices_application(decl, len(args),
                                         self._to_term_array(args))
        self._check_term_result(res)
        return res


    def walk_bv_constant(self, formula, **kwargs):
        width = formula.bv_width()
        res = None
        if width <= 64:
            # we can use the numberical representation
            value = formula.constant_value()
            res = libyices.yices_bvconst_uint64(width, value)
        else:
            # we must resort to strings to communicate the result to yices
            res = libyices.yices_parse_bvbin(formula.bv_bin_str())
        self._check_term_result(res)
        return res

    def walk_bv_ult(self, formula, args, **kwargs):
        res = libyices.yices_bvlt_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_ule(self, formula, args, **kwargs):
        res = libyices.yices_bvle_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_concat(self, formula, args, **kwargs):
        res = libyices.yices_bvconcat2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_extract(self, formula, args, **kwargs):
        res = libyices.yices_bvextract(args[0],
                                       formula.bv_extract_start(),
                                       formula.bv_extract_end())
        self._check_term_result(res)
        return res

    def walk_bv_or(self, formula, args, **kwargs):
        res = libyices.yices_bvor2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_not(self, formula, args, **kwargs):
        res = libyices.yices_bvnot(args[0])
        self._check_term_result(res)
        return res

    def walk_bv_and(self, formula, args, **kwargs):
        res = libyices.yices_bvand2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_xor(self, formula, args, **kwargs):
        res = libyices.yices_bvxor2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_add(self, formula, args, **kwargs):
        res = libyices.yices_bvadd(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_sub(self, formula, args, **kwargs):
        res = libyices.yices_bvsub(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_neg(self, formula, args, **kwargs):
        res = libyices.yices_bvneg(args[0])
        self._check_term_result(res)
        return res

    def walk_bv_mul(self, formula, args, **kwargs):
        res = libyices.yices_bvmul(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_udiv(self, formula, args, **kwargs):
        res = libyices.yices_bvdiv(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_urem(self, formula, args, **kwargs):
        res = libyices.yices_bvrem(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_lshl(self, formula, args, **kwargs):
        res = libyices.yices_bvshl(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_lshr(self, formula, args, **kwargs):
        res = libyices.yices_bvlshr(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_rol(self, formula, args, **kwargs):
        res = libyices.yices_rotate_left(args[0], formula.bv_rotation_step())
        self._check_term_result(res)
        return res

    def walk_bv_ror(self, formula, args, **kwargs):
        res = libyices.yices_rotate_right(args[0], formula.bv_rotation_step())
        self._check_term_result(res)
        return res

    def walk_bv_zext(self, formula, args, **kwargs):
        res = libyices.yices_zero_extend(args[0], formula.bv_extend_step())
        self._check_term_result(res)
        return res

    def walk_bv_sext (self, formula, args, **kwargs):
        res = libyices.yices_sign_extend(args[0], formula.bv_extend_step())
        self._check_term_result(res)
        return res

    def walk_bv_slt(self, formula, args, **kwargs):
        res = libyices.yices_bvslt_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_sle (self, formula, args, **kwargs):
        res = libyices.yices_bvsle_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_comp (self, formula, args, **kwargs):
        a,b = args
        eq = libyices.yices_bveq_atom(a, b)
        self._check_term_result(eq)
        one = libyices.yices_bvconst_int32(1, 1)
        zero = libyices.yices_bvconst_int32(1, 0)
        res = libyices.yices_ite(eq, one, zero)
        self._check_term_result(res)
        return res

    def walk_bv_sdiv (self, formula, args, **kwargs):
        res = libyices.yices_bvsdiv(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_srem (self, formula, args, **kwargs):
        res = libyices.yices_bvsrem(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_ashr (self, formula, args, **kwargs):
        res = libyices.yices_bvashr(args[0], args[1])
        self._check_term_result(res)
        return res


    def _type_to_yices(self, tp):
        if tp.is_bool_type():
            return libyices.yices_bool_type()
        elif tp.is_real_type():
            return libyices.yices_real_type()
        elif tp.is_int_type():
            return libyices.yices_int_type()
        elif tp.is_function_type():
            stps = [self._type_to_yices(x) for x in tp.param_types]
            rtp = self._type_to_yices(tp.return_type)
            #pylint: disable=star-args
            arr = (libyices.type_t * len(stps))(*stps)
            return libyices.yices_function_type(len(stps),
                                                arr,
                                                rtp)
        elif tp.is_bv_type():
            return libyices.yices_bv_type(tp.width)
        else:
            raise NotImplementedError

    def declare_variable(self, var):
        if not var.is_symbol(): raise TypeError
        if var.symbol_name() not in self.symbol_to_decl:
            tp = self._type_to_yices(var.symbol_type())
            decl = libyices.yices_new_uninterpreted_term(tp)
            libyices.yices_set_term_name(decl, String(var.symbol_name()))
            self.symbol_to_decl[var] = decl
            self.decl_to_symbol[decl] = var
