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
from warnings import warn

from six.moves import xrange

from pysmt.exceptions import SolverAPINotFound

try:
    import yicespy
except ImportError:
    raise SolverAPINotFound


from pysmt.solvers.eager import EagerModel
from pysmt.solvers.solver import Solver, Converter, SolverOptions
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin

from pysmt.walkers import DagWalker
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.exceptions import (InternalSolverError, NonLinearError,
                              PysmtValueError, PysmtTypeError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.constants import Fraction, is_pysmt_integer

import pysmt.logics


# Initialization
def init():
    if not getattr(init, 'initialized', False):
        yicespy.yices_init()
    init.initialized = True

def reset_yices():
    yicespy.yices_reset()

init()

@atexit.register
def cleanup():
    yicespy.yices_exit()

# Yices constants
STATUS_UNKNOWN = 2
STATUS_SAT = 3
STATUS_UNSAT = 4

def yices_logic(pysmt_logic):
    """Return a Yices String representing the given pySMT logic."""
    ylogic = str(pysmt_logic)
    if ylogic == "QF_BOOL":
        ylogic = "NONE"
    return ylogic


class YicesOptions(SolverOptions):
    def __init__(self, **base_options):
        SolverOptions.__init__(self, **base_options)
        # TODO: Yices Supports UnsatCore extraction
        # but we did not wrapped it yet.
        if self.unsat_cores_mode is not None:
            raise PysmtValueError("'unsat_cores_mode' option not supported.")

    @staticmethod
    def _set_option(cfg, name, value):
        rv = yicespy.yices_set_config(cfg, name, value)
        if rv != 0:
            # This might be a parameter to be set later (see set_params)
            # We raise the exception only if the parameter exists but the value
            # provided to the parameter is invalid.
            err = yicespy.yices_error_code()
            if err == yicespy.CTX_INVALID_PARAMETER_VALUE:
                raise PysmtValueError("Error setting the option "
                                      "'%s=%s'" % (name,value))

    def __call__(self, solver):
        if self.generate_models:
            # Yices always generates models
            pass
        if self.incremental:
            self._set_option(solver.yices_config, "mode", "push-pop")
        else:
            self._set_option(solver.yices_config, "mode", "one-shot")

        if self.random_seed is not None:
            self._set_option(solver.yices_config,
                             "random-seed", str(self.random_seed))

        for k,v in self.solver_options.items():
            self._set_option(solver.yices_config, str(k), str(v))

    def set_params(self, solver):
        """Set Search Parameters.

        Yices makes a distinction between configuratin and search
        parameters.  The first are fixed for the lifetime of a
        context, while the latter can be different for every call to
        check_context.

        A list of available parameters is available at:
        http://yices.csl.sri.com/doc/parameters.html
        """
        params = yicespy.yices_new_param_record()
        yicespy.yices_default_params_for_context(solver.yices, params)
        for k,v in self.solver_options.items():
            rv = yicespy.yices_set_param(params, k, v)
            if rv != 0:
                raise PysmtValueError("Error setting the option '%s=%s'" % (k,v))
        solver.yices_params = params

# EOC YicesOptions


class YicesSolver(Solver, SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = pysmt.logics.PYSMT_QF_LOGICS -\
             pysmt.logics.ARRAYS_LOGICS -\
             set(l for l in pysmt.logics.PYSMT_QF_LOGICS
                 if not l.theory.linear or l.theory.strings)
    OptionsClass = YicesOptions

    def __init__(self, environment, logic, **options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        **options)

        self.declarations = set()
        self.yices_config = yicespy.yices_new_config()
        if yicespy.yices_default_config_for_logic(self.yices_config,
                                                  yices_logic(logic)) != 0:
            warn("Error setting config for logic %s" % logic)
        self.options(self)
        self.yices = yicespy.yices_new_context(self.yices_config)
        self.options.set_params(self)
        yicespy.yices_free_config(self.yices_config)
        self.converter = YicesConverter(environment)
        self.mgr = environment.formula_manager
        self.model = None
        self.failed_pushes = 0
        return

    @clear_pending_pop
    def reset_assertions(self):
        yicespy.yices_reset_context(self.yices)

    @clear_pending_pop
    def declare_variable(self, var):
        raise NotImplementedError

    @clear_pending_pop
    def add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        code = yicespy.yices_assert_formula(self.yices, term)
        if code != 0:
            msg = yicespy.yices_error_string()
            if code == -1 and "non-linear arithmetic" in msg:
                raise NonLinearError(formula)
            raise InternalSolverError("Yices returned non-zero code upon assert"\
                                      ": %s (code: %s)" % \
                                      (msg, code))

    def get_model(self):
        assignment = {}
        # MG: This iteration is problematic, since it assumes that all
        # defined symbols have a type that is compatible with this
        # solver.  In this case, the problem occurs with Arrays and
        # Strings that are not supported.
        for s in self.environment.formula_manager.get_all_symbols():
            if s.is_symbol() and s.symbol_type().is_string_type():
                continue
            if s.is_term():
                if s.symbol_type().is_array_type(): continue
                if s.symbol_type().is_custom_type(): continue
                v = self.get_value(s)
                assignment[s] = v
        return EagerModel(assignment=assignment, environment=self.environment)

    @clear_pending_pop
    def solve(self, assumptions=None):
        if assumptions is not None:
            self.push()
            self.add_assertion(self.mgr.And(assumptions))
            self.pending_pop = True

        out = yicespy.yices_check_context(self.yices, self.yices_params)

        if self.model is not None:
            yicespy.yices_free_model(self.model)
            self.model = None

        assert out in [STATUS_SAT, STATUS_UNSAT, STATUS_UNKNOWN]
        if out == STATUS_UNKNOWN:
            raise SolverReturnedUnknownResultError()
        elif out == STATUS_SAT:
            self.model = yicespy.yices_get_model(self.yices, 1)
            return True
        else:
            return False

    @clear_pending_pop
    def all_sat(self, important, callback):
        raise NotImplementedError

    @clear_pending_pop
    def push(self, levels=1):
        for _ in xrange(levels):
            c = yicespy.yices_push(self.yices)
            if c != 0:
                # 4 is STATUS_UNSAT
                if yicespy.yices_context_status(self.yices) == 4:
                    # Yices fails to push if the context is in UNSAT state
                    # (It makes no sense to conjoin formulae to False)
                    # PySMT allows this and we support it by counting the
                    # spurious push calls
                    self.failed_pushes += 1
                else:
                    raise InternalSolverError("Error in push: %s" % \
                                              yicespy.yices_error_string())

    @clear_pending_pop
    def pop(self, levels=1):
        for _ in xrange(levels):
            if self.failed_pushes > 0:
                self.failed_pushes -= 1
            else:
                c = yicespy.yices_pop(self.yices)
                if c != 0:
                    raise InternalSolverError("Error in pop: %s" % \
                                              yicespy.yices_error_string())

    def print_model(self, name_filter=None):
        for var in self.declarations:
            if name_filter is None or not var.symbol_name().startswith(name_filter):
                print("%s = %s", (var.symbol_name(), self.get_value(var)))

    def _check_error(self, res):
        if res != 0:
            err = yicespy.yices_error_string()
            raise InternalSolverError("Yices returned an error: " + err)

    def get_value(self, item):
        self._assert_no_function_type(item)

        titem = self.converter.convert(item)
        ty = self.environment.stc.get_type(item)
        if ty.is_bool_type():
            status, res = yicespy.yices_get_bool_value(self.model, titem)
            self._check_error(status)
            return self.mgr.Bool(bool(res))
        elif ty.is_int_type():
            res = yicespy.yices_get_integer_value(self.model, titem)
            return self.mgr.Int(res)
        elif ty.is_real_type():
            status, val = yicespy.yices_get_rational_value(self.model, titem)
            self._check_error(status)
            return self.mgr.Real(Fraction(val))
        elif ty.is_bv_type():
            status, res = yicespy.yices_get_bv_value(self.model, titem,  ty.width)
            self._check_error(status)
            str_val = "".join(str(x) for x in reversed(res))
            return self.mgr.BV("#b" + str_val)
        else:
            raise NotImplementedError()

    def _exit(self):
        yicespy.yices_free_context(self.yices)
        yicespy.yices_free_param_record(self.yices_params)

# EOC YicesSolver


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
        self._yicesSort = {}

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    def _check_term_result(self, res):
        if res == -1:
            err = yicespy.yices_error_string()
            raise InternalSolverError("Yices returned an error: " + err)

    def walk_and(self, formula, args, **kwargs):
        res = yicespy.yices_and(len(args), args)
        self._check_term_result(res)
        return res

    def walk_or(self, formula, args, **kwargs):
        res = yicespy.yices_or(len(args), args)
        self._check_term_result(res)
        return res

    def walk_not(self, formula, args, **kwargs):
        res = yicespy.yices_not(args[0])
        self._check_term_result(res)
        return res

    def walk_symbol(self, formula, **kwargs):
        symbol_type = formula.symbol_type()
        var_type = self._type_to_yices(symbol_type)
        term = yicespy.yices_new_uninterpreted_term(var_type)
        yicespy.yices_set_term_name(term, formula.symbol_name())
        self._check_term_result(term)
        return term

    def _bound_symbol(self, var):
        symbol_type = var.symbol_type()
        var_type = self._type_to_yices(symbol_type)
        term = yicespy.yices_new_variable(var_type)
        yicespy.yices_set_term_name(term, var.symbol_name())
        return term

    def walk_iff(self, formula, args, **kwargs):
        res = yicespy.yices_iff(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_implies(self, formula, args, **kwargs):
        res = yicespy.yices_implies(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_le(self, formula, args, **kwargs):
        res = yicespy.yices_arith_leq_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_lt(self, formula, args, **kwargs):
        res = yicespy.yices_arith_lt_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_ite(self, formula, args, **kwargs):
        i, t, e = args
        res = yicespy.yices_ite(i, t, e)
        self._check_term_result(res)
        return res

    def walk_real_constant(self, formula, **kwargs):
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        res = yicespy.yices_parse_rational(rep)
        self._check_term_result(res)
        return res

    def walk_int_constant(self, formula, **kwargs):
        assert is_pysmt_integer(formula.constant_value())
        rep = str(formula.constant_value())
        res = yicespy.yices_parse_rational(rep)
        self._check_term_result(res)
        return res

    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return yicespy.yices_true()
        else:
            return yicespy.yices_false()

    def walk_exists(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        res = yicespy.yices_exists(len(var_list), var_list, bound_formula)
        self._check_term_result(res)
        return res

    def walk_forall(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        res = yicespy.yices_forall(len(var_list), var_list, bound_formula)
        self._check_term_result(res)
        return res

    def _rename_bound_variables(self, formula, variables):
        """Bounds the variables in formula.

        Returns a tuple (new_formula, new_var_list) in which the old
        variables have been replaced by the new variables in the list.
        """
        new_vars = [self._bound_symbol(x) for x in variables]
        old_vars = [self.walk_symbol(x, []) for x in variables]
        new_formula = yicespy.yices_subst_term(len(variables), new_vars,
                                                old_vars, formula)
        return (new_formula, new_vars)


    def walk_plus(self, formula, args, **kwargs):
        res = yicespy.yices_sum(len(args), args)
        self._check_term_result(res)
        return res

    def walk_minus(self, formula, args, **kwargs):
        res = yicespy.yices_sub(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_equals(self, formula, args, **kwargs):
        tp = self._get_type(formula.arg(0))
        res = None
        if tp.is_bv_type():
            res = yicespy.yices_bveq_atom(args[0], args[1])
        elif tp.is_int_type() or tp.is_real_type():
            res = yicespy.yices_arith_eq_atom(args[0], args[1])
        else:
            assert tp.is_custom_type()
            res = yicespy.yices_eq(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_times(self, formula, args, **kwargs):
        res = args[0]
        for x in args[1:]:
            res = yicespy.yices_mul(res, x)
            self._check_term_result(res)
        return res

    def walk_toreal(self, formula, args, **kwargs):
        return args[0]

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()
        if name not in self.symbol_to_decl:
            self.declare_variable(name)
        decl = self.symbol_to_decl[name]
        res = yicespy.yices_application(decl, len(args), args)
        self._check_term_result(res)
        return res


    def walk_bv_constant(self, formula, **kwargs):
        width = formula.bv_width()
        res = None
        if width <= 64:
            # we can use the numberical representation
            value = formula.constant_value()
            res = yicespy.yices_bvconst_uint64(width, value)
        else:
            # we must resort to strings to communicate the result to yices
            res = yicespy.yices_parse_bvbin(formula.bv_bin_str())
        self._check_term_result(res)
        return res

    def walk_bv_ult(self, formula, args, **kwargs):
        res = yicespy.yices_bvlt_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_ule(self, formula, args, **kwargs):
        res = yicespy.yices_bvle_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_concat(self, formula, args, **kwargs):
        res = yicespy.yices_bvconcat2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_extract(self, formula, args, **kwargs):
        res = yicespy.yices_bvextract(args[0],
                                       formula.bv_extract_start(),
                                       formula.bv_extract_end())
        self._check_term_result(res)
        return res

    def walk_bv_or(self, formula, args, **kwargs):
        res = yicespy.yices_bvor2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_not(self, formula, args, **kwargs):
        res = yicespy.yices_bvnot(args[0])
        self._check_term_result(res)
        return res

    def walk_bv_and(self, formula, args, **kwargs):
        res = yicespy.yices_bvand2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_xor(self, formula, args, **kwargs):
        res = yicespy.yices_bvxor2(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_add(self, formula, args, **kwargs):
        res = yicespy.yices_bvadd(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_sub(self, formula, args, **kwargs):
        res = yicespy.yices_bvsub(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_neg(self, formula, args, **kwargs):
        res = yicespy.yices_bvneg(args[0])
        self._check_term_result(res)
        return res

    def walk_bv_mul(self, formula, args, **kwargs):
        res = yicespy.yices_bvmul(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_udiv(self, formula, args, **kwargs):
        res = yicespy.yices_bvdiv(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_urem(self, formula, args, **kwargs):
        res = yicespy.yices_bvrem(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_lshl(self, formula, args, **kwargs):
        res = yicespy.yices_bvshl(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_lshr(self, formula, args, **kwargs):
        res = yicespy.yices_bvlshr(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_rol(self, formula, args, **kwargs):
        res = yicespy.yices_rotate_left(args[0], formula.bv_rotation_step())
        self._check_term_result(res)
        return res

    def walk_bv_ror(self, formula, args, **kwargs):
        res = yicespy.yices_rotate_right(args[0], formula.bv_rotation_step())
        self._check_term_result(res)
        return res

    def walk_bv_zext(self, formula, args, **kwargs):
        res = yicespy.yices_zero_extend(args[0], formula.bv_extend_step())
        self._check_term_result(res)
        return res

    def walk_bv_sext (self, formula, args, **kwargs):
        res = yicespy.yices_sign_extend(args[0], formula.bv_extend_step())
        self._check_term_result(res)
        return res

    def walk_bv_slt(self, formula, args, **kwargs):
        res = yicespy.yices_bvslt_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_sle (self, formula, args, **kwargs):
        res = yicespy.yices_bvsle_atom(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_comp (self, formula, args, **kwargs):
        a,b = args
        eq = yicespy.yices_bveq_atom(a, b)
        self._check_term_result(eq)
        one = yicespy.yices_bvconst_int32(1, 1)
        zero = yicespy.yices_bvconst_int32(1, 0)
        res = yicespy.yices_ite(eq, one, zero)
        self._check_term_result(res)
        return res

    def walk_bv_sdiv (self, formula, args, **kwargs):
        res = yicespy.yices_bvsdiv(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_srem (self, formula, args, **kwargs):
        res = yicespy.yices_bvsrem(args[0], args[1])
        self._check_term_result(res)
        return res

    def walk_bv_ashr (self, formula, args, **kwargs):
        res = yicespy.yices_bvashr(args[0], args[1])
        self._check_term_result(res)
        return res

    def yicesSort(self, name):
        """Return the yices Sort for the given name."""
        name = str(name)
        try:
            return self._yicesSort[name]
        except KeyError:
            sort = yicespy.yices_new_uninterpreted_type()
            self._yicesSort[name] = sort
        return sort

    def _type_to_yices(self, tp):
        if tp.is_bool_type():
            return yicespy.yices_bool_type()
        elif tp.is_real_type():
            return yicespy.yices_real_type()
        elif tp.is_int_type():
            return yicespy.yices_int_type()
        elif tp.is_function_type():
            stps = [self._type_to_yices(x) for x in tp.param_types]
            rtp = self._type_to_yices(tp.return_type)
            #arr = (yicespy.type_t * len(stps))(*stps)
            return yicespy.yices_function_type(len(stps),
                                              stps,
                                              rtp)
        elif tp.is_bv_type():
            return yicespy.yices_bv_type(tp.width)
        elif tp.is_custom_type():
            return self.yicesSort(str(tp))
        else:
            raise NotImplementedError(tp)

    def declare_variable(self, var):
        if not var.is_symbol():
            raise PysmtTypeError("Trying to declare as a variable something "
                                 "that is not a symbol: %s" % var)
        if var.symbol_name() not in self.symbol_to_decl:
            tp = self._type_to_yices(var.symbol_type())
            decl = yicespy.yices_new_uninterpreted_term(tp)
            yicespy.yices_set_term_name(decl, var.symbol_name())
            self.symbol_to_decl[var] = decl
            self.decl_to_symbol[decl] = var
