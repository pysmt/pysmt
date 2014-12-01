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
import warnings

from fractions import Fraction

import pyices.context
import pyices.yices_lib as libyices
import pyices.fix_env
from pyices.yices_lib import String

from pysmt.solvers.eager import EagerModel
from pysmt.solvers.solver import Solver
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin

from pysmt.walkers import DagWalker
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.decorators import clear_pending_pop


import pysmt.logics


# Initialization
def init():
    if not getattr(init, '_initialized', False):
        libyices.yices_init()
    init._initialized = True

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

    def __init__(self, environment, logic=None, options=None):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        options=options)

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
                print var.symbol_name(), "=", self.get_value(var)


    def get_value(self, item):
        self._assert_no_function_type(item)

        titem = self.converter.convert(item)
        ty = self.environment.stc.get_type(item)
        if ty.is_bool_type():
            res = self._get_yices_value(titem, ctypes.c_bool(),
                                        libyices.yices_get_bool_value)
            return self.mgr.Bool(res)

        elif ty.is_int_type():
            res = self._get_yices_value(titem, ctypes.c_int(),
                                        libyices.yices_get_int32_value)
            return self.mgr.Int(res)

        elif ty.is_real_type():
            res = self._get_yices_value(titem, ctypes.c_double(),
                                        libyices.yices_get_double_value)
            warnings.warn("yices wrapper currently uses finite-precision reals!")
            return self.mgr.Real(res)
        else:
            raise NotImplementedError()


    def destroy(self):
        return self.exit()

    def exit(self):
        libyices.yices_free_context(self.yices)


    def _get_yices_value(self, term, term_type, getter_func):
        status = getter_func(
            self.model,
            term,
            ctypes.byref(term_type)
        )
        assert status == 0, "Failed to read the variable from the model"
        return term_type.value



class YicesConverter(DagWalker):

    def __init__(self, environment):
        DagWalker.__init__(self, environment)
        self.backconversion = {}
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type

        # Maps a Symbol into the corresponding internal yices instance
        self.symbol_to_decl = {}
        # Maps an internal yices instance into the corresponding symbol
        self.decl_to_symbol = {}


    def convert(self, formula):
        return self.walk(formula)


    def walk_and(self, formula, args):
        arr = (libyices.term_t * len(args))(*args)
        return libyices.yices_and(len(args), arr)

    def walk_or(self, formula, args):
        arr = (libyices.term_t * len(args))(*args)
        return libyices.yices_or(len(args), arr)

    def walk_not(self, formula, args):
        assert len(args) == 1
        return libyices.yices_not(args[0])

    def walk_symbol(self, formula, args):
        assert len(args) == 0
        symbol_type = formula.symbol_type()
        var_type = self._type_to_yices(symbol_type)
        term = libyices.yices_new_uninterpreted_term(var_type)
        libyices.yices_set_term_name(term, String(formula.symbol_name()))
        return term

    def _bound_symbol(self, var):
        symbol_type = var.symbol_type()
        var_type = self._type_to_yices(symbol_type)
        term = libyices.yices_new_variable(var_type)
        libyices.yices_set_term_name(term, String(var.symbol_name()))
        return term

    def walk_iff(self, formula, args):
        assert len(args) == 2
        return libyices.yices_iff(args[0], args[1])

    def walk_implies(self, formula, args):
        assert len(args) == 2
        return libyices.yices_implies(args[0], args[1])

    def walk_le(self, formula, args):
        assert len(args) == 2
        return libyices.yices_arith_leq_atom(args[0], args[1])

    def walk_lt(self, formula, args):
        assert len(args) == 2
        return libyices.yices_arith_lt_atom(args[0], args[1])

    def walk_ite(self, formula, args):
        assert len(args) == 3
        i, t, e = args
        return libyices.yices_ite(i, t, e)

    def walk_real_constant(self, formula, args):
        assert len(args) == 0
        assert type(formula.constant_value()) == Fraction
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        return libyices.yices_parse_rational(String(rep))

    def walk_int_constant(self, formula, args):
        assert len(args) == 0
        assert type(formula.constant_value()) == int or \
            type(formula.constant_value()) == long
        rep = str(formula.constant_value())
        return libyices.yices_parse_rational(String(rep))

    def walk_bool_constant(self, formula, args):
        assert len(args) == 0
        if formula.constant_value():
            return libyices.yices_true()
        else:
            return libyices.yices_false()

    def walk_exists(self, formula, args):
        assert len(args) == 1
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        arr = (libyices.term_t * len(var_list))(*var_list)
        return libyices.yices_exists(len(var_list), arr, bound_formula)

    def walk_forall(self, formula, args):
        assert len(args) == 1
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        arr = (libyices.term_t * len(var_list))(*var_list)
        return libyices.yices_forall(len(var_list), arr, bound_formula)

    def _rename_bound_variables(self, formula, variables):
        """Bounds the variables in formula.

        Returns a tuple (new_formula, new_var_list) in which the old
        variables have been replaced by the new variables in the list.
        """
        new_vars = [self._bound_symbol(x) for x in variables]
        old_vars = [self.walk_symbol(x, []) for x in variables]
        arr_new = (libyices.term_t * len(new_vars))(*new_vars)
        arr_old = (libyices.term_t * len(old_vars))(*old_vars)
        new_formula = libyices.yices_subst_term(len(variables), arr_new,
                                                arr_old, formula)
        return (new_formula, new_vars)


    def walk_plus(self, formula, args):
        assert len(args) >= 2
        arr = (libyices.term_t * len(args))(*args)
        return libyices.yices_sum(len(args), arr)

    def walk_minus(self, formula, args):
        assert len(args) == 2
        return libyices.yices_sub(args[0], args[1])

    def walk_equals(self, formula, args):
        assert len(args) == 2
        return libyices.yices_arith_eq_atom(args[0], args[1])

    def walk_times(self, formula, args):
        assert len(args) == 2
        return libyices.yices_mul(args[0], args[1])

    def walk_toreal(self, formula, args):
        assert len(args) == 1
        return args[0]

    def walk_function(self, formula, args):
        name = formula.function_name()
        if name not in self.symbol_to_decl:
            self.declare_variable(name)
        decl = self.symbol_to_decl[name]
        arr = (libyices.term_t * len(args))(*args)
        return libyices.yices_application(decl, len(args), arr)

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
            arr = (libyices.type_t * len(stps))(*stps)
            return libyices.yices_function_type(len(stps),
                                                arr,
                                                rtp)
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
