#
# This file is part of pySMT.
#
#   Copyright 2015 Andrea Micheli and Marco Gario
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
    import cvc5
except ImportError:
    raise SolverAPINotFound

from cvc5 import Kind

import pysmt.typing as types
from pysmt.logics import PYSMT_LOGICS, ARRAYS_CONST_LOGICS

from pysmt.solvers.solver import Solver, Converter, SolverOptions
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              InternalSolverError,
                              NonLinearError, PysmtValueError,
                              PysmtTypeError)
from pysmt.walkers import DagWalker
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.eager import EagerModel
from pysmt.decorators import catch_conversion_error
from pysmt.constants import Fraction, is_pysmt_integer, to_python_integer


class CVC5Options(SolverOptions):

    def __init__(self, **base_options):
        SolverOptions.__init__(self, **base_options)
        # TODO: CVC5 Supports UnsatCore extraction
        # but we did not wrapped it yet. (See #359)
        if self.unsat_cores_mode is not None:
            raise PysmtValueError("'unsat_cores_mode' option not supported.")

    @staticmethod
    def _set_option(cvc5, name, value):
        try:
            cvc5.setOption(name, value)
        except:
            raise PysmtValueError("Error setting the option '%s=%s'" % (name,value))

    def __call__(self, solver):
        if solver.logic_name == "QF_SLIA":
            self._set_option(solver.cvc5,
                             "strings-exp", "true")

        self._set_option(solver.cvc5,
                         "produce-models", str(self.generate_models).lower())
        self._set_option(solver.cvc5,
                         "incremental", str(self.incremental).lower())
        if self.random_seed is not None:
            self._set_option(solver.cvc5,
                             "seed", str(self.random_seed))

        # self._set_option(solver.cvc5, "miplib-trick", "true")
        # self._set_option(solver.cvc5, "miplib-trick-subs", "4")
        # self._set_option(solver.cvc5, "use-approx", "true")
        # self._set_option(solver.cvc5, "lemmas-on-replay-failure", "true")
        # self._set_option(solver.cvc5, "replay-early-close-depth", "4")
        # self._set_option(solver.cvc5, "replay-lemma-reject-cut", "128")
        # self._set_option(solver.cvc5, "replay-reject-cut", "512")
        # self._set_option(solver.cvc5, "unconstrained-simp", "true")
        # self._set_option(solver.cvc5, "use-soi", "true")
        # self._set_option(solver.cvc5, "pb-rewrites", "true")
        self._set_option(solver.cvc5, "ite-simp", "true")
        self._set_option(solver.cvc5, "simp-ite-compress", "true")

        #self._set_option(solver.cvc5, "nl-ext-tplanes", "true")


        for k,v in self.solver_options.items():
            self._set_option(solver.cvc5, str(k), str(v))

# EOC CVC5Options


class CVC5Solver(Solver, SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = PYSMT_LOGICS -\
             ARRAYS_CONST_LOGICS

    OptionsClass = CVC5Options

    def __init__(self, environment, logic, **options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        **options)
        self.cvc5 = cvc5.Solver()
        self.declarations = None
        self.logic_name = str(logic)
        if "t" in self.logic_name:
            # Custom Type extension
            self.logic_name = self.logic_name.replace("t","")
        if self.logic_name == "QF_BOOL":
            self.logic_name = "QF_LRA"
        elif self.logic_name == "BOOL":
            self.logic_name = "LRA"
        self.cvc5.setLogic(self.logic_name)

        self.options(self)

        self.converter = CVC5Converter(environment, cvc5=self.cvc5)

    def reset_assertions(self):
        self.cvc5.resetAssertions()

    def declare_variable(self, var):
        raise NotImplementedError

    def add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        self.cvc5.assertFormula(term)

    def get_model(self):
        assignment = {}
        for s in self.environment.formula_manager.get_all_symbols():
            if s.is_term():
                if s.symbol_type().is_custom_type(): continue
                v = self.get_value(s)
                assignment[s] = v
        return EagerModel(assignment=assignment, environment=self.environment)

    def solve(self, assumptions=None):
        if assumptions is not None:
            cvc5_assumptions = [self.converter.convert(a) for a in assumptions]
            res = self.cvc5.checkSatAssuming(*cvc5_assumptions)
        else:
            try:
                res = self.cvc5.checkSat()
            except Exception as ex:
                raise InternalSolverError(str(ex))

        # Convert returned type
        if res.isUnknown():
            raise SolverReturnedUnknownResultError()
        else:
            return res.isSat()

    def push(self, levels=1):
        if not self.options.incremental:
            # The exceptions from CVC5 are not raised correctly
            # (probably due to the wrapper)
            # Therefore, we need to check that we can actually do a push
            raise NotImplementedError("The solver is not incremental")

        for _ in range(levels):
            self.cvc5.push()
        return

    def pop(self, levels=1):
        for _ in range(levels):
            self.cvc5.pop()
        return

    def print_model(self, name_filter=None):
        if name_filter is None:
            var_set = self.declarations
        else:
            var_set = (var for var in self.declarations\
                       if name_filter(var))
        for var in var_set:
            print("%s = %s", (var.symbol_name(), self.get_value(var)))
        return

    def get_value(self, item):
        self._assert_no_function_type(item)
        term = self.converter.convert(item)
        cvc5_res = self.cvc5.getValue(term)
        res = self.converter.back(cvc5_res)
        if self.environment.stc.get_type(item).is_real_type() and \
           self.environment.stc.get_type(res).is_int_type():
            res = self.environment.formula_manager.Real(Fraction(res.constant_value(), 1))
        return res

    def _exit(self):
        del self.cvc5

    def set_option(self, name, value):
        """Sets an option.

        :param name and value: Option to be set
        :type name: String
        :type value: String
        """
        self.cvc5.setOption(name, value)



class CVC5Converter(Converter, DagWalker):

    def __init__(self, environment, cvc5):
        DagWalker.__init__(self, environment)

        self.cvc5 = cvc5

        self.declared_vars = {}
        self.backconversion = {}
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type
        return

    def declare_variable(self, var):
        if not var.is_symbol():
            raise PysmtTypeError("Trying to declare as a variable something "
                                 "that is not a symbol: %s" % var)
        if var.symbol_name() not in self.declared_vars:
            cvc5_type = self._type_to_cvc5(var.symbol_type())
            decl = self.cvc5.mkConst(cvc5_type, var.symbol_name())
            self.declared_vars[var] = decl

    def back(self, expr):
        res = None
        if expr.isBooleanValue():
            v = expr.getBooleanValue()
            res = self.mgr.Bool(v)
        elif expr.isIntegerValue():
            v = expr.getIntegerValue()
            res = self.mgr.Int(int(v))
        elif expr.isRealValue():
            v = expr.getRealValue()
            res = self.mgr.Real(Fraction(v))
        elif expr.isBitVectorValue():
            w = expr.getSort().getBitVectorSize()
            res = self.mgr.BV(str(expr), w)
        elif expr.isStringValue():
            s = expr.getStringValue()
            res = self.mgr.String(s)
        elif expr.isConstArray():
            const_ = expr.getConstArrayBase()
            array_type = self._cvc5_type_to_type(expr.getSort())
            base_value = self.back(const_)
            res = self.mgr.Array(array_type.index_type, base_value)
        else:
            raise PysmtTypeError("Unsupported expression:", str(expr))

        return res

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    def walk_and(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.AND, *args)

    def walk_or(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.OR, *args)

    def walk_not(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.NOT, *args)

    def walk_symbol(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if formula not in self.declared_vars:
            self.declare_variable(formula)
        return self.declared_vars[formula]

    def walk_iff(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.EQUAL, args[0], args[1])

    def walk_implies(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.IMPLIES, args[0], args[1])

    def walk_le(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.LEQ, args[0], args[1])

    def walk_lt(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.LT, args[0], args[1])

    def walk_ite(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.ITE, args[0], args[1], args[2])

    def walk_real_constant(self, formula, **kwargs):
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        return self.cvc5.mkReal(rep)

    def walk_int_constant(self, formula, **kwargs):
        assert is_pysmt_integer(formula.constant_value())
        rep = str(formula.constant_value())
        return self.cvc5.mkInteger(rep)

    def walk_bool_constant(self, formula, **kwargs):
        return self.cvc5.mkBoolean(formula.constant_value())

    def walk_exists(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        bound_vars_list = self.cvc5.mkTerm(Kind.VARIABLE_LIST, *var_list)
        return self.cvc5.mkTerm(Kind.EXISTS,
                           bound_vars_list,
                           bound_formula)

    def walk_forall(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        bound_vars_list = self.cvc5.mkTerm(Kind.VARIABLE_LIST, *var_list)
        return self.cvc5.mkTerm(Kind.FORALL,
                           bound_vars_list,
                           bound_formula)

    def walk_plus(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.ADD, *args)

    def walk_array_store(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STORE, args[0], args[1], args[2])

    def walk_array_select(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.SELECT, args[0], args[1])

    def walk_minus(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.SUB, args[0], args[1])

    def walk_equals(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.EQUAL, args[0], args[1])

    def walk_times(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.MULT, *args)

    def walk_div(self, formula, args, **kwargs):
        if self.env.stc.get_type(formula).is_int_type():
            return self.cvc5.mkTerm(Kind.INTS_DIVISION, *args)
        else:
            return self.cvc5.mkTerm(Kind.DIVISION, *args)

    def walk_pow(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.POW, args[0], self.cvc5.mkTerm(Kind.TO_REAL, args[1]))

    def walk_toreal(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.TO_REAL, args[0])

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()
        if name not in self.declared_vars:
            self.declare_variable(name)
        decl = self.declared_vars[name]
        return self.cvc5.mkTerm(Kind.APPLY_UF, decl, *args)

    def walk_bv_constant(self, formula, **kwargs):
        v = formula.constant_value()
        width = formula.bv_width()
        return self.cvc5.mkBitVector(width, str(v), 10)

    def walk_bv_ult(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_ULT, args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_ULE, args[0], args[1])

    def walk_bv_concat(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_CONCAT, args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        ext = self.cvc5.mkOp(Kind.BITVECTOR_EXTRACT,
                             formula.bv_extract_end(),
                             formula.bv_extract_start())
        return self.cvc5.mkTerm(ext, args[0])

    def walk_bv_or(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_OR, args[0], args[1])

    def walk_bv_not(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_NOT, args[0])

    def walk_bv_and(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_AND, args[0], args[1])

    def walk_bv_xor(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_XOR, args[0], args[1])

    def walk_bv_add(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_ADD, *args)

    def walk_bv_sub(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_SUB, args[0], args[1])

    def walk_bv_neg(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_NEG, args[0])

    def walk_bv_mul(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_MULT, args[0], args[1])

    def walk_bv_tonatural(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_TO_NAT, args[0])

    def walk_bv_udiv(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_UDIV, *args)

    def walk_bv_urem(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_UREM, *args)

    def walk_bv_lshl(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_SHL, args[0], args[1])

    def walk_bv_lshr(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_LSHR, args[0], args[1])

    def walk_bv_rol(self, formula, args, **kwargs):
        ext = self.cvc5.mkOp(Kind.BITVECTOR_ROTATE_LEFT, formula.bv_rotation_step())
        return self.cvc5.mkTerm(ext, args[0])

    def walk_bv_ror(self, formula, args, **kwargs):
        ext = self.cvc5.mkOp(Kind.BITVECTOR_ROTATE_RIGHT, formula.bv_rotation_step())
        return self.cvc5.mkTerm(ext, args[0])

    def walk_bv_zext(self, formula, args, **kwargs):
        ext = self.cvc5.mkOp(Kind.BITVECTOR_ZERO_EXTEND, formula.bv_extend_step())
        return self.cvc5.mkTerm(ext, args[0])

    def walk_bv_sext (self, formula, args, **kwargs):
        ext = self.cvc5.mkOp(Kind.BITVECTOR_SIGN_EXTEND, formula.bv_extend_step())
        return self.cvc5.mkTerm(ext, args[0])

    def walk_bv_slt(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_SLT, args[0], args[1])

    def walk_bv_sle(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_SLE, args[0], args[1])

    def walk_bv_comp(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_COMP, args[0], args[1])

    def walk_bv_sdiv(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_SDIV, *args)

    def walk_bv_srem(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_SREM, *args)

    def walk_bv_ashr(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.BITVECTOR_ASHR, args[0], args[1])

    def walk_str_constant(self, formula, args, **kwargs):
        return self.cvc5.mkString(formula.constant_value())

    def walk_str_length (self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_LENGTH , args[0])

    def walk_str_concat(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_CONCAT, *args)

    def walk_str_contains(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_CONTAINS, args[0], args[1])

    def walk_str_indexof(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_INDEXOF, args[0], args[1], args[2])

    def walk_str_replace(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_REPLACE, args[0], args[1], args[2])

    def walk_str_substr(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_SUBSTR, args[0], args[1], args[2])

    def walk_str_prefixof(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_PREFIX, args[0], args[1])

    def walk_str_suffixof(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_SUFFIX, args[0], args[1])

    def walk_str_to_int(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_TO_INT, args[0])

    def walk_int_to_str(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_FROM_INT, args[0])

    def walk_str_charat(self, formula, args, **kwargs):
        return self.cvc5.mkTerm(Kind.STRING_CHARAT, args[0], args[1])

    def _type_to_cvc5(self, tp):
        if tp.is_bool_type():
            return self.cvc5.getBooleanSort()
        elif tp.is_real_type():
            return self.cvc5.getRealSort()
        elif tp.is_int_type():
            return self.cvc5.getIntegerSort()
        elif tp.is_function_type():
            stps = [self._type_to_cvc5(x) for x in tp.param_types]
            rtp = self._type_to_cvc5(tp.return_type)
            return self.cvc5.mkFunctionSort(stps, rtp)
        elif tp.is_array_type():
            # Recursively convert the types of index and elem
            idx_cvc_type = self._type_to_cvc5(tp.index_type)
            elem_cvc_type = self._type_to_cvc5(tp.elem_type)
            return self.cvc5.mkArraySort(idx_cvc_type, elem_cvc_type)
        elif tp.is_bv_type():
            return self.cvc5.mkBitVectorSort(tp.width)
        elif tp.is_string_type():
            return self.cvc5.getStringSort()
        elif tp.is_custom_type():
            return self.cvc5.mkUninterpretedSort(str(tp))
        else:
            raise NotImplementedError("Unsupported type: %s" %tp)

    def _cvc5_type_to_type(self, type_):
        if type_.isBoolean():
            return types.BOOL
        elif type_.isInteger():
            return types.INT
        elif type_.isReal():
            return types.REAL
        elif type_.isArray():
            # Recursively convert the types of index and elem
            idx_type = self._cvc5_type_to_type(type_.getArrayIndexSort())
            elem_type = self._cvc5_type_to_type(type_.getArrayElementSort())
            return types.ArrayType(idx_type, elem_type)
        elif type_.isBitVector():
            return types.BVType(type_.getBitVectorSize())
        elif type_.isFunction():
            # Casting Type into FunctionType
            type_ = cvc5.FunctionType(type_)
            return_type = type_.getRangeType()
            param_types = tuple(self._cvc5_type_to_type(ty) for ty in type_.getArgTypes())
            return types.FunctionType(return_type, param_types)
        else:
            raise NotImplementedError("Unsupported type: %s" % type_)

    def _rename_bound_variables(self, formula, variables):
        """Bounds the variables in formula.

        Returns a tuple (new_formula, new_var_list) in which the old
        variables have been replaced by the new variables in the list.
        """
        mkBoundVar = self.cvc5.mkVar
        new_var_list = [mkBoundVar(self._type_to_cvc5(x.symbol_type()),
                                   x.symbol_name())
                        for x in variables]
        old_var_list = [self.walk_symbol(x, []) for x in variables]
        new_formula = formula.substitute(old_var_list, new_var_list)
        return (new_formula, new_var_list)
