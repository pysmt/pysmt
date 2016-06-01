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
import warnings
from fractions import Fraction
from six.moves import xrange

from pysmt.exceptions import SolverAPINotFound
from pysmt.shortcuts import String

try:
    import CVC4
except ImportError:
    raise SolverAPINotFound

from pysmt.logics import PYSMT_QF_LOGICS, QF_SLIA
from pysmt.solvers.solver import Solver, Converter
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.walkers import DagWalker
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.eager import EagerModel
from pysmt.decorators import catch_conversion_error


class CVC4Solver(Solver, SmtLibBasicSolver, SmtLibIgnoreMixin):
    LOGICS = PYSMT_QF_LOGICS | frozenset([QF_SLIA])

    def __init__(self, environment, logic, **options):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        **options)
        self.em = CVC4.ExprManager()

        self.cvc4 = None
        self.declarations = None
        self.logic_name = str(logic)
        if self.logic_name == "QF_BOOL":
            self.logic_name = "QF_LRA"

        self.reset_assertions()
        self.converter = CVC4Converter(environment, cvc4_exprMgr=self.em)
        return

    def reset_assertions(self):
        del self.cvc4
        self.cvc4 = CVC4.SmtEngine(self.em)
        if( self.logic_name == "QF_SLIA"):
            self.set_option("strings-exp", "true")
        self.set_option("produce-models", "false")
        self.set_option("incremental", "false")
        if self.options.generate_models:
            self.set_option("produce-models", "true")
        if self.options.incremental:
            self.set_option("incremental", "true")
        self.declarations = set()
        self.cvc4.setLogic(self.logic_name)

    def declare_variable(self, var):
        self.converter.declare_variable(var)
        return

    def add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        self.cvc4.assertFormula(term)
        return

    def get_model(self):
        assignment = {}
        for s in self.environment.formula_manager.get_all_symbols():
            if s.is_term():
                v = self.get_value(s)
                assignment[s] = v
        return EagerModel(assignment=assignment, environment=self.environment)

    def solve(self, assumptions=None):
        if assumptions is not None:
            conj_assumptions = self.environment.formula_manager.And(assumptions)
            cvc4_assumption = self.converter.convert(conj_assumptions)
            res = self.cvc4.checkSat(cvc4_assumption)
        else:
            res = self.cvc4.checkSat()

        # Convert returned type
        res_type = res.isSat()
        if res_type == CVC4.Result.SAT_UNKNOWN:
            raise SolverReturnedUnknownResultError()
        else:
            return res_type == CVC4.Result.SAT
        return

    def push(self, levels=1):
        if not self.options.incremental:
            # The exceptions from CVC4 are not raised correctly
            # (probably due to the wrapper)
            # Therefore, we need to check that we can actually do a push
            raise NotImplementedError("The solver is not incremental")

        for _ in xrange(levels):
            self.cvc4.push()
        return

    def pop(self, levels=1):
        for _ in xrange(levels):
            self.cvc4.pop()
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
        cvc4_res = self.cvc4.getValue(term)
        res = self.converter.back(cvc4_res)
        if self.environment.stc.get_type(item).is_real_type() and \
           self.environment.stc.get_type(res).is_int_type():
            res = self.environment.formula_manager.Real(Fraction(res.constant_value(), 1))
        return res

    def _exit(self):
        del self.cvc4
    
    def set_option(self, name, value):
        """Sets an option.

        :param name and value: Option to be set
        :type name: String
        :type value: String
        """
        self.cvc4.setOption(name, CVC4.SExpr(value))
        


class CVC4Converter(Converter, DagWalker):

    def __init__(self, environment, cvc4_exprMgr):
        DagWalker.__init__(self, environment)

        self.cvc4_exprMgr = cvc4_exprMgr
        self.mkExpr = cvc4_exprMgr.mkExpr
        self.mkConst = cvc4_exprMgr.mkConst
        self.mkVar = cvc4_exprMgr.mkVar
        self.realType = cvc4_exprMgr.realType()
        self.intType = cvc4_exprMgr.integerType()
        self.boolType = cvc4_exprMgr.booleanType()
        self.stringType = cvc4_exprMgr.stringType()

        self.declared_vars = {}
        self.backconversion = {}
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type
        return

    def declare_variable(self, var):
        if not var.is_symbol():
            raise TypeError
        if var.symbol_name() not in self.declared_vars:
            cvc4_type = self._type_to_cvc4(var.symbol_type())
            decl = self.mkVar(var.symbol_name(), cvc4_type)
            self.declared_vars[var] = decl

    def back(self, expr):
        res = None
        if expr.isConst():
            if expr.getType().isBoolean():
                v = expr.getConstBoolean()
                res = self.mgr.Bool(v)
            elif expr.getType().isInteger():
                v = expr.getConstRational().toString()
                res = self.mgr.Int(int(v))
            elif expr.getType().isReal():
                v = expr.getConstRational().toString()
                res = self.mgr.Real(Fraction(v))
            elif expr.getType().isBitVector():
                bv = expr.getConstBitVector()
                v = bv.getValue().toString()
                width = bv.getSize()
                res = self.mgr.BV(int(v), width)
            elif expr.getType().isString():
                v = expr.getConstString()
                res = self.mgr.String(v.toString())
            else:
                raise TypeError("Unsupported constant type:", expr.getType())
        else:
            raise TypeError("Unsupported expression:", expr.toString())

        return res

    @catch_conversion_error
    def convert(self, formula):
        return self.walk(formula)

    def walk_and(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.AND, args)

    def walk_or(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.OR, args)

    def walk_not(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.NOT, args[0])

    def walk_symbol(self, formula, **kwargs):
        if formula not in self.declared_vars:
            self.declare_variable(formula)
        return self.declared_vars[formula]

    def walk_iff(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.IFF, args[0], args[1])

    def walk_implies(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.IMPLIES, args[0], args[1])

    def walk_le(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.LEQ, args[0], args[1])

    def walk_lt(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.LT, args[0], args[1])

    def walk_ite(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.ITE, args[0], args[1], args[2])

    def walk_real_constant(self, formula, **kwargs):
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        return self.mkConst(CVC4.Rational(n, d))

    def walk_int_constant(self, formula, **kwargs):
        assert type(formula.constant_value()) == int
        return self.mkConst(CVC4.Rational(formula.constant_value()))

    def walk_bool_constant(self, formula, **kwargs):
        return self.cvc4_exprMgr.mkBoolConst(formula.constant_value())

    def walk_exists(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        bound_vars_list = self.mkExpr(CVC4.BOUND_VAR_LIST, var_list)
        return self.mkExpr(CVC4.EXISTS,
                           bound_vars_list,
                           bound_formula)

    def walk_forall(self, formula, args, **kwargs):
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        bound_vars_list = self.mkExpr(CVC4.BOUND_VAR_LIST, var_list)
        return self.mkExpr(CVC4.FORALL,
                           bound_vars_list,
                           bound_formula)

    def walk_plus(self, formula, args, **kwargs):
        res = self.mkExpr(CVC4.PLUS, args)
        return res

    def walk_minus(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.MINUS, args[0], args[1])

    def walk_equals(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.EQUAL, args[0], args[1])

    def walk_times(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.MULT, args[0], args[1])

    def walk_toreal(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.TO_REAL, args[0])

    def walk_function(self, formula, args, **kwargs):
        name = formula.function_name()
        if name not in self.declared_vars:
            self.declare_variable(name)
        decl = self.declared_vars[name]
        return self.mkExpr(CVC4.APPLY_UF, decl, *args)

    def walk_bv_constant(self, formula, **kwargs):
        value = formula.constant_value()
        width = formula.bv_width()
        return self.mkConst(CVC4.BitVector(width, value))

    def walk_bv_ult(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_ULT, args[0], args[1])

    def walk_bv_ule(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_ULE, args[0], args[1])

    def walk_bv_concat(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_CONCAT, args[0], args[1])

    def walk_bv_extract(self, formula, args, **kwargs):
        ext = self.mkConst(CVC4.BitVectorExtract(formula.bv_extract_end(),
                                                 formula.bv_extract_start()))
        return self.mkExpr(CVC4.BITVECTOR_EXTRACT, ext, args[0])

    def walk_bv_or(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_OR, args[0], args[1])

    def walk_bv_not(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_NOT, args[0])

    def walk_bv_and(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_AND, args[0], args[1])

    def walk_bv_xor(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_XOR, args[0], args[1])

    def walk_bv_add(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_PLUS, args[0], args[1])

    def walk_bv_sub(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_SUB, args[0], args[1])

    def walk_bv_neg(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_NEG, args[0])

    def walk_bv_mul(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_MULT, args[0], args[1])

    def walk_bv_udiv(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_UDIV, args[0], args[1])

    def walk_bv_urem(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_UREM, args[0], args[1])

    def walk_bv_lshl(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_SHL, args[0], args[1])

    def walk_bv_lshr(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_LSHR, args[0], args[1])

    def walk_bv_rol(self, formula, args, **kwargs):
        ext = self.mkConst(CVC4.BitVectorRotateLeft(formula.bv_rotation_step()))
        return self.mkExpr(CVC4.BITVECTOR_ROTATE_LEFT, ext, args[0])

    def walk_bv_ror(self, formula, args, **kwargs):
        ext = self.mkConst(CVC4.BitVectorRotateRight(formula.bv_rotation_step()))
        return self.mkExpr(CVC4.BITVECTOR_ROTATE_RIGHT, ext, args[0])

    def walk_bv_zext(self, formula, args, **kwargs):
        ext = self.mkConst(CVC4.BitVectorZeroExtend(formula.bv_extend_step()))
        return self.mkExpr(CVC4.BITVECTOR_ZERO_EXTEND, ext, args[0])

    def walk_bv_sext (self, formula, args, **kwargs):
        ext = self.mkConst(CVC4.BitVectorSignExtend(formula.bv_extend_step()))
        return self.mkExpr(CVC4.BITVECTOR_SIGN_EXTEND, ext, args[0])

    def walk_bv_slt(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_SLT, args[0], args[1])

    def walk_bv_sle (self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_SLE, args[0], args[1])

    def walk_bv_comp (self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_COMP, args[0], args[1])

    def walk_bv_sdiv (self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_SDIV, args[0], args[1])

    def walk_bv_srem (self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_SREM, args[0], args[1])

    def walk_bv_ashr (self, formula, args, **kwargs):
        return self.mkExpr(CVC4.BITVECTOR_ASHR, args[0], args[1])

    def walk_string_constant(self, formula, args, **kwargs):
        #assert type(formula.constant_value()) == str
        return self.mkConst(CVC4.CVC4String(formula.constant_value()))
    
    def walk_str_length (self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_LENGTH , args[0])
    def walk_str_concat(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_CONCAT, args)
    def walk_str_contains(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_STRCTN, args[0], args[1])
    def walk_str_indexof(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_STRIDOF, args[0], args[1], args[2])
    def walk_str_replace(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_STRREPL, args[0], args[1], args[2])
    def walk_str_substr(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_SUBSTR, args[0], args[1], args[2])
    def walk_str_prefixof(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_PREFIX, args[0], args[1])
    def walk_str_suffixof(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_SUFFIX, args[0], args[1])
    def walk_str_to_int(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_STOI, args[0])
    def walk_int_to_str(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_ITOS, args[0])
    def walk_str_to_unit16(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_STOU16, args[0])
    def walk_uint16_to_str(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_U16TOS, args[0])
    def walk_str_to_uint32(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_STOU32, args[0])
    def walk_uint32_to_str(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_U32TOS, args[0])
    def walk_str_charat(self, formula, args, **kwargs):
        return self.mkExpr(CVC4.STRING_CHARAT, args[0], args[1])
    
    def _type_to_cvc4(self, tp):
        if tp.is_bool_type():
            return self.boolType
        elif tp.is_real_type():
            return self.realType
        elif tp.is_int_type():
            return self.intType
        elif tp.is_function_type():
            stps = [self._type_to_cvc4(x) for x in tp.param_types]
            rtp = self._type_to_cvc4(tp.return_type)
            return self.cvc4_exprMgr.mkFunctionType(stps, rtp)
        elif tp.is_bv_type():
            return self.cvc4_exprMgr.mkBitVectorType(tp.width)
        elif tp.is_string_type():
            return self.stringType
        else:
            raise NotImplementedError("Unsupported type: %s" %tp)

    def _rename_bound_variables(self, formula, variables):
        """Bounds the variables in formula.

        Returns a tuple (new_formula, new_var_list) in which the old
        variables have been replaced by the new variables in the list.
        """
        mkBoundVar = self.cvc4_exprMgr.mkBoundVar
        new_var_list = [mkBoundVar(x.symbol_name(),
                                   self._type_to_cvc4(x.symbol_type())) \
                        for x in variables]
        old_var_list = [self.walk_symbol(x) for x in variables]
        new_formula = formula.substitute(old_var_list, new_var_list)
        return (new_formula, new_var_list)
