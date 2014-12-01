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
from fractions import Fraction

import CVC4

import pysmt
from pysmt.solvers.solver import Solver
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.walkers import DagWalker
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.eager import EagerModel

class CVC4Solver(Solver, SmtLibBasicSolver, SmtLibIgnoreMixin):
    LOGICS = pysmt.logics.PYSMT_LOGICS

    def __init__(self, environment, logic, options=None):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        options=options)
        self.em = CVC4.ExprManager()
        self.cvc4 = CVC4.SmtEngine(self.em)
        self.cvc4.setOption("produce-models", CVC4.SExpr("true"))

        self.cvc4.setLogic(str(logic))
        self.converter = CVC4Converter(environment, cvc4_exprMgr=self.em)
        self.declarations = set()
        return

    def reset_assertions(self):
        #TODO: Shall we just discard the current SmtEngine or is there a
        # lightweight way to proceed?
        raise NotImplementedError

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
        for _ in xrange(levels):
            self.cvc4.push()
        return

    def pop(self, levels=1):
        for _ in xrange(levels):
            self.cvc4.pop()
        return

    def print_model(self, name_filter=None):
        if name_filter == None:
            var_set = self.declarations
        else:
            var_set = (var for var in self.declarations\
                       if name_filter(var))

        for var in var_set:
            print(var.symbol_name(), "=", self.get_value(var))

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

    def exit(self):
        del self.cvc4
        self.cvc4 = None
        return


class CVC4Converter(DagWalker):

    def __init__(self, environment, cvc4_exprMgr):
        DagWalker.__init__(self, environment)

        self.cvc4_exprMgr = cvc4_exprMgr
        self.mkExpr = cvc4_exprMgr.mkExpr
        self.mkConst = cvc4_exprMgr.mkConst
        self.mkVar = cvc4_exprMgr.mkVar
        self.realType = cvc4_exprMgr.realType()
        self.intType = cvc4_exprMgr.integerType()
        self.boolType = cvc4_exprMgr.booleanType()

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
                res = self.env.formula_manager.Bool(v)
            elif expr.getType().isInteger():
                v = expr.getConstRational().toString()
                res = self.env.formula_manager.Int(int(v))
            elif expr.getType().isReal():
                v = expr.getConstRational().toString()
                res = self.env.formula_manager.Real(Fraction(v))

            else:
                raise TypeError("Unsupported constant type:", expr.getType())
        else:
            raise TypeError("Unsupported expression:", expr.toString())

        return res



    def convert(self, formula):
        return self.walk(formula)

    def walk_and(self, formula, args):
        assert len(args) >= 2
        return self.mkExpr(CVC4.AND, args)

    def walk_or(self, formula, args):
        assert len(args) >= 2
        return self.mkExpr(CVC4.OR, args)

    def walk_not(self, formula, args):
        assert len(args) == 1
        return self.mkExpr(CVC4.NOT, args[0])

    def walk_symbol(self, formula, args):
        assert len(args) == 0
        if formula not in self.declared_vars:
            self.declare_variable(formula)
        return self.declared_vars[formula]

    def walk_iff(self, formula, args):
        assert len(args) == 2
        return self.mkExpr(CVC4.IFF, args[0], args[1])

    def walk_implies(self, formula, args):
        assert len(args) == 2
        return self.mkExpr(CVC4.IMPLIES, args[0], args[1])

    def walk_le(self, formula, args):
        assert len(args) == 2
        return self.mkExpr(CVC4.LEQ, args[0], args[1])

    def walk_lt(self, formula, args):
        assert len(args) == 2
        return self.mkExpr(CVC4.LT, args[0], args[1])

    def walk_ite(self, formula, args):
        assert len(args) == 3
        return self.mkExpr(CVC4.ITE, *args)

    def walk_real_constant(self, formula, args):
        assert len(args) == 0
        assert type(formula.constant_value()) == Fraction
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        return self.mkConst(CVC4.Rational(n, d))

    def walk_int_constant(self, formula, args):
        assert len(args) == 0
        assert type(formula.constant_value()) == int
        return self.mkConst(CVC4.Rational(formula.constant_value()))

    def walk_bool_constant(self, formula, args):
        assert len(args) == 0
        assert type(formula.constant_value()) == bool
        return self.cvc4_exprMgr.mkBoolConst(formula.constant_value())

    def walk_exists(self, formula, args):
        assert len(args) == 1
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        bound_vars_list = self.mkExpr(CVC4.BOUND_VAR_LIST, var_list)
        return self.mkExpr(CVC4.EXISTS,
                           bound_vars_list,
                           bound_formula)

    def walk_forall(self, formula, args):
        assert len(args) == 1
        (bound_formula, var_list) = \
                 self._rename_bound_variables(args[0], formula.quantifier_vars())
        bound_vars_list = self.mkExpr(CVC4.BOUND_VAR_LIST, var_list)
        return self.mkExpr(CVC4.FORALL,
                           bound_vars_list,
                           bound_formula)

    def walk_plus(self, formula, args):
        assert len(args) >= 2
        res = self.mkExpr(CVC4.PLUS, args)
        return res

    def walk_minus(self, formula, args):
        assert len(args) == 2
        return self.mkExpr(CVC4.MINUS, args[0], args[1])

    def walk_equals(self, formula, args):
        assert len(args) == 2
        return self.mkExpr(CVC4.EQUAL, args[0], args[1])

    def walk_times(self, formula, args):
        assert len(args) == 2
        return self.mkExpr(CVC4.MULT, args[0], args[1])

    def walk_toreal(self, formula, args):
        assert len(args) == 1
        return self.mkExpr(CVC4.TO_REAL, args[0])

    def walk_function(self, formula, args):
        name = formula.function_name()
        if name not in self.declared_vars:
            self.declare_variable(name)
        decl = self.declared_vars[name]
        return self.mkExpr(CVC4.APPLY_UF, decl, *args)

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
        else:
            raise NotImplementedError

    def _rename_bound_variables(self, formula, variables):
        """Bounds the variables in formula.

        Returns a tuple (new_formula, new_var_list) in which the old
        variables have been replaced by the new variables in the list.
        """
        mkBoundVar = self.cvc4_exprMgr.mkBoundVar
        new_var_list = [mkBoundVar(x.symbol_name(),
                                   self._type_to_cvc4(x.symbol_type())) \
                        for x in variables]
        old_var_list = [self.walk_symbol(x, []) for x in variables]
        new_formula = formula.substitute(old_var_list, new_var_list)
        return (new_formula, new_var_list)
