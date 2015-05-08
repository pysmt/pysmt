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

import z3

from fractions import Fraction
from six.moves import xrange

from pysmt import typing as types
from pysmt.solvers.solver import (IncrementalTrackingSolver, UnsatCoreSolver,
                                  Model, Converter)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.qelim import QuantifierEliminator
from pysmt.solvers.interpolation import Interpolator

from pysmt.walkers import DagWalker
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              SolverNotConfiguredForUnsatCoresError,
                              SolverStatusError,
                              InternalSolverError,
                              ConvertExpressionError)
from pysmt.decorators import clear_pending_pop

from pysmt.logics import LRA, LIA, QF_UFLIA, QF_UFLRA, PYSMT_LOGICS, BV_LOGICS
from pysmt.oracles import get_logic


# patch z3api
z3.is_ite = lambda x: z3.is_app_of(x, z3.Z3_OP_ITE)

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
                pysmt_d = self.converter.back(d())
                yield pysmt_d, self.get_value(pysmt_d)

    def __contains__(self, x):
        """Returns whether the model contains a value for 'x'."""
        return x in (v for v, _ in self)



class Z3Solver(IncrementalTrackingSolver, UnsatCoreSolver,
               SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = PYSMT_LOGICS - BV_LOGICS

    def __init__(self, environment, logic, user_options):
        IncrementalTrackingSolver.__init__(self,
                                           environment=environment,
                                           logic=logic,
                                           user_options=user_options)
        # Here we could use:
        # self.z3 = z3.SolverFor(str(logic))
        # But it seems to have problems with quantified formulae
        self.z3 = z3.Solver()

        if self.options.unsat_cores_mode != None:
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
            return {t[0] : (t[1],t[2]) for t in self.assertions}
        return None

    def get_named_unsat_core(self):
        """After a call to solve() yielding UNSAT, returns the unsat core as a
        dict of names to formulae"""
        if self.options.unsat_cores_mode is None:
            raise SolverNotConfiguredForUnsatCoresError

        if self.last_result != False:
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

    def exit(self):
        if not self._destroyed:
            self._destroyed = True
            del self.z3



class Z3Converter(Converter, DagWalker):

    def __init__(self, environment):
        DagWalker.__init__(self, environment)
        self.backconversion = {}
        self.mgr = environment.formula_manager
        self._get_type = environment.stc.get_type

        return

    def convert(self, formula):
        return self.walk(formula)

    def back(self, expr):
        assert z3.is_expr(expr)

        if askey(expr) in self.backconversion:
            return self.backconversion[askey(expr)]

        if z3.is_quantifier(expr):
            raise NotImplementedError(
                "Quantified back conversion is currently not supported")

        args = [self.back(x) for x in expr.children()]

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
            if self._get_type(args[0]) == types.BOOL:
                res = self.mgr.Iff(args[0], args[1])
            else:
                res = self.mgr.Equals(args[0], args[1])

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

        elif z3.is_sub(expr):
            res = self.mgr.Minus(args[0], args[1])

        elif z3.is_not(expr):
            res = self.mgr.Not(args[0])

        elif z3.is_quantifier(expr):
            if expr.is_forall():
                pass
            else:
                pass
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
            else:
                # it must be a symbol
                res = self.mgr.get_symbol(str(expr))


        elif z3.is_ite(expr):
            res = self.mgr.Ite(args[0], args[1], args[2])


        if res is None:
            raise ConvertExpressionError(message=("Unsupported expression: %s" %
                                                   str(expr)),
                                          expression=expr)

        self.backconversion[askey(expr)] = res

        return res


    def walk_and(self, formula, args):
        return z3.And(*args)

    def walk_or(self, formula, args):
        return z3.Or(*args)

    def walk_not(self, formula, args):
        return z3.Not(args[0])

    def walk_symbol(self, formula, args):
        symbol_type = formula.symbol_type()
        if symbol_type == types.BOOL:
            res = z3.Bool(formula.symbol_name())
        elif symbol_type == types.REAL:
            res = z3.Real(formula.symbol_name())
        elif symbol_type == types.INT:
            res = z3.Int(formula.symbol_name())
        else:
            assert False
        return res

    def walk_iff(self, formula, args):
        return (args[0] == args[1])

    def walk_implies(self, formula, args):
        return z3.Implies(*args)

    def walk_le(self, formula, args):
        return (args[0] <= args[1])

    def walk_lt(self, formula, args):
        return (args[0] < args[1])

    def walk_ite(self, formula, args):
        i = args[0]
        t = args[1]
        e = args[2]

        if self._get_type(formula) == types.BOOL:
            return z3.And(z3.Implies(i, t), z3.Implies(z3.Not(i), e))
        else:
            return z3.If(i, t, e)

    def walk_real_constant(self, formula, args):
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        return z3.RealVal(rep)

    def walk_int_constant(self, formula, args):
        assert type(formula.constant_value()) == int or \
            type(formula.constant_value()) == long
        return z3.IntVal(formula.constant_value())

    def walk_bool_constant(self, formula, args):
        return z3.BoolVal(formula.constant_value())

    def walk_exists(self, formula, args):
        return z3.Exists([self.walk_symbol(x, [])
                          for x in formula.quantifier_vars()],
                         args[0])

    def walk_forall(self, formula, args):
        return z3.ForAll([self.walk_symbol(x, [])
                          for x in formula.quantifier_vars()],
                         args[0])

    def walk_plus(self, formula, args):
        return z3.Sum(*args)

    def walk_minus(self, formula, args):
        return (args[0] - args[1])

    def walk_equals(self, formula, args):
        return (args[0] == args[1])

    def walk_times(self, formula, args):
        return (args[0] * args[1])

    def walk_toreal(self, formula, args):
        return z3.ToReal(args[0])

    def walk_function(self, formula, args):
        f = formula.function_name()
        tp = f.symbol_type()
        sig = [self._type_to_z3(x) for x in tp.param_types]
        sig.append(self._type_to_z3(tp.return_type))
        z3_f = z3.Function(f.symbol_name(), *sig)
        return z3_f(*args)

    def _type_to_z3(self, tp):
        if tp == types.BOOL:
            return z3.BoolSort()
        elif tp == types.REAL:
            return z3.RealSort()
        elif tp == types.INT:
            return z3.IntSort()
        else:
            raise NotImplementedError



class Z3QuantifierEliminator(QuantifierEliminator):

    LOGICS = [LIA, LRA]

    def __init__(self, environment, logic=None):
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


class Z3Interpolator(Interpolator):

    LOGICS = [QF_UFLIA, QF_UFLRA]

    def __init__(self, environment, logic=None):
        self.environment = environment
        self.logic = logic
        self.converter = Z3Converter(environment)


    def _check_logic(self, formulas):
        for f in formulas:
            logic = get_logic(f, self.environment)
            ok = any(logic <= l for l in self.LOGICS)
            if not ok:
                raise NotImplementedError(
                    "Logic not supported by Z3 inteprolation."
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
