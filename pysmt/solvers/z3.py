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

from pysmt import typing as types
from pysmt.solvers.solver import Solver, Model
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.qelim import QuantifierEliminator

from pysmt.walkers import DagWalker
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.decorators import clear_pending_pop

import pysmt.logics

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

    def get_value(self, formula):
        titem = self.converter.convert(formula)
        z3_res = self.z3_model.eval(titem, model_completion=True)
        return self.converter.back(z3_res)


class Z3Solver(Solver, SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = pysmt.logics.PYSMT_LOGICS

    def __init__(self, environment, logic, options=None):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        options=options)
        # Here we could use:
        # self.z3 = z3.SolverFor(str(logic))
        # But it seems to have problems with quantified formulae
        self.z3 = z3.Solver()

        self.declarations = set()
        self.converter = Z3Converter(environment)
        self.mgr = environment.formula_manager
        return

    @clear_pending_pop
    def reset_assertions(self):
        self.z3.reset()
        return


    @clear_pending_pop
    def declare_variable(self, var):
        self.declarations.add(var)
        return

    @clear_pending_pop
    def add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)
        self.z3.add(term)
        return

    def get_model(self):
        return Z3Model(self.environment, self.z3.model())

    @clear_pending_pop
    def solve(self, assumptions=None):
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
            raise SolverReturnedUnknownResultError()

        return sres == 'sat'

    @clear_pending_pop
    def all_sat(self, important, callback):
        raise NotImplementedError

    @clear_pending_pop
    def push(self, levels=1):
        for _ in xrange(levels):
            self.z3.push()

    @clear_pending_pop
    def pop(self, levels=1):
        for _ in xrange(levels):
            self.z3.pop()

    def print_model(self, name_filter=None):
        for var in self.declarations:
            if name_filter is None or not var.symbol_name().startswith(name_filter):
                print var.symbol_name(), "=", self.get_value(var)


    def get_value(self, item):
        self._assert_no_function_type(item)

        titem = self.converter.convert(item)
        res = self.z3.model().eval(titem, model_completion=True)
        r = self.converter.back(res)
        return r

    def exit(self):
        del self.z3
        self.z3 = None
        return


class Z3Converter(DagWalker):

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
            assert len(args) == 2
            res = self.mgr.Div(args[0], args[1])

        elif z3.is_eq(expr):
            assert len(args) == 2
            res = self.mgr.Equals(args[0], args[1])

        elif z3.is_false(expr):
            assert len(args) == 0
            res = self.mgr.FALSE()

        elif z3.is_true(expr):
            assert len(args) == 0
            res = self.mgr.TRUE()

        elif z3.is_gt(expr):
            assert len(args) == 2
            res = self.mgr.GT(args[0], args[1])

        elif z3.is_ge(expr):
            assert len(args) == 2
            res = self.mgr.GE(args[0], args[1])

        elif z3.is_lt(expr):
            assert len(args) == 2
            res = self.mgr.LT(args[0], args[1])

        elif z3.is_le(expr):
            assert len(args) == 2
            res = self.mgr.LE(args[0], args[1])

        elif z3.is_mul(expr):
            assert len(args) == 2
            res = self.mgr.Times(args[0], args[1])

        elif z3.is_sub(expr):
            assert len(args) == 2
            res = self.mgr.Minus(args[0], args[1])

        elif z3.is_not(expr):
            assert len(args) == 1
            res = self.mgr.Not(args[0])

        elif z3.is_quantifier(expr):
            assert len(args) == 2
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
            assert len(args) == 3
            res = self.mgr.Ite(args[0], args[1], args[2])

        else:
            raise TypeError("Unsupported expression:", expr)

        if res is None:
            raise TypeError("Unsupported expression:", expr)

        self.backconversion[askey(expr)] = res

        return res


    def walk_and(self, formula, args):
        return z3.And(*args)

    def walk_or(self, formula, args):
        return z3.Or(*args)

    def walk_not(self, formula, args):
        assert len(args) == 1
        return z3.Not(args[0])

    def walk_symbol(self, formula, args):
        assert len(args) == 0
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
        assert len(args) == 2
        return z3.And(z3.Implies(args[0], args[1]),
                      z3.Implies(args[1], args[0]))

    def walk_implies(self, formula, args):
        assert len(args) == 2
        return z3.Implies(*args)

    def walk_le(self, formula, args):
        assert len(args) == 2
        return (args[0] <= args[1])

    def walk_lt(self, formula, args):
        assert len(args) == 2
        return (args[0] < args[1])

    def walk_ite(self, formula, args):
        assert len(args) == 3
        i = args[0]
        t = args[1]
        e = args[2]

        if self._get_type(formula) == types.BOOL:
            return z3.And(z3.Implies(i, t), z3.Implies(z3.Not(i), e))
        else:
            return z3.If(i, t, e)

    def walk_real_constant(self, formula, args):
        assert len(args) == 0
        assert type(formula.constant_value()) == Fraction
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        return z3.RealVal(rep)

    def walk_int_constant(self, formula, args):
        assert len(args) == 0
        assert type(formula.constant_value()) == int or \
            type(formula.constant_value()) == long
        return z3.IntVal(formula.constant_value())

    def walk_bool_constant(self, formula, args):
        assert len(args) == 0
        return z3.BoolVal(formula.constant_value())

    def walk_exists(self, formula, args):
        assert len(args) == 1
        return z3.Exists([self.walk_symbol(x, [])
                          for x in formula.quantifier_vars()],
                         args[0])

    def walk_forall(self, formula, args):
        assert len(args) == 1
        return z3.ForAll([self.walk_symbol(x, [])
                          for x in formula.quantifier_vars()],
                         args[0])

    def walk_plus(self, formula, args):
        assert len(args) >= 2
        return z3.Sum(*args)

    def walk_minus(self, formula, args):
        assert len(args) == 2
        return (args[0] - args[1])

    def walk_equals(self, formula, args):
        assert len(args) == 2
        return (args[0] == args[1])

    def walk_times(self, formula, args):
        assert len(args) == 2
        return (args[0] * args[1])

    def walk_toreal(self, formula, args):
        assert len(args) == 1
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

    def __init__(self, environment):
        self.environment = environment
        self.converter = Z3Converter(environment)


    def eliminate_quantifiers(self, formula):
        simplifier = z3.Tactic('simplify')
        eliminator = z3.Tactic('qe')

        f = self.converter.convert(formula)

        s = simplifier(f, elim_and=True,
                       pull_cheap_ite=True,
                       ite_extra_rules=True).as_expr()
        res = eliminator(s, eliminate_variables_as_block=True).as_expr()
        return self.converter.back(res)
