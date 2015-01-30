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
import re
from fractions import Fraction

import mathsat

import pysmt.logics
from pysmt import typing as types
from pysmt.solvers.solver import Solver
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.solvers.eager import EagerModel
from pysmt.walkers import DagWalker
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.exceptions import InternalSolverError
from pysmt.decorators import clear_pending_pop
from pysmt.environment import TypeUnsafeEnvironment
from pysmt.utils.generic_number import GenericNumber, disambiguate


class MathSAT5Solver(Solver, SmtLibBasicSolver, SmtLibIgnoreMixin):

    LOGICS = pysmt.logics.PYSMT_QF_LOGICS

    def __init__(self, environment, logic, options=None, debugFile=None):
        Solver.__init__(self,
                        environment=environment,
                        logic=logic,
                        options=options)

        self.config = mathsat.msat_create_default_config(str(logic))
        check = mathsat.msat_set_option(self.config, "model_generation", "true")
        assert check == 0

        if debugFile is not None:
            mathsat.msat_set_option(self.config, "debug.api_call_trace", "1")
            mathsat.msat_set_option(self.config, "debug.api_call_trace_filename",
                                    debugFile)

        self.msat_env = mathsat.msat_create_env(self.config)

        self.realType = mathsat.msat_get_rational_type(self.msat_env)
        self.intType = mathsat.msat_get_integer_type(self.msat_env)
        self.boolType = mathsat.msat_get_bool_type(self.msat_env)

        self.mgr = environment.formula_manager
        self.converter = MSatConverter(environment, self.msat_env)
        return

    @clear_pending_pop
    def reset_assertions(self):
        mathsat.msat_reset_env(self.msat_env)
        return

    @clear_pending_pop
    def declare_variable(self, var):
        self.converter.declare_variable(var)

    @clear_pending_pop
    def add_assertion(self, formula, named=None):
        self._assert_is_boolean(formula)
        term = self.converter.convert(formula)

        res = mathsat.msat_assert_formula(self.msat_env, term)

        if res != 0:
            msat_msg = mathsat.msat_last_error_message(self.msat_env)
            raise InternalSolverError(msat_msg)
        return


    @clear_pending_pop
    def solve(self, assumptions=None):
        res = None
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
                res = mathsat.msat_solve_with_assumptions(self.msat_env, bool_ass)
            else:
                res = mathsat.msat_solve(self.msat_env)

        else:
            res = mathsat.msat_solve(self.msat_env)

        assert res in [mathsat.MSAT_UNKNOWN,mathsat.MSAT_SAT,mathsat.MSAT_UNSAT]
        if res == mathsat.MSAT_UNKNOWN:
            raise SolverReturnedUnknownResultError()
        return res == mathsat.MSAT_SAT

    @clear_pending_pop
    def all_sat(self, important, callback):
        self.push()
        mathsat.msat_all_sat(self.msat_env,
                             [self._var2term(x) for x in important],
                             callback)
        self.pop()

    @clear_pending_pop
    def push(self, levels=1):
        for _ in xrange(levels):
            mathsat.msat_push_backtrack_point(self.msat_env)
        return

    @clear_pending_pop
    def pop(self, levels=1):
        for _ in xrange(levels):
            mathsat.msat_pop_backtrack_point(self.msat_env)
        return

    def _var2term(self, var):
        decl = mathsat.msat_find_decl(self.msat_env, var.symbol_name())
        titem = mathsat.msat_make_term(self.msat_env, decl, [])
        return titem


    def set_preferred_var(self, var):
        tvar = self.converter.convert(var)
        mathsat.msat_add_preferred_for_branching(self.msat_env, tvar)
        return


    def print_model(self, name_filter=None):
        if name_filter is not None:
            raise NotImplementedError
        for v in self.converter.symbol_to_decl.keys():
            var = self.mgr.Symbol(v)
            assert var is not None
            print v, "=", self.get_value(var)

    def get_value(self, item):
        self._assert_no_function_type(item)

        titem = self.converter.convert(item)
        tval = mathsat.msat_get_model_value(self.msat_env, titem)

        if mathsat.msat_term_is_number(self.msat_env, tval):
            rep = mathsat.msat_term_repr(tval)
            if self.environment.stc.get_type(item).is_real_type():
                match = re.match(r"(-?\d+)/(\d+)", rep)
                if match is not None:
                    return self.mgr.Real((int(match.group(1)),
                                          int(match.group(2))))
                else:
                    return self.mgr.Real(int(rep))
            else:
                assert self.environment.stc.get_type(item).is_int_type()
                return self.mgr.Int(int(rep))


        else:
            assert mathsat.msat_term_is_true(self.msat_env, tval) or \
                mathsat.msat_term_is_false(self.msat_env, tval)
            bval = (mathsat.msat_term_is_true(self.msat_env, tval) == 1)
            return self.mgr.Bool(bval)


    def get_model(self):
        assignment = {}
        for s in self.environment.formula_manager.get_all_symbols():
            if s.is_term():
                v = self.get_value(s)
                assignment[s] = v
        return EagerModel(assignment=assignment, environment=self.environment)


    def exit(self):
        if self.msat_env:
            mathsat.msat_destroy_env(self.msat_env)
            mathsat.msat_destroy_config(self.config)
            self.msat_env = None
            self.config = None
        return



class MSatConverter(DagWalker):

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

        self.boolType = mathsat.msat_get_bool_type(self.msat_env)
        self.realType = mathsat.msat_get_rational_type(self.msat_env)
        self.intType = mathsat.msat_get_integer_type(self.msat_env)

        self.back_memoization = {}
        return


    def back(self, expr):
        tu_env = TypeUnsafeEnvironment()
        tu_res = self._walk_back(expr, tu_env.formula_manager)
        tu_f = disambiguate(tu_env, tu_res, create_toreal_on_demand=True)
        return self.env.formula_manager.normalize(tu_f)


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
        res = None
        arity = len(args)

        if mathsat.msat_term_is_true(self.msat_env, term):
            res = mgr.TRUE()

        elif mathsat.msat_term_is_false(self.msat_env, term):
            res = mgr.FALSE()

        elif mathsat.msat_term_is_number(self.msat_env, term):
            ty = mathsat.msat_term_get_type(term)
            if mathsat.msat_is_integer_type(self.msat_env, ty):
                res = GenericNumber(int(mathsat.msat_term_repr(term)))
            elif mathsat.msat_is_rational_type(self.msat_env, ty):
                res = mgr.Real(Fraction(mathsat.msat_term_repr(term)))
            else:
                raise NotImplementedError

        elif mathsat.msat_term_is_and(self.msat_env, term):
            res = mgr.And(args)

        elif mathsat.msat_term_is_or(self.msat_env, term):
            res = mgr.Or(args)

        elif mathsat.msat_term_is_not(self.msat_env, term):
            assert arity == 1
            res = mgr.Not(args[0])

        elif mathsat.msat_term_is_iff(self.msat_env, term):
            assert arity == 2
            res = mgr.Iff(args[0], args[1])

        elif mathsat.msat_term_is_term_ite(self.msat_env, term):
            assert arity == 3
            res = mgr.Ite(args[0], args[1], args[2])

        elif mathsat.msat_term_is_equal(self.msat_env, term):
            assert arity == 2
            res = mgr.Equals(args[0], args[1])

        elif mathsat.msat_term_is_leq(self.msat_env, term):
            assert arity == 2
            res = mgr.LE(args[0], args[1])

        elif mathsat.msat_term_is_plus(self.msat_env, term):
            res = mgr.Plus(args)

        elif mathsat.msat_term_is_times(self.msat_env, term):
            assert arity == 2
            res = mgr.Times(args[0], args[1])

        elif mathsat.msat_term_is_boolean_constant(self.msat_env, term):
            rep = mathsat.msat_term_repr(term)
            res = mgr.Symbol(rep, types.BOOL)

        elif mathsat.msat_term_is_constant(self.msat_env, term):
            rep = mathsat.msat_term_repr(term)

            ty = mathsat.msat_term_get_type(term)
            if mathsat.msat_is_rational_type(self.msat_env, ty):
                res = mgr.Symbol(rep, types.REAL)
            elif mathsat.msat_is_integer_type(self.msat_env, ty):
                res = mgr.Symbol(rep, types.INT)
            else:
                raise NotImplementedError("Unsupported variable type found")

        elif mathsat.msat_term_is_uf(self.msat_env, term):
            d = mathsat.msat_term_get_decl(term)
            fun = self.get_symbol_from_declaration(d)
            res = mgr.Function(fun, args)

        else:
            raise TypeError("Unsupported expression:",
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
                for i in xrange(arity):
                    son = mathsat.msat_term_get_arg(current, i)
                    stack.append(son)
            elif self.back_memoization[current] is None:
                args=[self.back_memoization[mathsat.msat_term_get_arg(current,i)]
                      for i in xrange(arity)]
                res = self._back_single_term(current, mgr, args)
                self.back_memoization[current] = res
            else:
                # we already visited the node, nothing else to do
                pass
        return self.back_memoization[term]


    def convert(self, formula):
        """Convert a PySMT formula into a MathSat Term.

        This function might throw a InternalSolverError exception if
        an error during conversion occurs.
        """
        res = self.walk(formula)
        if mathsat.MSAT_ERROR_TERM(res):
            msat_msg = mathsat.msat_last_error_message(self.msat_env)
            raise InternalSolverError(msat_msg)
        return res


    def walk_and(self, formula, args):
        res = mathsat.msat_make_true(self.msat_env)
        for a in args:
            res = mathsat.msat_make_and(self.msat_env, res, a)
        return res

    def walk_or(self, formula, args):
        res = mathsat.msat_make_false(self.msat_env)
        for a in args:
            res = mathsat.msat_make_or(self.msat_env, res, a)
        return res

    def walk_not(self, formula, args):
        assert len(args) == 1
        return mathsat.msat_make_not(self.msat_env, args[0])

    def walk_symbol(self, formula, args):
        assert len(args) == 0
        if formula not in self.symbol_to_decl:
            self.declare_variable(formula)
        decl = self.symbol_to_decl[formula]
        return mathsat.msat_make_constant(self.msat_env, decl)

    def walk_le(self, formula, args):
        assert len(args) == 2
        return mathsat.msat_make_leq(self.msat_env, args[0], args[1])

    def walk_lt(self, formula, args):
        assert len(args) == 2
        leq = mathsat.msat_make_leq(self.msat_env, args[1], args[0])
        return mathsat.msat_make_not(self.msat_env, leq)

    def walk_ite(self, formula, args):
        assert len(args) == 3
        i = args[0]
        t = args[1]
        e = args[2]

        if self._get_type(formula).is_bool_type():
            impl = self.mgr.Implies(formula.arg(0), formula.arg(1))
            th = self.walk_implies(impl, [i,t])
            nif = self.mgr.Not(formula.arg(1))
            ni = self.walk_not(nif, [i])
            el = self.walk_implies(self.mgr.Implies(nif, formula.arg(2)), [ni,e])
            return mathsat.msat_make_and(self.msat_env, th, el)
        else:
            return mathsat.msat_make_term_ite(self.msat_env, i, t, e)

    def walk_real_constant(self, formula, args):
        assert len(args) == 0
        assert type(formula.constant_value()) == Fraction
        frac = formula.constant_value()
        n,d = frac.numerator, frac.denominator
        rep = str(n) + "/" + str(d)
        return mathsat.msat_make_number(self.msat_env, rep)

    def walk_int_constant(self, formula, args):
        assert len(args) == 0
        assert type(formula.constant_value()) == int or \
            type(formula.constant_value()) == long
        rep = str(formula.constant_value())
        return mathsat.msat_make_number(self.msat_env, rep)

    def walk_bool_constant(self, formula, args):
        assert len(args) == 0
        if formula.constant_value():
            return mathsat.msat_make_true(self.msat_env)
        else:
            return mathsat.msat_make_false(self.msat_env)

    def walk_forall(self, formula, args):
        raise NotImplementedError

    def walk_exists(self, formula, args):
        raise NotImplementedError

    def walk_plus(self, formula, args):
        res = mathsat.msat_make_number(self.msat_env, "0")
        for a in args:
            res = mathsat.msat_make_plus(self.msat_env, res, a)
        return res

    def walk_minus(self, formula, args):
        assert len(args) == 2
        n_one = mathsat.msat_make_number(self.msat_env, "-1")
        n_s2 = mathsat.msat_make_times(self.msat_env, n_one, args[1])
        return mathsat.msat_make_plus(self.msat_env, args[0], n_s2)

    def walk_equals(self, formula, args):
        assert len(args) == 2
        return mathsat.msat_make_equal(self.msat_env, args[0], args[1])

    def walk_iff(self, formula, args):
        assert len(args) == 2
        lf = formula.arg(0)
        rf = formula.arg(1)

        li = self.walk_implies(self.mgr.Implies(lf, rf), [args[0], args[1]])
        ri = self.walk_implies(self.mgr.Implies(rf, lf), [args[1], args[0]])

        return mathsat.msat_make_and(self.msat_env, li, ri)

    def walk_implies(self, formula, args):
        assert len(args) == 2
        neg = self.walk_not(self.mgr.Not(formula.arg(0)), [args[0]])
        return mathsat.msat_make_or(self.msat_env, neg, args[1])

    def walk_times(self, formula, args):
        return mathsat.msat_make_times(self.msat_env, args[0], args[1])

    def walk_function(self, formula, args):
        name = formula.function_name()
        if name not in self.symbol_to_decl:
            self.declare_variable(name)
        decl = self.symbol_to_decl[name]
        return mathsat.msat_make_uf(self.msat_env, decl, args)

    def walk_toreal(self, formula, args):
        assert len(args) == 1
        # In mathsat toreal is implicit
        return args[0]

    def _type_to_msat(self, tp):
        if tp.is_bool_type():
            return self.boolType
        elif tp.is_real_type():
            return self.realType
        elif tp.is_int_type():
            return self.intType
        elif tp.is_function_type():
            stps = [self._type_to_msat(x) for x in tp.param_types]
            rtp = self._type_to_msat(tp.return_type)
            return mathsat.msat_get_function_type(self.msat_env,
                                                stps,
                                                rtp)
        else:
            raise NotImplementedError

    def declare_variable(self, var):
        if not var.is_symbol(): raise TypeError
        if var.symbol_name() not in self.symbol_to_decl:
            tp = self._type_to_msat(var.symbol_type())
            decl = mathsat.msat_declare_function(self.msat_env,
                                                 var.symbol_name(),
                                                 tp)
            self.symbol_to_decl[var] = decl
            self.decl_to_symbol[mathsat.msat_decl_id(decl)] = var
