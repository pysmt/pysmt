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
import unittest
from six.moves import xrange

import pysmt.operators as op
from pysmt.shortcuts import Symbol, FreshSymbol, And, Not, GT, Function, Plus
from pysmt.shortcuts import Bool, TRUE, Real, LE, FALSE, Or, Equals, Implies
from pysmt.shortcuts import Solver
from pysmt.shortcuts import get_env, get_model, is_valid, is_sat, get_implicant
from pysmt.typing import BOOL, REAL, FunctionType
from pysmt.test import TestCase, skipIfSolverNotAvailable, skipIfNoSolverForLogic
from pysmt.test.examples import get_example_formulae
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              InternalSolverError, NoSolverAvailableError)
from pysmt.logics import QF_UFLIRA, QF_BOOL, QF_LRA, QF_BV, AUTO

class TestBasic(TestCase):

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_create_and_solve(self):
        solver = Solver(logic=QF_BOOL)

        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))

        g = f.substitute({varB:varA})
        solver.add_assertion(g)
        res = solver.solve()
        self.assertFalse(res, "Formula was expected to be UNSAT")

        h = And(g, Bool(False))
        simp_h = h.simplify()
        self.assertEqual(simp_h, Bool(False))

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_is_sat(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        g = f.substitute({varB:varA})

        self.assertUnsat(g, logic=QF_BOOL,
                         msg="Formula was expected to be UNSAT")

        for solver in get_env().factory.all_solvers():
            self.assertUnsat(g, solver_name=solver,
                             msg="Formula was expected to be UNSAT")

    # This test works only if is_sat requests QF_BOOL as logic, since
    # that is the only logic handled by BDDs
    @skipIfSolverNotAvailable("bdd")
    def test_get_logic_in_is_sat(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        self.assertSat(f, logic=AUTO)

    @skipIfSolverNotAvailable("bdd")
    def test_default_logic_in_is_sat(self):
        factory = get_env().factory
        factory.default_logic = QF_BOOL

        self.assertEquals(factory.default_logic, QF_BOOL)
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        self.assertSat(f)


    @skipIfNoSolverForLogic(QF_BOOL)
    def test_get_model_unsat(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        g = f.substitute({varB:varA})

        res = get_model(g, logic=QF_BOOL)
        self.assertIsNone(res, "Formula was expected to be UNSAT")

        for solver in get_env().factory.all_solvers(logic=QF_BOOL):
            res = get_model(g, solver_name=solver)
            self.assertIsNone(res, "Formula was expected to be UNSAT")

    @skipIfNoSolverForLogic(QF_LRA)
    def test_get_model_sat(self):
        varA = Symbol("A", BOOL)
        varX = Symbol("X", REAL)

        f = And(varA, Equals(varX, Real(8)))

        res = get_model(f, logic=QF_LRA)
        self.assertIsNotNone(res, "Formula was expected to be SAT")
        self.assertTrue(res.get_value(varA) == TRUE())
        self.assertTrue(res.get_value(varX) == Real(8))

        for solver in get_env().factory.all_solvers(logic=QF_LRA):
            res = get_model(f, solver_name=solver)
            self.assertIsNotNone(res, "Formula was expected to be SAT")
            self.assertTrue(res.get_value(varA) == TRUE())
            self.assertTrue(res.get_value(varX) == Real(8))

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_get_implicant_unsat(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        g = f.substitute({varB:varA})

        res = get_implicant(g, logic=QF_BOOL)
        self.assertIsNone(res, "Formula was expected to be UNSAT")

        for solver in get_env().factory.all_solvers(logic=QF_BOOL):
            res = get_implicant(g, solver_name=solver)
            self.assertIsNone(res, "Formula was expected to be UNSAT")

    @skipIfNoSolverForLogic(QF_LRA)
    def test_get_implicant_sat(self):
        varA = Symbol("A", BOOL)
        varX = Symbol("X", REAL)

        f = And(varA, Equals(varX, Real(8)))

        res = get_implicant(f, logic=QF_LRA)
        self.assertIsNotNone(res, "Formula was expected to be SAT")
        self.assertValid(Implies(res, f), logic=QF_LRA)

        for solver in get_env().factory.all_solvers(logic=QF_LRA):
            res = get_implicant(f, solver_name=solver)
            self.assertIsNotNone(res, "Formula was expected to be SAT")
            self.assertTrue(is_valid(Implies(res, f)))


    @skipIfNoSolverForLogic(QF_BOOL)
    def test_get_py_value(self):
        varA = Symbol("A", BOOL)

        with Solver(logic=QF_BOOL) as s:
            s.add_assertion(varA)
            s.solve()
            self.assertTrue(s.get_py_value(varA))

    @skipIfSolverNotAvailable("msat")
    def test_examples_msat(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if not logic.quantifier_free: continue
            v = is_valid(f, solver_name='msat')
            s = is_sat(f, solver_name='msat')

            self.assertEqual(validity, v, f)
            self.assertEqual(satisfiability, s, f)

    @skipIfSolverNotAvailable("cvc4")
    def test_examples_cvc4(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if logic == QF_BV: continue
            try:
                if not logic.quantifier_free: continue
                v = is_valid(f, solver_name='cvc4')
                s = is_sat(f, solver_name='cvc4')

                self.assertEqual(validity, v, f)
                self.assertEqual(satisfiability, s, f)

            except SolverReturnedUnknownResultError:
                # CVC4 does not handle quantifiers in a complete way
                self.assertFalse(logic.quantifier_free)

    @skipIfSolverNotAvailable("yices")
    def test_examples_yices(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if logic == QF_BV: continue
            if not logic.quantifier_free: continue
            v = is_valid(f, solver_name='yices')
            s = is_sat(f, solver_name='yices')

            self.assertEqual(validity, v, f)
            self.assertEqual(satisfiability, s, f)



    def do_model(self, solver_name):
        for (f, _, satisfiability, logic) in get_example_formulae():
            if satisfiability and not logic.theory.uninterpreted and logic.quantifier_free:
                try:
                    with Solver(name=solver_name, logic=logic) as s:
                        s.add_assertion(f)

                        check = s.solve()
                        self.assertTrue(check)

                        # Ask single values to the solver
                        subs = {}
                        for d in f.get_free_variables():
                            m = s.get_value(d)
                            subs[d] = m

                        simp = f.substitute(subs).simplify()
                        self.assertEqual(simp, TRUE(), "%s -- %s :> %s" % (f, subs, simp))

                        # Ask the eager model
                        subs = {}
                        model = s.get_model()
                        for d in f.get_free_variables():
                            m = model.get_value(d)
                            subs[d] = m

                        simp = f.substitute(subs).simplify()
                        self.assertEqual(simp, TRUE())
                except NoSolverAvailableError:
                    pass

    @skipIfSolverNotAvailable("cvc4")
    def test_model_cvc4(self):
        self.do_model("cvc4")

    @skipIfSolverNotAvailable("z3")
    def test_model_z3(self):
        self.do_model("z3")

    @skipIfSolverNotAvailable("msat")
    def test_model_msat(self):
        self.do_model("msat")

    @skipIfSolverNotAvailable("yices")
    def test_model_yices(self):
        self.do_model("yices")

    @skipIfSolverNotAvailable("picosat")
    def test_model_picosat(self):
        self.do_model("picosat")


    @skipIfSolverNotAvailable("z3")
    def test_examples_z3(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if logic == QF_BV: continue
            v = is_valid(f, solver_name='z3')
            s = is_sat(f, solver_name='z3')

            self.assertEqual(validity, v, f)
            self.assertEqual(satisfiability, s, f)

    def test_examples_by_logic(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if len(get_env().factory.all_solvers(logic=logic)) > 0:
                v = is_valid(f, logic=logic)
                s = is_sat(f, logic=logic)

                self.assertEqual(validity, v, f.serialize())
                self.assertEqual(satisfiability, s, f.serialize())


    def test_examples_get_implicant(self):
        for (f, _, satisfiability, logic) in get_example_formulae():
            if logic.quantifier_free and \
               (get_env().factory.all_solvers(logic=logic)) > 0:
                f_i = get_implicant(f, logic=logic)
                if satisfiability:
                    self.assertValid(Implies(f_i, f), logic=logic)
                else:
                    self.assertIsNone(f_i)

    def test_solving_under_assumption(self):
        v1, v2 = [FreshSymbol() for _ in xrange(2)]
        xor = Or(And(v1, Not(v2)), And(Not(v1), v2))

        for name in get_env().factory.all_solvers():
            with Solver(name=name) as solver:
                solver.add_assertion(xor)
                res1 = solver.solve(assumptions=[v1, Not(v2)])
                model1 = solver.get_model()
                res2 = solver.solve(assumptions=[Not(v1), v2])
                model2 = solver.get_model()
                res3 = solver.solve(assumptions=[v1, v2])
                self.assertTrue(res1)
                self.assertTrue(res2)
                self.assertFalse(res3)

                self.assertEqual(model1.get_value(v1), TRUE())
                self.assertEqual(model1.get_value(v2), FALSE())
                self.assertEqual(model2.get_value(v1), FALSE())
                self.assertEqual(model2.get_value(v2), TRUE())


    def test_solving_under_assumption_theory(self):
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)

        v1 = GT(x, Real(10))
        v2 = LE(y, Real(2))

        xor = Or(And(v1, Not(v2)), And(Not(v1), v2))

        for name in get_env().factory.all_solvers(logic=QF_LRA):
            with Solver(name=name) as solver:
                solver.add_assertion(xor)
                res1 = solver.solve(assumptions=[v1, Not(v2)])
                model1 = solver.get_model()
                res2 = solver.solve(assumptions=[Not(v1), v2])
                model2 = solver.get_model()
                res3 = solver.solve(assumptions=[v1, v2])
                self.assertTrue(res1)
                self.assertTrue(res2)
                self.assertFalse(res3)

                self.assertEqual(model1.get_value(v1), TRUE())
                self.assertEqual(model1.get_value(v2), FALSE())
                self.assertEqual(model2.get_value(v1), FALSE())
                self.assertEqual(model2.get_value(v2), TRUE())

    def test_solving_under_assumption_mixed(self):
        x = Symbol("x", REAL)

        v1 = GT(x, Real(10))
        v2 = Symbol("v2", BOOL)

        xor = Or(And(v1, Not(v2)), And(Not(v1), v2))

        for name in get_env().factory.all_solvers(logic=QF_UFLIRA):
            with Solver(name=name) as solver:
                solver.add_assertion(xor)
                res1 = solver.solve(assumptions=[v1, Not(v2)])
                model1 = solver.get_model()
                res2 = solver.solve(assumptions=[Not(v1), v2])
                model2 = solver.get_model()
                res3 = solver.solve(assumptions=[v1, v2])
                self.assertTrue(res1)
                self.assertTrue(res2)
                self.assertFalse(res3)

                self.assertEqual(model1.get_value(v1), TRUE())
                self.assertEqual(model1.get_value(v2), FALSE())
                self.assertEqual(model2.get_value(v1), FALSE())
                self.assertEqual(model2.get_value(v2), TRUE())

    def test_add_assertion(self):
        r = FreshSymbol(REAL)

        f1 = Plus(r, r)
        f2 = GT(r, r)

        for sname in get_env().factory.all_solvers(logic=QF_LRA):
            with Solver(name=sname) as solver:
                with self.assertRaises(TypeError):
                    solver.add_assertion(f1)
                self.assertIsNone(solver.add_assertion(f2))

    def test_get_value_of_function(self):
        """get_value on a function should raise an exception."""
        h = Symbol("h", FunctionType(REAL, [REAL, REAL]))

        h_0_0 = Function(h, (Real(0), Real(1)))
        f = GT(h_0_0, Real(0))
        for sname in get_env().factory.all_solvers(logic=QF_UFLIRA):
            with Solver(name=sname) as solver:
                solver.add_assertion(f)
                res = solver.solve()
                self.assertTrue(res)
                with self.assertRaises(TypeError):
                    solver.get_value(h)
                self.assertIsNotNone(solver.get_value(h_0_0))


    @skipIfSolverNotAvailable("msat")
    def test_msat_converter_on_msat_error(self):
        import mathsat
        import _mathsat
        from pysmt.solvers.msat import MathSAT5Solver, MSatConverter


        env = get_env()
        msat = MathSAT5Solver(env, logic=QF_UFLIRA)
        new_converter = MSatConverter(env, msat.msat_env)

        def walk_plus(formula, args):
            res = mathsat.MSAT_MAKE_ERROR_TERM()
            return res

        # Replace the function used to compute the Plus()
        # with one that returns a msat_error
        new_converter.functions[op.PLUS] = walk_plus

        r, s = FreshSymbol(REAL), FreshSymbol(REAL)
        f1 = GT(r, s)
        f2 = Plus(r, s)

        t1 = new_converter.convert(f1)
        self.assertFalse(mathsat.MSAT_ERROR_TERM(t1))

        with self.assertRaises(InternalSolverError):
            new_converter.convert(f2)


if __name__ == '__main__':
    unittest.main()
