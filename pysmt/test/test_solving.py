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
import pysmt.operators as op
from pysmt.shortcuts import Symbol, FreshSymbol, And, Not, GT, Function, Plus
from pysmt.shortcuts import Bool, TRUE, Real, LE, FALSE, Or
from pysmt.shortcuts import Solver
from pysmt.shortcuts import is_sat, is_valid, get_env
from pysmt.typing import BOOL, REAL, FunctionType
from pysmt.test import TestCase, skipIfNoSolverAvailable, skipIfSolverNotAvailable
from pysmt.test.examples import get_example_formulae
from pysmt.exceptions import SolverReturnedUnknownResultError, InternalSolverError
from pysmt.logics import QF_UFLIRA

class TestBasic(TestCase):

    @skipIfNoSolverAvailable
    def test_create_and_solve(self):
        solver = Solver()

        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))

        g = f.substitute({varB:varA})
        solver.add_assertion(g)
        res = solver.solve()
        self.assertFalse(res, "Formula was expected to be UNSAT")

        h = And(g, Bool(False))
        simp_h = h.simplify()
        self.assertEquals(simp_h, Bool(False))

    @skipIfNoSolverAvailable
    def test_is_sat(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        g = f.substitute({varB:varA})

        res = is_sat(g)
        self.assertFalse(res, "Formula was expected to be UNSAT")

        for solver in get_env().factory.all_solvers(): #['msat', 'z3', 'cvc4']:
            res = is_sat(g, solver_name=solver)
            self.assertFalse(res, "Formula was expected to be UNSAT")

    @skipIfNoSolverAvailable
    def test_get_py_value(self):
        varA = Symbol("A", BOOL)

        with Solver() as s:
            s.add_assertion(varA)
            s.solve()
            self.assertTrue(s.get_py_value(varA))

    @skipIfSolverNotAvailable("msat")
    def test_examples_msat(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if not logic.quantifier_free: continue
            v = is_valid(f, solver_name='msat')
            s = is_sat(f, solver_name='msat')

            self.assertEquals(validity, v, f)
            self.assertEquals(satisfiability, s, f)

    @skipIfSolverNotAvailable("cvc4")
    def test_examples_cvc4(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            try:
                v = is_valid(f, solver_name='cvc4')
                s = is_sat(f, solver_name='cvc4')

                self.assertEquals(validity, v, f)
                self.assertEquals(satisfiability, s, f)

            except SolverReturnedUnknownResultError:
                # CVC4 does not handle quantifiers in a complete way
                self.assertFalse(logic.quantifier_free)

    @skipIfSolverNotAvailable("yices")
    def test_examples_yices(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if not logic.quantifier_free: continue
            v = is_valid(f, solver_name='yices')
            s = is_sat(f, solver_name='yices')

            self.assertEquals(validity, v, f)
            self.assertEquals(satisfiability, s, f)



    def do_model(self, solver_name):
        for (f, _, satisfiability, logic) in get_example_formulae():
            if satisfiability and not logic.uninterpreted and logic.quantifier_free:
                with Solver(name=solver_name) as s:
                    s.add_assertion(f)

                    check = s.solve()
                    self.assertTrue(check)

                    # Ask single values to the solver
                    subs = {}
                    for d in f.get_dependencies():
                        m = s.get_value(d)
                        subs[d] = m

                    simp = f.substitute(subs).simplify()
                    self.assertEquals(simp, TRUE())

                    # Ask the eager model
                    subs = {}
                    model = s.get_model()
                    for d in f.get_dependencies():
                        m = model.get_value(d)
                        subs[d] = m

                    simp = f.substitute(subs).simplify()
                    self.assertEquals(simp, TRUE())

    @skipIfSolverNotAvailable("cvc4")
    def test_model_cvc4(self):
        self.do_model("cvc4")

    @skipIfSolverNotAvailable("z3")
    def test_model_z3(self):
        self.do_model("z3")

    @skipIfSolverNotAvailable("msat")
    def test_model_msat(self):
        self.do_model("msat")

    @skipIfSolverNotAvailable("z3")
    def test_examples_z3(self):
        for (f, validity, satisfiability, _) in get_example_formulae():
            v = is_valid(f, solver_name='z3')
            s = is_sat(f, solver_name='z3')

            self.assertEquals(validity, v, f)
            self.assertEquals(satisfiability, s, f)

    @skipIfNoSolverAvailable
    def test_examples_by_logic(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            v = is_valid(f, logic=logic)
            s = is_sat(f, logic=logic)

            self.assertEquals(validity, v, f)
            self.assertEquals(satisfiability, s, f)

    @skipIfNoSolverAvailable
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

                self.assertEquals(model1.get_value(v1), TRUE())
                self.assertEquals(model1.get_value(v2), FALSE())
                self.assertEquals(model2.get_value(v1), FALSE())
                self.assertEquals(model2.get_value(v2), TRUE())


    @skipIfNoSolverAvailable
    def test_solving_under_assumption_theory(self):
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)

        v1 = GT(x, Real(10))
        v2 = LE(y, Real(2))

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

                self.assertEquals(model1.get_value(v1), TRUE())
                self.assertEquals(model1.get_value(v2), FALSE())
                self.assertEquals(model2.get_value(v1), FALSE())
                self.assertEquals(model2.get_value(v2), TRUE())

    @skipIfNoSolverAvailable
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

                self.assertEquals(model1.get_value(v1), TRUE())
                self.assertEquals(model1.get_value(v2), FALSE())
                self.assertEquals(model2.get_value(v1), FALSE())
                self.assertEquals(model2.get_value(v2), TRUE())

    @skipIfNoSolverAvailable
    def test_add_assertion(self):
        r = FreshSymbol(REAL)

        f1 = Plus(r, r)
        f2 = GT(r, r)

        for sname in get_env().factory.all_solvers(logic=QF_UFLIRA):
            with Solver(name=sname) as solver:
                with self.assertRaises(TypeError):
                    solver.add_assertion(f1)
                self.assertIsNone(solver.add_assertion(f2))

    @skipIfNoSolverAvailable
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
