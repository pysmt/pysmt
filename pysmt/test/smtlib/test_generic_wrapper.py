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
import os
from unittest import skipIf

from fractions import Fraction

from pysmt.test import TestCase, main
from pysmt.shortcuts import get_env, Solver, is_valid, is_sat
from pysmt.shortcuts import LE, LT, Real, GT, Int, Symbol, And, Not, Type
from pysmt.shortcuts import FunctionType, Equals, Function, TRUE, Implies, Plus
from pysmt.typing import BOOL, REAL, INT
from pysmt.logics import QF_UFLIRA, QF_UFLRA, QF_UFLIA, QF_BOOL, QF_UFBV, QF_LRA
from pysmt.exceptions import (SolverRedefinitionError, NoSolverAvailableError,
                              UnknownSolverAnswerError)

from pysmt.test.examples import get_example_formulae

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
ALL_WRAPPERS = []

for _, _, fnames in os.walk(BASE_DIR):
    for f in fnames:
        if f.endswith(".solver.sh"):
            name = os.path.basename(f)
            path = os.path.join(BASE_DIR, "bin/" + f)
            ALL_WRAPPERS.append((name, path))


class TestGenericWrapper(TestCase):

    def setUp(self):
        TestCase.setUp(self)

        self.all_solvers = []
        for (name, path) in ALL_WRAPPERS:
            self.env.factory.add_generic_solver(name,
                                           [path],
                                           [QF_UFLRA,
                                            QF_UFLIA,
                                            QF_UFBV])
            self.all_solvers.append(name)


    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_generic_wrapper_basic(self):
        a = Symbol("A", BOOL)
        f = And(a, Not(a))

        for n in self.all_solvers:
            with Solver(name=n, logic=QF_BOOL) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertFalse(res)

    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_generic_wrapper_enable_debug(self):
        a = Symbol("A", BOOL)
        f = And(a, Not(a))

        for n in self.all_solvers:
            with Solver(name=n, logic=QF_BOOL,
                        solver_options={'debug_interaction':True}) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertFalse(res)


    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_generic_wrapper_model(self):
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        f = And(a, Not(b))

        for n in self.all_solvers:
            with Solver(name=n, logic=QF_BOOL) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertTrue(res)

                self.assertFalse(s.get_py_value(b))
                self.assertTrue(s.get_py_value(a))

    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_generic_wrapper_eager_model(self):
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        f = And(a, Not(b))

        for n in self.all_solvers:
            model = None
            with Solver(name=n, logic=QF_BOOL) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertTrue(res)
                model = s.get_model()

            self.assertFalse(model.get_value(b).is_true())
            self.assertTrue(model.get_value(a).is_true())

    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_generic_wrapper_model_env_unused_vars(self):
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)
        c = Symbol("C", BOOL)
        d = Symbol("D", BOOL)
        unused = And(c, d)
        f = And(a, Not(b))

        for n in self.all_solvers:
            model = None
            with Solver(name=n, logic=QF_BOOL) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertTrue(res)
                model = s.get_model()

            self.assertFalse(model.get_value(b).is_true())
            self.assertTrue(model.get_value(a).is_true())


    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_custom_types(self):
        A = Type("A", 0)
        a, b = Symbol("a", A), Symbol("b", A)
        p = Symbol("p", INT)
        fun = Symbol("g", FunctionType(A, [INT, A]))
        app = Function(fun, [p, b])
        f_a = Equals(a, app)
        for n in self.all_solvers:
            with Solver(name=n, logic=QF_UFLIA) as s:
                s.add_assertion(f_a)
                res = s.solve()
                self.assertTrue(res)

    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_examples(self):
        for name in self.all_solvers:
            for example in get_example_formulae():
                f = example.expr
                try:
                    v = is_valid(f, solver_name=name)
                    s = is_sat(f, solver_name=name)
                    self.assertEqual(example.is_valid, v, f)
                    self.assertEqual(example.is_sat, s, f)
                except NoSolverAvailableError:
                    # The solver does not support the specified logic
                    continue
                except UnknownSolverAnswerError:
                    # MathSAT does not deal with UF with boolean args.
                    # This is handled via the native API, but not via the
                    # SMT-LIB Wrapper
                    self.assertTrue(name == "mathsat.solver.sh", name)

    def test_redefinition(self):
        env = get_env()
        env.factory.add_generic_solver("test__redefinition",
                                       ["/tmp/nonexistent"],
                                       [QF_UFLIRA])
        with self.assertRaises(SolverRedefinitionError):
            env.factory.add_generic_solver("test__redefinition",
                                           ["/tmp/nonexistent"],
                                           [QF_UFLIRA])

    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_reals(self):
        f = And(LT(Symbol("x", REAL), Real(2)),
                LE(Symbol("x", REAL), Real(3)))
        for n in self.all_solvers:
            with Solver(name=n, logic=QF_UFLRA) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertTrue(res)

    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_ints(self):
        f = And(LT(Symbol("x", INT), Int(2)),
                GT(Symbol("x", INT), Int(2)))
        for n in self.all_solvers:
            with Solver(name=n, logic=QF_UFLIA) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertFalse(res)


    @skipIf(len(ALL_WRAPPERS) == 0, "No wrapper available")
    def test_clear_pop_smtlibsolver(self):
        for n in self.all_solvers:
            with Solver(name=n, logic=QF_LRA) as s:
                x1, x2 = [Symbol(var, REAL) for var in ["x1", "x2"]]
                init = LT(Plus(x1, Real(-1), x2), Real(Fraction(1,4)))
                invar = TRUE()
                safe = LT(Plus(x1, x2), Real(8))
                invar_init = And(invar, init)
                iv_imp = Implies(invar, safe)

                self.assertFalse(s.is_unsat(invar_init))
                self.assertFalse(s.is_valid(iv_imp))


if __name__ == "__main__":
    main()
