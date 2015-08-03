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
import unittest

from pysmt.test import TestCase
from pysmt.shortcuts import get_env, Solver, is_valid, is_sat
from pysmt.shortcuts import LE, LT, Real, GT, Int, Symbol, And, Not
from pysmt.typing import BOOL, REAL, INT
from pysmt.logics import QF_UFLIRA, QF_BOOL, QF_UFBV, get_closer_logic
from pysmt.exceptions import SolverRedefinitionError, NoLogicAvailableError

from pysmt.test.examples import get_example_formulae


BASE_DIR = os.path.dirname(os.path.abspath(__file__))

def any_wrapper():
    """Check if at least one wrapper is available."""
    return any(f.endswith(".solver.sh")
               for _, _, fnames in os.walk(BASE_DIR)
               for f in fnames)

NO_WRAPPERS_AVAILABLE = not any_wrapper()


class TestGenericWrapper(TestCase):

    def setUp(self):
        TestCase.setUp(self)

        self.all_solvers = []

        env = get_env()
        for _, _, fnames in os.walk(BASE_DIR):
            for f in fnames:
                if f.endswith(".solver.sh"):
                    name = os.path.basename(f)
                    path = os.path.join(BASE_DIR, "bin/" + f)
                    env.factory.add_generic_solver(name,
                                                   [path],
                                                   [QF_UFLIRA,
                                                    QF_UFBV])
                    self.all_solvers.append(f)


    @unittest.skipIf(NO_WRAPPERS_AVAILABLE, "No wrapper available")
    def test_generic_wrapper_basic(self):
        a = Symbol("A", BOOL)
        f = And(a, Not(a))

        for n in self.all_solvers:
            with Solver(name=n, logic=QF_BOOL) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertFalse(res)


    @unittest.skipIf(NO_WRAPPERS_AVAILABLE, "No wrapper available")
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


    @unittest.skipIf(NO_WRAPPERS_AVAILABLE, "No wrapper available")
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


    @unittest.skipIf(NO_WRAPPERS_AVAILABLE, "No wrapper available")
    def test_examples(self):
        for n in self.all_solvers:
            with Solver(name=n) as solver:
                for (f, validity, satisfiability, logic) in \
                    get_example_formulae():
                    try:
                        get_closer_logic(solver.LOGICS, logic)
                    except NoLogicAvailableError:
                        continue
                    v = is_valid(f, solver_name=n, logic=logic)
                    s = is_sat(f, solver_name=n, logic=logic)

                    self.assertEqual(validity, v, f)
                    self.assertEqual(satisfiability, s, f)


    def test_redefinition(self):
        env = get_env()
        env.factory.add_generic_solver("test__redefinition",
                                       ["/tmp/nonexistent"],
                                       [QF_UFLIRA])
        with self.assertRaises(SolverRedefinitionError):
            env.factory.add_generic_solver("test__redefinition",
                                           ["/tmp/nonexistent"],
                                           [QF_UFLIRA])


    @unittest.skipIf(NO_WRAPPERS_AVAILABLE, "No wrapper available")
    def test_reals(self):
        f = And(LT(Symbol("x", REAL), Real(2)), LE(Symbol("x", REAL), Real(3)))

        for n in self.all_solvers:
            with Solver(name=n) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertTrue(res)


    @unittest.skipIf(NO_WRAPPERS_AVAILABLE, "No wrapper available")
    def test_ints(self):
        f = And(LT(Symbol("x", INT), Int(2)), GT(Symbol("x", INT), Int(2)))

        for n in self.all_solvers:
            with Solver(name=n) as s:
                s.add_assertion(f)
                res = s.solve()
                self.assertFalse(res)

if __name__ == "__main__":
    unittest.main()
