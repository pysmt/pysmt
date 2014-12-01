import os
import unittest

from pysmt.shortcuts import *
from pysmt.test import TestCase
from pysmt.shortcuts import Symbol, And, Not, get_env, Solver
from pysmt.typing import BOOL, REAL, INT
from pysmt.logics import QF_UFLIRA, QF_BOOL
from pysmt.exceptions import SolverRedefinitionError

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
                                                   [QF_UFLIRA])
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
            for (f, validity, satisfiability, logic) in get_example_formulae():
                if not logic.quantifier_free: continue
                v = is_valid(f, solver_name=n, logic=logic)
                s = is_sat(f, solver_name=n, logic=logic)

                self.assertEquals(validity, v, f)
                self.assertEquals(satisfiability, s, f)


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
