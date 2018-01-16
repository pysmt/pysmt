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
import os, sys

from pysmt.test import TestCase
from pysmt.test import skipIfSolverNotAvailable
from pysmt.test.examples import get_example_formulae
from pysmt.logics import QF_LRA, QF_UFLIRA, QF_BOOL
from pysmt.solvers.portfolio import Portfolio
from pysmt.smtlib.parser import get_formula_fname
from pysmt.shortcuts import TRUE, Implies, Equals, Symbol, FALSE
from pysmt.shortcuts import reset_env, is_sat
from pysmt.typing import REAL


class PortfolioTestCase(TestCase):

    @skipIfSolverNotAvailable("z3")
    @skipIfSolverNotAvailable("msat")
    @skipIfSolverNotAvailable("cvc4")
    def test_basic(self):
        with Portfolio(["z3", "msat", "cvc4"],
                       environment=self.env,
                       logic="QF_LRA") as p:
            for example in get_example_formulae():
                if not example.logic <= QF_LRA: continue
                res = p.is_sat(example.expr)
                self.assertEqual(res, example.is_sat, example.expr)
                if res:
                    self.assertTrue(p.get_model().get_value(example.expr).is_true())

    @skipIfSolverNotAvailable("msat")
    @skipIfSolverNotAvailable("cvc4")
    @skipIfSolverNotAvailable("yices")
    def test_smtlib(self):
        from pysmt.test.smtlib.parser_utils import SMTLIB_TEST_FILES, SMTLIB_DIR

        for (logic, f, expected_result) in SMTLIB_TEST_FILES:
            smtfile = os.path.join(SMTLIB_DIR, f)
            if logic <= QF_UFLIRA:
                self.run_smtlib(smtfile, logic, expected_result)

    @skipIfSolverNotAvailable("msat")
    def test_smtlib_multi_msat(self):
        from pysmt.test.smtlib.parser_utils import SMTLIB_TEST_FILES, SMTLIB_DIR

        # On some platforms (Windows x64) the internal pickling process requires
        # quite a lot of recursion...
        old_recursion_limit = sys.getrecursionlimit()
        sys.setrecursionlimit(999999)
        
        for (logic, f, expected_result) in SMTLIB_TEST_FILES:
            smtfile = os.path.join(SMTLIB_DIR, f)
            if logic <= QF_UFLIRA:
                env = reset_env()
                formula = get_formula_fname(smtfile, env)
                # Simplifying the formula to reduce its depth to avoid errors on some
                # platforms until issue #455 for details.
                formula = formula.simplify()
                with Portfolio([("msat", {"random_seed": 1}),
                                ("msat", {"random_seed": 17}),
                                ("msat", {"random_seed": 42})],
                               logic=logic,
                               environment=env,
                               incremental=False,
                               generate_models=False) as s:
                    res = s.is_sat(formula)
                    self.assertEqual(expected_result, res, smtfile)

        #reset recursion limit
        sys.setrecursionlimit(old_recursion_limit)

    def run_smtlib(self, smtfile, logic, expected_result):
        env = reset_env()
        formula = get_formula_fname(smtfile, env)
        with Portfolio(["cvc4", "msat", "yices"],
                       logic=logic,
                       environment=env,
                       incremental=False,
                       generate_models=False) as s:
            res = s.is_sat(formula)
            self.assertEqual(expected_result, res, smtfile)

    @skipIfSolverNotAvailable("msat")
    @skipIfSolverNotAvailable("cvc4")
    @skipIfSolverNotAvailable("z3")
    def test_shortcuts(self):
        for (expr, _, sat_res, logic) in get_example_formulae():
            if not logic <= QF_UFLIRA: continue
            res = is_sat(expr, portfolio=["z3", "cvc4", "msat"])
            self.assertEqual(res, sat_res, expr)

        with self.assertRaises(ValueError):
            is_sat(TRUE(), portfolio=["supersolver"])

    @skipIfSolverNotAvailable("msat")
    @skipIfSolverNotAvailable("picosat")
    @skipIfSolverNotAvailable("btor")
    @skipIfSolverNotAvailable("bdd")
    def test_get_value(self):
        with Portfolio(["msat", "picosat", "btor", "bdd"],
                       logic=QF_UFLIRA,
                       environment=self.env,
                       incremental=False,
                       generate_models=True) as s:
            x, y = Symbol("x"), Symbol("y")
            s.add_assertion(Implies(x, y))
            s.add_assertion(x)
            res = s.solve()
            self.assertTrue(res)
            v = s.get_value(x)
            self.assertTrue(v, TRUE())

    @skipIfSolverNotAvailable("msat")
    @skipIfSolverNotAvailable("cvc4")
    @skipIfSolverNotAvailable("yices")
    def test_incrementality(self):
        with Portfolio(["cvc4", "msat", "yices"],
                       logic=QF_UFLIRA,
                       environment=self.env,
                       incremental=True,
                       generate_models=True) as s:
            x, y = Symbol("x"), Symbol("y")
            s.add_assertion(Implies(x, y))
            s.push()
            s.add_assertion(x)
            res = s.solve()
            self.assertTrue(res)
            v = s.get_value(y)
            self.assertTrue(v, TRUE())
            s.pop()
            s.add_assertion(x)
            res = s.solve()
            self.assertTrue(res)
            v = s.get_value(x)
            self.assertTrue(v, FALSE())

    @skipIfSolverNotAvailable("z3")
    @skipIfSolverNotAvailable("bdd")
    def test_exceptions(self):
        with Portfolio(["bdd", "z3"],
                       logic=QF_BOOL,
                       environment=self.env,
                       incremental=True,
                       generate_models=True,
                       solver_options={"exit_on_exception":False}) as s:
            s.add_assertion(Equals(Symbol("r", REAL), Symbol("r", REAL)))
            res = s.solve()
            self.assertTrue(res)

            # TODO: How can we make this test more robust?
            # It assumes that bdd will raise an error before z3.
            # It should be so, but this is non-deterministic by nature
            with Portfolio(["bdd", "z3"],
                           logic=QF_BOOL,
                           environment=self.env,
                           incremental=True,
                           generate_models=True,
                           solver_options={"exit_on_exception":True}) as s:
                s.add_assertion(Equals(Symbol("r", REAL), Symbol("r", REAL)))
                with self.assertRaises(Exception):
                    s.solve()


if __name__ == "__main__":
    import unittest
    unittest.main()
