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
from collections.abc import Callable
from functools import wraps

from pysmt.environment import get_env, reset_env
from pysmt.fnode import FNode
from pysmt.logics import Logic

skipIf = unittest.skipIf


class TestCase(unittest.TestCase):
    """Wrapper on the unittest TestCase class.

    This class provides setUp and tearDown methods for pySMT in which
    a fresh environment is provided for each test.
    """

    def setUp(self):
        self.env = reset_env()

    def tearDown(self):
        pass

    if "assertRaisesRegex" not in dir(unittest.TestCase):
        assertRaisesRegex = unittest.TestCase.assertRaisesRegexp  # type: ignore[attr-defined]

    def assertValid(
        self,
        formula: FNode,
        msg: str | tuple[FNode, FNode] | FNode | None = None,
        solver_name: None = None,
        logic: Logic | None = None,
    ):
        """Assert that formula is VALID."""
        self.assertTrue(
            self.env.factory.is_valid(
                formula=formula, solver_name=solver_name, logic=logic
            ),
            msg=msg,
        )

    def assertSat(
        self,
        formula: FNode,
        msg: None = None,
        solver_name: None = None,
        logic: None = None,
    ):
        """Assert that formula is SAT."""
        self.assertTrue(
            self.env.factory.is_sat(
                formula=formula, solver_name=solver_name, logic=logic
            ),
            msg=msg,
        )

    def assertUnsat(
        self,
        formula: FNode,
        msg: None = None,
        solver_name: None = None,
        logic: None = None,
    ):
        """Assert that formula is UNSAT."""
        self.assertTrue(
            self.env.factory.is_unsat(
                formula=formula, solver_name=solver_name, logic=logic
            ),
            msg=msg,
        )


class skipIfSolverNotAvailable:
    """Skip a test if the given solver is not available."""

    def __init__(self, solver):
        self.solver = solver

    def __call__(self, test_fun):
        msg = f"{self.solver} not available"
        cond = self.solver not in get_env().factory.all_solvers()

        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)

        return wrapper


class skipIfQENotAvailable:
    """Skip a test if the given solver does not support quantifier elimination."""

    def __init__(self, qe):
        self.qe = qe

    def __call__(self, test_fun):
        msg = f"Quantifier Eliminator {self.qe} not available"
        cond = self.qe not in get_env().factory.all_quantifier_eliminators()

        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)

        return wrapper


class skipIfNoSolverForLogic:
    """Skip a test if there is no solver for the given logic."""

    def __init__(self, logic: Logic):
        self.logic = logic

    def __call__(self, test_fun: Callable) -> Callable:
        msg = f"Solver for {self.logic} not available"
        cond = not get_env().factory.has_solvers(logic=self.logic)

        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)

        return wrapper


class skipIfNoUnsatCoreSolverForLogic:
    """Skip a test if there is no solver for the given logic."""

    def __init__(self, logic):
        self.logic = logic

    def __call__(self, test_fun):
        msg = f"Unsat Core Solver for {self.logic} not available"
        cond = len(get_env().factory.all_unsat_core_solvers(logic=self.logic)) == 0

        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)

        return wrapper


class skipIfNoQEForLogic:
    """Skip a test if there is no quantifier eliminator for the given logic."""

    def __init__(self, logic):
        self.logic = logic

    def __call__(self, test_fun):
        msg = f"Quantifier Eliminator for {self.logic} not available"
        cond = len(get_env().factory.all_quantifier_eliminators(logic=self.logic)) == 0

        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)

        return wrapper


class skipIfNoOptimizerForLogic:
    """Skip a test if there is no optimizer for the given logic."""

    def __init__(self, logic: Logic):
        self.logic = logic

    def __call__(self, test_fun: Callable) -> Callable:
        msg = f"Optimizer for {self.logic} not available"
        cond = len(get_env().factory.all_optimizers(logic=self.logic)) == 0

        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)

        return wrapper


# Export a main function
main = unittest.main

# Export SkipTest
SkipTest = unittest.SkipTest
