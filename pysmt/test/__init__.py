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
from functools import wraps

try:
    import unittest2 as unittest
except ImportError:
    import unittest

from pysmt.environment import get_env, reset_env
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
        assertRaisesRegex = unittest.TestCase.assertRaisesRegexp


    def assertValid(self, formula, msg=None, solver_name=None, logic=None):
        """Assert that formula is VALID."""
        self.assertTrue(self.env.factory.is_valid(formula=formula,
                                                  solver_name=solver_name,
                                                  logic=logic),
                        msg=msg)

    def assertSat(self, formula, msg=None, solver_name=None, logic=None):
        """Assert that formula is SAT."""
        self.assertTrue(self.env.factory.is_sat(formula=formula,
                                                solver_name=solver_name,
                                                logic=logic),
                        msg=msg)

    def assertUnsat(self, formula, msg=None, solver_name=None, logic=None):
        """Assert that formula is UNSAT."""
        self.assertTrue(self.env.factory.is_unsat(formula=formula,
                                                  solver_name=solver_name,
                                                  logic=logic),
                        msg=msg)


class skipIfSolverNotAvailable(object):
    """Skip a test if the given solver is not available."""

    def __init__(self, solver):
        self.solver = solver

    def __call__(self, test_fun):
        msg = "%s not available" % self.solver
        cond = self.solver not in get_env().factory.all_solvers()
        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper

class skipIfQENotAvailable(object):
    """Skip a test if the given solver does not support quantifier elimination."""

    def __init__(self, qe):
        self.qe = qe

    def __call__(self, test_fun):
        msg = "Quantifier Eliminator %s not available" % self.qe
        cond = self.qe not in get_env().factory.all_quantifier_eliminators()
        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper


class skipIfNoSolverForLogic(object):
    """Skip a test if there is no solver for the given logic."""

    def __init__(self, logic):
        self.logic = logic

    def __call__(self, test_fun):
        msg = "Solver for %s not available" % self.logic
        cond = not get_env().factory.has_solvers(logic=self.logic)
        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper


class skipIfNoUnsatCoreSolverForLogic(object):
    """Skip a test if there is no solver for the given logic."""

    def __init__(self, logic):
        self.logic = logic

    def __call__(self, test_fun):
        msg = "Unsat Core Solver for %s not available" % self.logic
        cond = len(get_env().factory.all_unsat_core_solvers(logic=self.logic)) == 0
        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper


class skipIfNoQEForLogic(object):
    """Skip a test if there is no quantifier eliminator for the given logic."""

    def __init__(self, logic):
        self.logic = logic

    def __call__(self, test_fun):
        msg = "Quantifier Eliminator for %s not available" % self.logic
        cond = len(get_env().factory.all_quantifier_eliminators(logic=self.logic)) == 0
        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper


# Export a main function
main = unittest.main

# Export SkipTest
SkipTest = unittest.SkipTest
