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

from functools import wraps

from pysmt.shortcuts import reset_env, get_env
from pysmt.decorators import deprecated

class TestCase(unittest.TestCase):
    """Wrapper on the unittest TestCase class.

    This class provides setUp and tearDown methods for pySMT in which
    a fresh environment is provided for each test.
    """

    def setUp(self):
        self.env = reset_env()

    def tearDown(self):
        pass

@deprecated("skipIfNoSolverForLogic (be specific about expectations!)")
def skipIfNoSolverAvailable(test_fun):
    """Skip the test if no solver is available."""

    msg = "No solver available"
    cond = len(get_env().factory.all_solvers()) == 0
    @unittest.skipIf(cond, msg)
    @wraps(test_fun)
    def wrapper(self, *args, **kwargs):
        return test_fun(self, *args, **kwargs)
    return wrapper


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


class skipIfNoSolverForLogic(object):
    """Skip a test if there is no solver for the given logic."""

    def __init__(self, logic):
        self.logic = logic

    def __call__(self, test_fun):
        msg = "Solver for %s not available" % self.logic
        cond = len(get_env().factory.all_solvers(logic=self.logic)) == 0
        @unittest.skipIf(cond, msg)
        @wraps(test_fun)
        def wrapper(*args, **kwargs):
            return test_fun(*args, **kwargs)
        return wrapper
