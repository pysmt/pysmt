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
from nose.plugins.attrib import attr

from pysmt.randomizer import build_random_formula, build_random_qf_formula
from pysmt.shortcuts import is_valid, Iff
from pysmt.shortcuts import get_env
from pysmt.type_checker import SimpleTypeChecker
from pysmt.test import TestCase, skipIfSolverNotAvailable


global FEW_ITERATIONS
global NORMAL_ITERATIONS
global MANY_ITERATIONS

FEW_ITERATIONS=5
NORMAL_ITERATIONS=10
MANY_ITERATIONS=15

class TestRand(TestCase):

    @attr("slow")
    @skipIfSolverNotAvailable('z3')
    def test_simplify_qf_hard(self):
        """Test simplifier on random formula.

        This version of the test forces the simplifier to validate
        each simplification step, therefore it is slow, and we run it
        only on few sample formulas.
        """
        for i in xrange(FEW_ITERATIONS):
            f = build_random_qf_formula(10, 20, 5, 0.1, seed=i)
            get_env().simplifier.validate_simplifications = True
            sf = f.simplify()
            get_env().simplifier.validate_simplifications = False

            res = is_valid(Iff(f, sf), solver_name='z3')
            self.assertTrue(res,
                            "Simplification did not provide equivalent "+
                            "result:\n f= %s\n sf = %s" % (f, sf))

    @attr("slow")
    @skipIfSolverNotAvailable('z3')
    def test_simplify_qf_z3(self):
        """ Test simplifier on quantifier free random formula using Z3 """
        for i in xrange(MANY_ITERATIONS):
            f = build_random_qf_formula(10, 20, 4, 0.1, seed=i)
            sf = f.simplify()
            test = Iff(f, sf)
            res = is_valid(test, solver_name='z3')

            self.assertTrue(res,
                            "Simplification of formula %d " % i +
                            "did not provide equivalent "+
                            "result:\n f= %s\n sf = %s" % (f, sf))

    @attr("slow")
    @skipIfSolverNotAvailable('msat')
    def test_simplify_qf_msat(self):
        """ Test simplifier on quantifier free random formula using MathSAT"""
        for i in xrange(MANY_ITERATIONS):
            f = build_random_qf_formula(10, 20, 4, 0.1, seed=i)
            sf = f.simplify()
            test = Iff(f, sf)
            res = is_valid(test, solver_name='msat')

            self.assertTrue(res,
                            "Simplification of formula %d " % i +
                            "did not provide equivalent "+
                            "result:\n f= %s\n sf = %s" % (f, sf))


    def test_hrserializer(self):
        for i in xrange(MANY_ITERATIONS):
            f = build_random_formula(10, 20, 5, 0.1, seed=i)
            s = str(f)
            self.assertIsNotNone(s, "String is None")
            self.assertTrue(len(s) > 0, "Empty string from formula")


    def test_substituter(self):
        # TODO
        pass

    def test_smtprinter(self):
        # TODO
        pass

    def test_simple_typecheck(self):
        for i in xrange(MANY_ITERATIONS):
            f = build_random_formula(10, 20, 5, 0.1, seed=i)
            type_ = SimpleTypeChecker().walk(f)

            self.assertIsNotNone(type_,
                                 "Type of formula %d " % i +
                                 "is not valid:\n f= %s" % f)


if __name__ == '__main__':
    import unittest

    FEW_ITERATIONS=5
    NORMAL_ITERATIONS=15
    MANY_ITERATIONS=30

    unittest.main()
