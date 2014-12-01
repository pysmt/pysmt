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
from pysmt.shortcuts import FreshSymbol, GT, And, Plus, Real, Int, LE, Iff
from pysmt.shortcuts import is_valid, get_env
from pysmt.typing import REAL, INT
from pysmt.test import TestCase
from pysmt.test.examples import get_example_formulae
from pysmt.logics import QF_UFLIRA


class TestBasic(TestCase):

    @unittest.skipIf('msat' not in get_env().factory.all_solvers(),
                     "MathSAT is not available.")
    def test_msat_back_simple(self):
        from pysmt.solvers.msat import MathSAT5Solver, MSatConverter

        env = get_env()
        msat = MathSAT5Solver(environment=env, logic=QF_UFLIRA)
        new_converter = MSatConverter(env, msat.msat_env)

        r, s = FreshSymbol(REAL), FreshSymbol(INT)
        f1 = GT(r, Real(1))
        f2 = LE(Plus(s, Int(2)), Int(3))
        f3 = LE(Int(2), Int(3))
        f = And(f1, f2, f3)

        term = new_converter.convert(f)
        res = new_converter.back(term)

        # Checking equality is not enough: see net test as MathSAT can
        # change the shape of the formula into a logically equivalent
        # form.
        self.assertTrue(is_valid(Iff(f, res)))


    @unittest.skipIf('msat' not in get_env().factory.all_solvers(),
                     "MathSAT is not available.")
    def test_msat_back_not_identical(self):
        from pysmt.solvers.msat import MathSAT5Solver, MSatConverter

        env = get_env()
        msat = MathSAT5Solver(environment=env, logic=QF_UFLIRA)
        new_converter = MSatConverter(env, msat.msat_env)

        r, s = FreshSymbol(REAL), FreshSymbol(REAL)
        # r + 1 > s + 1
        f = GT(Plus(r, Real(1)), Plus(s, Real(1)))

        term = new_converter.convert(f)
        res = new_converter.back(term)
        self.assertFalse(f == res)


    @unittest.skipIf('msat' not in get_env().factory.all_solvers(),
                     "MathSAT is not available.")
    def test_msat_back_formulae(self):
        from pysmt.solvers.msat import MathSAT5Solver, MSatConverter

        env = get_env()
        msat = MathSAT5Solver(environment=env, logic=QF_UFLIRA)
        new_converter = MSatConverter(env, msat.msat_env)

        for formula, _, _, logic in get_example_formulae():
            if logic.quantifier_free:
                term = new_converter.convert(formula)
                res = new_converter.back(term)
                self.assertTrue(is_valid(Iff(formula, res)))



if __name__ == '__main__':
    unittest.main()
