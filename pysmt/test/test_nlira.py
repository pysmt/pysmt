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
from fractions import Fraction

from pysmt.test import TestCase, main
from pysmt.test import skipIfSolverNotAvailable

from pysmt.oracles import get_logic
from pysmt.shortcuts import FreshSymbol, Times, Equals, Div, Real
from pysmt.shortcuts import Solver
from pysmt.typing import REAL
from pysmt.exceptions import SolverReturnedUnknownResultError


class TestNonLinear(TestCase):

    @skipIfSolverNotAvailable("z3")
    def test_times(self):
        x = FreshSymbol(REAL)
        f = Equals(Times(x, x), x)
        with Solver(name="z3") as s:
            self.assertTrue(s.is_sat(f))

    @skipIfSolverNotAvailable("z3")
    def test_div(self):
        x = FreshSymbol(REAL)
        f = Equals(Div(x, x), x)
        with Solver(name="z3") as s:
            self.assertTrue(s.is_sat(f))

    @skipIfSolverNotAvailable("z3")
    def test_irrational(self):
        x = FreshSymbol(REAL)
        f = Equals(Times(x, x), Real(2))
        with Solver(name="z3") as s:
            self.assertTrue(s.is_sat(f))
            model = s.get_model()
            approx = Fraction(-3109888511975, 2199023255552)
            self.assertEqual(model[x], Real(approx))

    def test_oracle(self):
        x = FreshSymbol(REAL)
        f = Equals(Times(x, x), Real(2))
        logic = get_logic(f)
        self.assertFalse(logic.theory.linear)

    @skipIfSolverNotAvailable("msat")
    def test_msat(self):
        x = FreshSymbol(REAL)
        f = Equals(Times(x, x), Real(2))
        with Solver(name="msat") as s:
            with self.assertRaises(SolverReturnedUnknownResultError):
                s.is_sat(f)


if __name__ == "__main__":
    main()
