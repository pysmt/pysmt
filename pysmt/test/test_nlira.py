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

from pysmt.test import TestCase, main
from pysmt.test import skipIfSolverNotAvailable, skipIfNoSolverForLogic

from pysmt.oracles import get_logic
from pysmt.shortcuts import FreshSymbol, Times, Equals, Div, Real, Int, Pow
from pysmt.shortcuts import Solver, Symbol, And, Not, is_sat
from pysmt.typing import REAL, INT
from pysmt.exceptions import (ConvertExpressionError,
                              NonLinearError,
                              SolverReturnedUnknownResultError)
from pysmt.logics import QF_NRA
from pysmt.constants import Fraction


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
            xval = model[x]
            self.assertTrue(xval.is_algebraic_constant())
            # There are two solutions, that only differ by sign
            # we take the positive one
            x_approx_val = abs(xval.algebraic_approx_value())
            approx = Fraction(3109888511975, 2199023255552)
            # We only get an approximation of the actual value.
            # We check that the error of the approximation is within
            # the precision (default is 10 digits)
            err = abs(x_approx_val - approx)
            self.assertTrue(err < 0.00000000001, err)

    def test_oracle(self):
        x = FreshSymbol(REAL)
        f = Equals(Times(x, x), Real(2))
        logic = get_logic(f)
        self.assertFalse(logic.theory.linear)

    def test_unknownresult(self):
        x = FreshSymbol(REAL)
        f = Equals(Times(x, x), Real(2))
        for sname in self.env.factory.all_solvers():
            with Solver(name=sname) as s:
                if sname in ["bdd", "picosat", "btor"]:
                    with self.assertRaises(ConvertExpressionError):
                        s.is_sat(f)
                elif sname in ["yices", "cvc4", "msat"]:
                    with self.assertRaises(NonLinearError):
                        s.is_sat(f)
                else:
                    res = s.is_sat(f)
                    self.assertTrue(res, sname)
                    self.assertIn(QF_NRA, s.LOGICS, sname)

    @skipIfSolverNotAvailable("z3")
    def test_integer(self):
        x = FreshSymbol(INT)
        f = Equals(Times(x, x), Int(2))
        with Solver(name="z3") as s:
            self.assertFalse(s.is_sat(f))

        # f = Equals(Times(Int(4), Pow(x, Int(-1))), Int(2))
        # self.assertTrue(is_sat(f, solver_name="z3"))

        # f = Equals(Div(Int(4), x), Int(2))
        # self.assertTrue(is_sat(f, solver_name="z3"))

        f = Equals(Times(x, x), Int(16))
        self.assertTrue(is_sat(f, solver_name="z3"))

    @skipIfSolverNotAvailable("z3")
    def test_div_pow(self):
        x = FreshSymbol(REAL)
        f = Equals(Times(Real(4), Pow(x, Real(-1))), Real(2))
        try:
            self.assertTrue(is_sat(f))
        except SolverReturnedUnknownResultError:
            pass

        f = Equals(Div(Real(4), x), Real(2))
        try:
            self.assertTrue(is_sat(f, solver_name="z3"))
        except SolverReturnedUnknownResultError:
            pass

        f = Equals(Times(x, x), Real(16))
        try:
            self.assertTrue(is_sat(f))
        except SolverReturnedUnknownResultError:
            pass

    @skipIfNoSolverForLogic(QF_NRA)
    def test_div_by_0(self):
        varA = Symbol('A', REAL)
        varB = Symbol('B', REAL)

        f = And(Equals(varA, varB),
                Not(Equals(Div(varA, Real(0)), Div(varB, Real(0)))))

        self.assertUnsat(f)


if __name__ == "__main__":
    main()
