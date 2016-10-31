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
from pysmt.shortcuts import Solver, is_sat
from pysmt.typing import REAL, INT
from pysmt.exceptions import (ConvertExpressionError,
                              NonLinearError,
                              SolverReturnedUnknownResultError,
                              DeltaSATError)
from pysmt.logics import QF_NRA, QF_NIA
from pysmt.constants import Fraction


class TestNonLinear(TestCase):

    @skipIfSolverNotAvailable("z3")
    def test_times(self):
        x = FreshSymbol(REAL)
        f = Equals(Times(x, x), x)
        self.assertDeltaSat(f)

    @skipIfNoSolverForLogic(QF_NRA)
    def test_div(self):
        x = FreshSymbol(REAL)
        f = Equals(Div(x, x), x)
        self.assertDeltaSat(f)

    @skipIfSolverNotAvailable("z3")
    def test_irrational(self):
        x = FreshSymbol(REAL)
        f = Equals(Times(x, x), Real(2))
        with Solver(name="z3") as s:
            self.assertTrue(s.is_sat(f))
            model = s.get_model()
            xval = model[x]
            self.assertTrue(xval.is_algebraic_constant())
            approx = Fraction(-3109888511975, 2199023255552)
            self.assertEqual(xval.algebraic_approx_value(), approx)

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
                if sname in  ["bdd", "picosat", "btor"]:
                    with self.assertRaises(ConvertExpressionError):
                        s.is_sat(f)
                elif sname in ["yices", "cvc4", "msat"]:
                    with self.assertRaises(NonLinearError):
                        s.is_sat(f)
                elif sname == "dreal":
                    with self.assertRaises(DeltaSATError):
                        s.is_sat(f)
                else:
                    res = s.is_sat(f)
                    self.assertTrue(res, sname)
                    self.assertIn(QF_NRA, s.LOGICS, sname)

    @skipIfNoSolverForLogic(QF_NIA)
    def test_integer(self):
        x = FreshSymbol(INT)
        f = Equals(Times(x, x), Int(2))
        with Solver(logic=QF_NIA) as s:
            self.assertFalse(s.is_sat(f))
        f = Equals(Div(Int(4), x), Int(2))
        self.assertTrue(is_sat(f, logic=QF_NIA))
        f = Equals(Times(x, x), Int(16))
        self.assertTrue(is_sat(f))

    def test_pow(self):
        f = Pow(Real(5), Real(2.2))
        self.assertNotEqual(f, Real(25))

        f = Pow(Real(5), Real(2))
        self.assertEqual(f, Real(25))

        f = Pow(Int(5), Int(2))
        self.assertEqual(f, Int(25))


    @skipIfNoSolverForLogic(QF_NRA)
    def test_div_pow(self):
        x = FreshSymbol(REAL)
        for sname in self.env.factory.all_solvers(logic=QF_NRA):
            f = Equals(Times(Real(4), Pow(x, Real(-1))), Real(2))
            self.assertDeltaSat(f, solver_name=sname)
            f = Equals(Div(Real(4), x), Real(2))
            self.assertDeltaSat(f, solver_name=sname)
            f = Equals(Times(x, x), Real(16))
            self.assertDeltaSat(f, solver_name=sname)



if __name__ == "__main__":
    main()
