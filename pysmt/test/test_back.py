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
from pysmt.shortcuts import FreshSymbol, GT, And, Plus, Real, Int, LE, Iff
from pysmt.shortcuts import Solver
from pysmt.typing import REAL, INT
from pysmt.test import TestCase, skipIfSolverNotAvailable, main
from pysmt.test.examples import get_example_formulae
from pysmt.logics import QF_UFLIRA
from pysmt.exceptions import NoSolverAvailableError


class TestBasic(TestCase):

    @skipIfSolverNotAvailable("msat")
    def test_msat_back_simple(self):
        msat = Solver(name="msat", logic=QF_UFLIRA)

        r, s = FreshSymbol(REAL), FreshSymbol(INT)
        f1 = GT(r, Real(1))
        f2 = LE(Plus(s, Int(2)), Int(3))
        f3 = LE(Int(2), Int(3))
        f = And(f1, f2, f3)

        term = msat.converter.convert(f)
        res = msat.converter.back(term)

        # Checking equality is not enough: MathSAT can change the
        # shape of the formula into a logically equivalent form.
        self.assertValid(Iff(f, res), logic=QF_UFLIRA)

    @skipIfSolverNotAvailable("msat")
    def test_msat_back_not_identical(self):
        msat = Solver(name="msat", logic=QF_UFLIRA)

        r, s = FreshSymbol(REAL), FreshSymbol(REAL)
        # r + 1 > s + 1
        f = GT(Plus(r, Real(1)), Plus(s, Real(1)))

        term = msat.converter.convert(f)
        res = msat.converter.back(term)
        self.assertFalse(f == res)

    def do_back(self, solver_name, z3_string_buffer=False):
        for formula, _, _, logic in get_example_formulae():
            if logic.quantifier_free:
                if logic.theory.custom_type and z3_string_buffer:
                    # Printing of declare-sort from Z3 is not conformant
                    # with the SMT-LIB. We might consider extending our
                    # parser.
                    continue
                try:
                    s = Solver(name=solver_name, logic=logic)
                    term = s.converter.convert(formula)
                    if solver_name == "z3":
                        if z3_string_buffer:
                            res = s.converter.back_via_smtlib(term)
                        else:
                            res = s.converter.back(term)
                    else:
                        res = s.converter.back(term)
                    self.assertValid(Iff(formula, res), logic=logic,
                                     solver_name=solver_name)
                except NoSolverAvailableError:
                    pass

    @skipIfSolverNotAvailable("msat")
    def test_msat_back_formulae(self):
        self.do_back("msat")

    @skipIfSolverNotAvailable("z3")
    def test_z3_back_formulae(self):
        self.do_back("z3", z3_string_buffer=False)
        self.do_back("z3", z3_string_buffer=True)


if __name__ == '__main__':
    main()
