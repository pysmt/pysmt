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
from pysmt.test import TestCase, main, skipIfSolverNotAvailable
from pysmt.shortcuts import Symbol, ForAll, Solver, LT, Real, Int, Implies
from pysmt.typing import REAL, INT
from pysmt.logics import LRA, LIA


class TestCVC4Quantifiers(TestCase):

    @skipIfSolverNotAvailable('cvc4')
    def test_bool(self):
        x, y = Symbol("x"), Symbol("y")
        f = ForAll([x], Implies(x,y))
        with Solver(name='cvc4', logic=LIA) as s:
            s.add_assertion(f)
            res = s.solve()
            self.assertTrue(res)

    @skipIfSolverNotAvailable('cvc4')
    def test_int(self):
        p, q = Symbol("p", INT), Symbol("q", INT)
        f = ForAll([p], Implies(LT(Int(0), p), LT(q, p)))
        with Solver(name='cvc4', logic=LIA) as s:
            s.add_assertion(f)
            res = s.solve()
            self.assertTrue(res)

    @skipIfSolverNotAvailable('cvc4')
    def test_real(self):
        r, s = Symbol("r", REAL), Symbol("s", REAL)
        f = ForAll([r], Implies(LT(Real(0), r), LT(s, r)))
        with Solver(name='cvc4', logic=LRA) as s:
            s.add_assertion(f)
            res = s.solve()
            self.assertTrue(res)


if __name__ == '__main__':
    main()
