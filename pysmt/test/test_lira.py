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
from pysmt.shortcuts import *
from pysmt.typing import INT, REAL, FunctionType
from pysmt.test import TestCase, main
from pysmt.logics import QF_UFLIRA, UFLIRA

class TestLIRA(TestCase):

    def test_lira(self):
        a = Symbol("a", REAL)
        b = Symbol("b", INT)

        check = And(Equals(a, Real(3)), Equals(a, ToReal(b)))
        for sname in get_env().factory.all_solvers(logic=QF_UFLIRA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(b), Int(3))


    def test_toreal(self):
        a = Symbol("a", REAL)
        b = Symbol("b", INT)

        self.assertEqual(a, ToReal(a))
        self.assertEqual(Plus(a, Real(1)), ToReal(Plus(a, Real(1))))

        self.assertEqual(ToReal(b), ToReal(ToReal(b)))
        self.assertEqual(ToReal(Plus(b, Int(1))),
                          ToReal(ToReal(Plus(b, Int(1)))))


    def test_uflira(self):
        a = Symbol("a", REAL)
        b = Symbol("b", INT)
        h = Symbol("ih", FunctionType(REAL, [REAL, INT]))

        # ( ToReal(b) = a /\ h(ToReal(b), b) >= 3) -> (h(a,b) >= 0)
        check = Implies(And(Equals(ToReal(b), a),
                            GE(Function(h, (ToReal(b), b)), Real(3))),
                        GE(Function(h, (a, b)), Real(0)))

        for sname in get_env().factory.all_solvers(logic=UFLIRA):
            self.assertValid(check, solver_name=sname)


if __name__ == '__main__':
    main()
