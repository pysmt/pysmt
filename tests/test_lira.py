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
from pysmt.constants import Fraction
from pysmt.exceptions import PysmtTypeError
from pysmt.typing import INT, REAL, FunctionType
from pysmt.test import TestCase, main
from pysmt.logics import QF_LIRA, QF_UFLIRA, UFLIRA

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


    def test_toint_is_floor(self):
        # to_int rounds towards minus infinity, it does not truncate
        self.assertEqual(ToInt(Real(Fraction(-3, 2))), Int(-2))
        self.assertEqual(ToInt(Real(Fraction(3, 2))), Int(1))
        self.assertEqual(ToInt(Real(Fraction(-1, 3))), Int(-1))
        self.assertEqual(ToInt(Real(0)), Int(0))
        self.assertEqual(ToInt(Real(-2)), Int(-2))


    def test_toint(self):
        a = Symbol("a", REAL)
        b = Symbol("b", INT)

        # Casting an Int is a no-op
        self.assertEqual(b, ToInt(b))
        self.assertEqual(Plus(b, Int(1)), ToInt(Plus(b, Int(1))))

        self.assertTrue(ToInt(a).is_toint())
        self.assertEqual(get_type(ToInt(a)), INT)

        for bad in (TRUE(), Symbol("x"), BV(1, 8)):
            with self.assertRaises(PysmtTypeError):
                ToInt(bad)


    def test_toint_simplify(self):
        a = Symbol("a", REAL)
        b = Symbol("b", INT)

        # to_int(to_real(b)) is b, since b is an integer
        self.assertEqual(b, ToInt(ToReal(b)).simplify())
        self.assertEqual(Plus(b, Int(1)),
                         ToInt(ToReal(Plus(b, Int(1)))).simplify())

        # The converse does NOT hold: to_real(to_int(a)) is a only when a
        # happens to have an integer value.
        self.assertNotEqual(a, ToReal(ToInt(a)).simplify())


    def test_isint(self):
        a = Symbol("a", REAL)
        b = Symbol("b", INT)

        # is_int is expanded into its SMT-LIB definition
        self.assertEqual(IsInt(a), Equals(a, ToReal(ToInt(a))))
        # An Int is trivially an integer
        self.assertEqual(IsInt(b), TRUE())

        with self.assertRaises(PysmtTypeError):
            IsInt(TRUE())


    def test_toint_solving(self):
        a = Symbol("a", REAL)

        for sname in get_env().factory.all_solvers(logic=QF_LIRA):
            # 7/2 floors to 3
            self.assertSat(And(Equals(a, Real(Fraction(7, 2))),
                               Equals(ToInt(a), Int(3))),
                           solver_name=sname)
            # -3/2 floors to -2, and in particular not to -1
            self.assertSat(And(Equals(a, Real(Fraction(-3, 2))),
                               Equals(ToInt(a), Int(-2))),
                           solver_name=sname)
            self.assertUnsat(And(Equals(a, Real(Fraction(-3, 2))),
                                 Equals(ToInt(a), Int(-1))),
                             solver_name=sname)
            # 1/2 is not an integer
            self.assertUnsat(And(IsInt(a), Equals(a, Real(Fraction(1, 2)))),
                             solver_name=sname)
            self.assertSat(And(IsInt(a), Equals(a, Real(Fraction(4, 2)))),
                           solver_name=sname)


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
