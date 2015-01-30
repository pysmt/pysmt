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

from pysmt.shortcuts import (Real, Plus, Symbol, Equals, And, Bool, Or,
                             Div, LT, Int, ToReal)
from pysmt.shortcuts import Solver, is_valid, get_env, is_sat
from pysmt.typing import REAL, BOOL, INT, FunctionType
from pysmt.test import TestCase, skipIfSolverNotAvailable, skipIfNoSolverAvailable
from pysmt.logics import QF_UFLIRA, QF_BOOL


class TestRegressions(TestCase):

    @skipIfSolverNotAvailable("msat")
    @skipIfSolverNotAvailable("z3")
    def test_plus_converts_correctly_n_ary_functions(self):
        """Handling of Plus n-ary functionality.

        Only the first two elements were translated to the solver
        """

        a = Symbol("a", REAL)
        b = Symbol("b", REAL)
        c = Symbol("c", REAL)

        p1 = Plus(a, Real((1,6)), b,c,)
        p2 = Plus(a, b, c, Real((1,6)))


        self.assertTrue(is_valid(Equals(p1, p2)))
        self.assertTrue(is_valid(Equals(p1, p2), solver_name='z3'))
        self.assertTrue(is_valid(Equals(p1, p2), solver_name='msat'))


    def test_substitute_memoization(self):
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)

        f = And(a, b)
        g = f.substitute({a:Bool(True)})
        h = f.substitute({a:Bool(False)})

        self.assertNotEquals(h, g)

    @skipIfSolverNotAvailable("msat")
    def test_msat_bool_back_conversion(self):
        f = Symbol("A")
        with Solver(name='msat') as solver:
            solver.solve()
            val = solver.get_value(Symbol("A"))
            self.assertTrue(val.is_bool_constant())

    @skipIfSolverNotAvailable("msat")
    @skipIfSolverNotAvailable("z3")
    def test_conversion_of_fractions_in_z3(self):
        self.assertTrue(is_valid(Equals(Real(Fraction(1,9)),
                                        Div(Real(1), Real(9))),
                                 solver_name="msat"))
        self.assertTrue(is_valid(Equals(Real(Fraction(1,9)),
                                        Div(Real(1), Real(9))),
                                 solver_name="z3"))

    def test_simplifying_int_plus_changes_type_of_expression(self):
        varA = Symbol("At", INT)
        varB = Symbol("Bt", INT)
        get_type = get_env().stc.get_type
        f = Plus(varB, Int(1))
        old_type = get_type(f)
        f = f.simplify()
        new_type = get_type(f)
        self.assertEqual(new_type, old_type)

    @skipIfNoSolverAvailable
    def test_nary_operators_in_solver_converter(self):
        """Conversion of n-ary operators was not handled correctly by converters."""
        x = Symbol("x")
        r = Symbol("p", REAL)
        f_and_one = And(x)
        f_or_one = Or(x)
        f_plus_one = LT(Plus(r), Real(0))

        ten_x = [x,x,x,x,x,x,x,x,x,x]
        f_and_many = And(ten_x)
        f_or_many = Or(ten_x)
        f_plus_many = LT(Plus(r,r,r,r,r,r,r,r,r,r,r), Real(0))


        for name in get_env().factory.all_solvers(logic=QF_BOOL):
            self.assertTrue(is_sat(f_and_one, solver_name=name))
            self.assertTrue(is_sat(f_or_one, solver_name=name))
            self.assertTrue(is_sat(f_and_many, solver_name=name))
            self.assertTrue(is_sat(f_or_many, solver_name=name))

        for name in get_env().factory.all_solvers(logic=QF_UFLIRA):
            self.assertTrue(is_sat(f_plus_one, solver_name=name))
            self.assertTrue(is_sat(f_plus_many, solver_name=name))

    def test_dependencies_not_includes_toreal(self):
        p = Symbol("p", INT)
        r = ToReal(p)
        deps = r.get_dependencies()

        self.assertIn(p, deps)
        self.assertNotIn(r, deps)


    def test_multiple_declaration_w_same_functiontype(self):
        ft1 = FunctionType(REAL, [REAL])
        ft2 = FunctionType(REAL, [REAL])

        f1 = Symbol("f1", ft1)
        # The following raises an exception if not (ft1 == ft2)
        # since the same symbol has already been defined with
        # a "different" type.
        f1 = Symbol("f1", ft2)

if __name__ == "__main__":
    import unittest
    unittest.main()
