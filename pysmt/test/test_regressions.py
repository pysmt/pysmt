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
from six.moves import xrange

from pysmt.shortcuts import (Real, Plus, Symbol, Equals, And, Bool, Or,
                             Div, LT, LE, Int, ToReal, Iff, Exists, Times)
from pysmt.shortcuts import Solver, get_env, qelim, get_model, TRUE, ExactlyOne
from pysmt.typing import REAL, BOOL, INT, FunctionType
from pysmt.test import TestCase, skipIfSolverNotAvailable, skipIfNoSolverForLogic
from pysmt.logics import QF_UFLIRA, QF_BOOL, LIA
from pysmt.exceptions import ConvertExpressionError
from pysmt.test.examples import get_example_formulae
from pysmt.environment import Environment

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


        self.assertValid(Equals(p1, p2))
        self.assertValid(Equals(p1, p2), solver_name='z3')
        self.assertValid(Equals(p1, p2), solver_name='msat')


    def test_substitute_memoization(self):
        a = Symbol("A", BOOL)
        b = Symbol("B", BOOL)

        f = And(a, b)
        g = f.substitute({a:Bool(True)})
        h = f.substitute({a:Bool(False)})

        self.assertNotEqual(h, g)

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
        self.assertValid(Equals(Real(Fraction(1,9)),
                                Div(Real(1), Real(9))),
                         solver_name="msat")
        self.assertValid(Equals(Real(Fraction(1,9)),
                                Div(Real(1), Real(9))),
                         solver_name="z3")

    def test_simplifying_int_plus_changes_type_of_expression(self):
        varA = Symbol("At", INT)
        varB = Symbol("Bt", INT)
        get_type = get_env().stc.get_type
        f = Plus(varB, Int(1))
        old_type = get_type(f)
        f = f.simplify()
        new_type = get_type(f)
        self.assertEqual(new_type, old_type)

    @skipIfNoSolverForLogic(QF_UFLIRA)
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
            self.assertSat(f_and_one, solver_name=name)
            self.assertSat(f_or_one, solver_name=name)
            self.assertSat(f_and_many, solver_name=name)
            self.assertSat(f_or_many, solver_name=name)

        for name in get_env().factory.all_solvers(logic=QF_UFLIRA):
            self.assertSat(f_plus_one, solver_name=name)
            self.assertSat(f_plus_many, solver_name=name)

    def test_dependencies_not_includes_toreal(self):
        p = Symbol("p", INT)
        r = ToReal(p)
        deps = r.get_free_variables()

        self.assertIn(p, deps)
        self.assertNotIn(r, deps)

    def test_infix_notation_wrong_le(self):
        p = Symbol("p", INT)
        get_env().enable_infix_notation = True
        self.assertEqual(LE(p, Int(2)), p <= Int(2))


    def test_multiple_declaration_w_same_functiontype(self):
        ft1 = FunctionType(REAL, [REAL])
        ft2 = FunctionType(REAL, [REAL])

        f1 = Symbol("f1", ft1)
        # The following raises an exception if not (ft1 == ft2)
        # since the same symbol has already been defined with
        # a "different" type.
        f1 = Symbol("f1", ft2)

    @skipIfSolverNotAvailable("z3")
    def test_z3_iff(self):
        z3 = Solver(name="z3")
        conv = z3.converter

        x, y = Symbol("x"), Symbol("y")
        term = conv.convert(Iff(x, y))
        back = conv.back(term)
        self.assertEqual(Iff(x, y), back)

    @skipIfSolverNotAvailable("msat")
    def test_msat_iff(self):
        msat = Solver(name="msat")
        conv = msat.converter

        x, y = Symbol("x"), Symbol("y")
        term = conv.convert(Iff(x, y))
        back = conv.back(term)
        # Mathsat can reorder variables...
        self.assertTrue(Iff(x, y) == back or Iff(y, x) == back)


    def test_multiple_exit(self):
        for sname in get_env().factory.all_solvers():
            # Multiple exits should be ignored
            s = Solver(name=sname)
            s.exit()
            s.exit()
            self.assertTrue(True)

    @skipIfNoSolverForLogic(LIA)
    def test_lia_qe_requiring_modulus(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        f = Exists([x], Equals(y, Times(x, Int(2))))
        with self.assertRaises(ConvertExpressionError):
            qelim(f)

        try:
            qelim(f)
        except ConvertExpressionError as ex:
            # The modulus operator must be there
            self.assertIn("%2", str(ex.expression))

    @skipIfSolverNotAvailable("msat")
    def test_msat_partial_model(self):
        msat = Solver(name="msat")
        x, y = Symbol("x"), Symbol("y")
        msat.add_assertion(x)
        c = msat.solve()
        self.assertTrue(c)

        model = msat.get_model()
        self.assertNotIn(y, model)
        self.assertIn(x, model)
        msat.exit()

    @skipIfSolverNotAvailable("z3")
    def test_z3_model_iteration(self):
        x, y = Symbol("x"), Symbol("y")
        m = get_model(And(x, y), solver_name="z3")
        self.assertIsNotNone(m)

        for _, v in m:
            self.assertEqual(v, TRUE())

    def test_exactlyone_w_generator(self):
        x, y = Symbol("x"), Symbol("y")

        elems = [x,y]
        f1 = ExactlyOne(elems)
        f2 = ExactlyOne(e for e in elems)

        self.assertEquals(f1, f2)

    def test_determinism(self):
        def get_set(env):
            mgr = env.formula_manager
            r = set(mgr.Symbol("x%d" % i) for i in xrange(1000))
            for (f, _, _, _) in get_example_formulae(env):
                r |= set([f])
            return r

        # As first thing on the environment we build the set of formulae
        l1 = list(get_set(get_env()))

        # We try this ten times...
        for _ in xrange(10):
            # Do something to screw up memory layout...
            for y in (Symbol("y%d" % i) for i in xrange(1000)):
                self.assertIsNotNone(y)

            with Environment() as new_env:
                # As first thing on the environment we build the set of formulae
                l_test = list(get_set(new_env))

                # The ordering of the sets should be the same...
                for i,f in enumerate(l1):
                    nf = new_env.formula_manager.normalize(f)
                    self.assertEquals(nf, l_test[i])

    def test_is_one(self):
        self.assertTrue(Int(1).is_one())
        self.assertTrue(Real(1).is_one())
        self.assertTrue(Int(0).is_zero())
        self.assertTrue(Real(0).is_zero())

    def test_substitute_to_real(self):
        p = Symbol("p", INT)
        f = LT(ToReal(p), Real(0))

        new_f = f.substitute({p: Real(1)}).simplify()
        self.assertEqual(new_f, Bool(False))


if __name__ == "__main__":
    import unittest
    unittest.main()
