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
import pytest

from pysmt.test import TestCase, skipIfSolverNotAvailable, main
from pysmt.test.examples import get_example_formulae
from pysmt.environment import get_env
from pysmt.shortcuts import (Array, Store, Int, Symbol, Plus, Minus, Times,
                             Real, Equals, Iff, And, Or, Not, FALSE, TRUE)
from pysmt.typing import INT, REAL
from pysmt.simplifier import BddSimplifier
from pysmt.logics import QF_BOOL
from pysmt.exceptions import ConvertExpressionError, NoSolverAvailableError


class TestSimplify(TestCase):

    @pytest.mark.slow
    @skipIfSolverNotAvailable("z3")
    @skipIfSolverNotAvailable("cvc4")
    def test_simplify_qf(self):
        simp = get_env().simplifier
        for (f, _, _, logic) in get_example_formulae():
            if logic.is_quantified(): continue
            sname = "z3" if not logic.theory.strings else "cvc4"
            simp.validate_simplifications = sname
            sf = f.simplify()
            simp.validate_simplifications = None
            self.assertValid(Iff(f, sf), solver_name=sname,
                             msg="Simplification did not provide equivalent "+
                                "result:\n f= %s\n sf = %s" % (f, sf))

    @pytest.mark.slow
    @skipIfSolverNotAvailable("z3")
    def test_simplify_q(self):
        simp = get_env().simplifier
        for (f, _, _, logic) in get_example_formulae():
            if logic.quantifier_free: continue
            simp.validate_simplifications = "z3"
            sf = f.simplify()
            simp.validate_simplifications = None
            self.assertValid(Iff(f, sf), solver_name='z3',
                             msg="Simplification did not provide equivalent "+
                            "result:\n f= %s\n sf = %s" % (f, sf))


    def test_array_value(self):
        a1 = Array(INT, Int(0), {Int(12) : Int(10)})
        a2 = Store(Array(INT, Int(0)), Int(12), Int(10))
        self.assertEqual(a1, a2.simplify())

    @skipIfSolverNotAvailable("bdd")
    def test_bdd_simplify(self):
        s = BddSimplifier()
        for (f, _, _, logic) in get_example_formulae():
            if logic == QF_BOOL:
                fprime = s.simplify(f)
                self.assertValid(Iff(fprime, f))

        s = BddSimplifier()
        try:
            s.validate_simplifications = True
        except ValueError:
            self.assertTrue(len(self.env.factory.all_solvers())==1)
        for (f, _, _, logic) in get_example_formulae():
            if logic == QF_BOOL:
                fprime = s.simplify(f)
                self.assertValid(Iff(fprime, f))

    @skipIfSolverNotAvailable("bdd")
    @skipIfSolverNotAvailable("z3")
    def test_bdd_simplify_bool_abs(self):
        s = BddSimplifier()
        for (f, _, _, logic) in get_example_formulae():
            if not logic.theory.linear: continue
            if logic != QF_BOOL:
                with self.assertRaises(ConvertExpressionError):
                    s.simplify(f)

        s = BddSimplifier(bool_abstraction=True)
        for (f, _, _, logic) in get_example_formulae():
            if logic.quantifier_free:
                fprime = s.simplify(f)
                try:
                    self.assertValid(Iff(fprime, f))
                except NoSolverAvailableError:
                    pass

        s = BddSimplifier(bool_abstraction=True)
        f = And(Equals(Plus(Int(5), Int(1)),
                       Int(6)),
                Symbol("x"))
        fs = s.simplify(f)
        self.assertEqual(fs, Symbol("x"))


    def test_times_one(self):
        r = Symbol("r", REAL)
        f = Times(r, r, Real(1))
        f = f.simplify()
        self.assertNotIn(Real(1), f.args())


    def test_simplify_times_minus_one_in_plus(self):
        r0 = Symbol("r0", REAL)
        r1 = Symbol("r1", REAL)
        m_1 = Real(-1)
        orig = Plus(r0, Times(r1, m_1))
        simpl = orig.simplify()
        self.assertEqual(simpl, Minus(r0, r1))


    def test_simplify_coefficients_to_zero(self):
        r0 = Symbol("r0", REAL)
        m_2 = Real(-2)
        p_2 = Real(2)
        orig = Plus(Times(p_2, r0), Times(m_2, r0))
        simpl = orig.simplify()
        self.assertEqual(simpl, Real(0))

    def test_simplify_coefficients(self):
        r0 = Symbol("r0", REAL)
        r1 = Symbol("r1", REAL)
        r0r1 = Symbol("r0r1", REAL)
        m_4 = Real(-5)
        p_2 = Real(2)
        p_3 = Real(3)
        p_8 = Real(8)
        orig = Plus(Times(m_4, r0), Times(p_3, r1))
        orig = Plus(orig, Times(p_2, p_3, r0))
        orig = Minus(orig, Times(p_3, r0r1))
        orig = Plus(orig, Times(m_4, r0r1))
        simpl = orig.simplify()
        expected = Minus(Plus(Times(r1, p_3), r0), Times(r0r1, p_8))
        self.assertEquals(simpl, expected)
        self.assertValid(Equals(simpl, orig))


    def test_and_flattening(self):
        x,y,z = (Symbol(name) for name in "xyz")
        f1 = And(x, y, z)
        f2 = And(x, And(y, z))
        self.assertEqual(f2.simplify(), f1)

    def test_or_flattening(self):
        x,y,z = (Symbol(name) for name in "xyz")
        f1 = Or(x, y, z)
        f2 = Or(x, Or(y, z))
        self.assertEqual(f2.simplify(), f1)

    def test_trivial_false_and(self):
        x,y,z = (Symbol(name) for name in "xyz")
        f = And(x, y, z, Not(x))
        self.assertEqual(f.simplify(), FALSE())

    def test_trivial_true_or(self):
        x,y,z = (Symbol(name) for name in "xyz")
        f = Or(x, y, z, Not(x))
        self.assertEqual(f.simplify(), TRUE())

    def test_trivial_true_times(self):
        x,y,z = (Symbol(name, REAL) for name in "xyz")
        f = Equals(Times(x, z, y), Times(z, y, x))
        self.assertEqual(f.simplify(), TRUE())

if __name__ == '__main__':
    main()
