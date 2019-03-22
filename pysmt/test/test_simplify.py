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
from nose.plugins.attrib import attr
from pysmt.test import TestCase, skipIfSolverNotAvailable, main
from pysmt.test.examples import get_example_formulae
from pysmt.environment import get_env
from pysmt.shortcuts import (Array, Store, Int, Iff, Symbol, Plus, Equals, And,
                             Real, Times, Not, FALSE, Or, TRUE)
from pysmt.typing import INT, REAL
from pysmt.simplifier import BddSimplifier
from pysmt.logics import QF_BOOL
from pysmt.exceptions import ConvertExpressionError


class TestSimplify(TestCase):

    @attr("slow")
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

    @attr("slow")
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
                self.assertValid(Iff(fprime, f))

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
