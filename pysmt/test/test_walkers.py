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
import pysmt.operators as op

from pysmt.shortcuts import FreshSymbol, Symbol, Int, Bool, ForAll
from pysmt.shortcuts import And, Or, Iff, Not, Function, Real
from pysmt.shortcuts import LT, GT, Plus, Minus, Equals
from pysmt.shortcuts import get_env, substitute, TRUE
from pysmt.typing import INT, BOOL, REAL, FunctionType
from pysmt.walkers import TreeWalker, DagWalker, IdentityDagWalker
from pysmt.test import TestCase, main
from pysmt.formula import FormulaManager
from pysmt.test.examples import get_example_formulae
from pysmt.exceptions import UnsupportedOperatorError

from six.moves import xrange


class TestWalkers(TestCase):

    def test_subst(self):
        varA = Symbol("At", INT)
        varB = Symbol("Bt", INT)

        f = And(LT(varA, Plus(varB, Int(1))),
                GT(varA, Minus(varB, Int(1))))
        g = Equals(varA, varB)
        h = Iff(f, g)

        res = substitute(h, subs={varA:varB})

        self.assertEqual(res, h.substitute({varA:varB}))

        res = substitute(h, subs={varA:Int(1)})
        self.assertEqual(res, h.substitute({varA:Int(1)}))

    def test_substituter_conditions(self):
        x = Symbol("x")
        y = Symbol("y")
        and_x_x = And(x, x)
        ftype = FunctionType(BOOL, [BOOL])
        f = Symbol("f", ftype)

        # 1. All arguments must be terms
        args_good = {x:y}
        args_bad = {x:f}

        substitute(and_x_x, args_good)
        with self.assertRaisesRegex(TypeError, " substitutions"):
            substitute(and_x_x, args_bad)

        # 2. All arguments belong to the manager of the substituter.
        new_mgr = FormulaManager(get_env())
        new_x = new_mgr.Symbol("x")
        self.assertNotEqual(x, new_x)
        args_1 = {x: new_x}
        args_2 = {new_x: new_x}

        with self.assertRaisesRegex(TypeError, "Formula Manager" ):
            substitute(and_x_x, args_1)

        with self.assertRaisesRegex(TypeError, "Formula Manager."):
            substitute(and_x_x, args_2)

        with self.assertRaisesRegex(TypeError, "substitute()"):
            substitute(f, {x:x})

    def test_undefined_node(self):
        varA = Symbol("At", INT)

        dag_walker = DagWalker()
        with self.assertRaises(UnsupportedOperatorError):
            dag_walker.walk(varA)

        tree_walker = TreeWalker()
        with self.assertRaises(UnsupportedOperatorError):
            tree_walker.walk(varA)


    def test_walker_is_complete(self):
        op.ALL_TYPES.append(-1)
        with self.assertRaises(AssertionError):
            TreeWalker()
        op.ALL_TYPES.remove(-1)

    def test_identity_walker_simple(self):

        def walk_and_to_or(formula, args, **kwargs):
            return Or(args)

        def walk_or_to_and(formula, args, **kwargs):
            return And(args)

        walker = IdentityDagWalker(env=get_env())

        walker.set_function(walk_and_to_or, op.AND)
        walker.set_function(walk_or_to_and, op.OR)

        x, y, z = Symbol('x'), Symbol('y'), Symbol('z')

        cnf = And(Or(x,y,z), Or(z, Not(y)))
        fake_dnf = Or(And(x,y,z), And(z, Not(y)))
        result = walker.walk(cnf)
        self.assertEqual(result, fake_dnf)

        alternation = Or(cnf, Not(cnf))
        expected = And(fake_dnf, Not(fake_dnf))
        result = walker.walk(alternation)
        self.assertEqual(result, expected)

    def test_identity_dag_walker(self):
        idw = IdentityDagWalker()
        for (f, _, _, _) in get_example_formulae():
            rebuilt = idw.walk(f)
            self.assertTrue(rebuilt == f, "Rebuilt formula is not identical")

    def test_substitution_on_quantifiers(self):
        x, y = FreshSymbol(), FreshSymbol()

        # y /\ Forall x. x /\ y.
        f = And(y, ForAll([x], And(x, y)))

        subs = {y: Bool(True)}
        f_subs = substitute(f, subs).simplify()
        self.assertEqual(f_subs, ForAll([x], x))

        subs = {x: Bool(True)}
        f_subs = substitute(f, subs).simplify()
        self.assertEqual(f_subs, f)

    def test_substitution_complex(self):
        x, y = FreshSymbol(REAL), FreshSymbol(REAL)

        # y = 0 /\ (Forall x. x > 3 /\ y < 2)
        f = And(Equals(y, Real(0)),
                ForAll([x], And(GT(x, Real(3)), LT(y, Real(2)))))

        if "MSS" in str(self.env.SubstituterClass):
            subs = {y: Real(0),
                    ForAll([x], And(GT(x, Real(3)), LT(Real(0), Real(2)))): TRUE()}
        else:
            assert "MGS" in str(self.env.SubstituterClass)
            subs = {y: Real(0),
                    ForAll([x], And(GT(x, Real(3)), LT(y, Real(2)))): TRUE()}
        f_subs = substitute(f, subs).simplify()
        self.assertEqual(f_subs, TRUE())


    def test_substitution_term(self):
        x, y = FreshSymbol(REAL), FreshSymbol(REAL)

        # y = 0 /\ Forall x. x > 3
        f = And(Equals(y, Real(0)), ForAll([x], GT(x, Real(3))))

        subs = {GT(x, Real(3)): TRUE()}
        f_subs = substitute(f, subs)
        # Since 'x' is quantified, we cannot replace the term
        # therefore the substitution does not yield any result.
        self.assertEqual(f_subs, f)


    def test_substitution_on_functions(self):
        i, r = FreshSymbol(INT), FreshSymbol(REAL)
        f = Symbol("f", FunctionType(BOOL, [INT, REAL]))

        phi = Function(f, [Plus(i, Int(1)), Minus(r, Real(2))])

        phi_sub = substitute(phi, {i: Int(0)}).simplify()
        self.assertEqual(phi_sub, Function(f, [Int(1), Minus(r, Real(2))]))

        phi_sub = substitute(phi, {r: Real(0)}).simplify()
        self.assertEqual(phi_sub, Function(f, [Plus(i, Int(1)), Real(-2)]))

        phi_sub = substitute(phi, {r: Real(0), i: Int(0)}).simplify()
        self.assertEqual(phi_sub, Function(f, [Int(1), Real(-2)]))


    def test_iterative_get_free_variables(self):
        f = Symbol("x")
        for _ in xrange(1000):
            f = And(f, f)

        cone = f.get_free_variables()
        self.assertEqual(cone, set([Symbol("x")]))


if __name__ == '__main__':
    main()
