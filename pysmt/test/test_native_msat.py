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
from io import StringIO

from pysmt.environment import push_env, pop_env, get_env
from pysmt.exceptions import PysmtTypeError
from pysmt.shortcuts import (Symbol, And, Or, Not, Implies, Iff, Ite, LT, LE,
                             GT, Equals, Plus, Times, Div, ToReal, Int, Real,
                             BV, BVAdd, BVExtract, BVZExt, BVULT, Select,
                             Store, Function, ForAll, String, TRUE, Solver,
                             is_sat, is_valid, get_model, binary_interpolant)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.test import TestCase, main, skipIfSolverNotAvailable
from pysmt.typing import INT, REAL, BOOL, BVType, ArrayType, FunctionType


class TestNativeMSat(TestCase):

    def setUp(self):
        from pysmt.native import NativeEnvironment
        # Build first: if it raises, the environment stack is left intact
        env = NativeEnvironment("msat")
        pop_env()
        push_env(env)
        self.env = get_env()
        self.x, self.y = Symbol("x"), Symbol("y")
        self.i, self.j = Symbol("i", INT), Symbol("j", INT)
        self.r = Symbol("r", REAL)

    def assertEquivalent(self, a, b):
        self.assertTrue(is_valid(Iff(a, b), solver_name="msat"))

    @skipIfSolverNotAvailable("msat")
    def test_identity(self):
        import mathsat # type: ignore[import]
        f = And(self.x, self.y)
        self.assertIs(f, And(self.x, self.y))
        self.assertIs(f, And([self.x, self.y]))
        self.assertEqual(f.node_id(), 2 * mathsat.msat_term_id(f._term))
        self.assertIn(f, self.env.formula_manager)

    @skipIfSolverNotAvailable("msat")
    def test_mathsat_shape(self):
        # LT is reported as MathSAT builds it: not (j <= i)
        f = LT(self.i, self.j)
        self.assertTrue(f.is_not())
        self.assertTrue(f.arg(0).is_le())
        self.assertEqual(f.arg(0).args(), (self.j, self.i))
        self.assertIs(And(TRUE(), self.x), self.x)

    @skipIfSolverNotAvailable("msat")
    def test_trivial_conversion(self):
        f = And(self.x, LT(self.i, self.j))
        with Solver(name="msat") as s:
            self.assertIs(s.converter.convert(f), f._term)
            s.add_assertion(f)
            self.assertTrue(s.solve())
            self.assertIs(s.get_value(self.x), TRUE())

    @skipIfSolverNotAvailable("msat")
    def test_model(self):
        f = And(GT(self.i, Int(3)), LT(self.i, self.j))
        model = get_model(f, solver_name="msat")
        vi, vj = model[self.i], model[self.j]
        self.assertIn(vi, self.env.formula_manager)
        self.assertTrue(vi.is_int_constant())
        self.assertGreater(vj.constant_value(), vi.constant_value())

    @skipIfSolverNotAvailable("msat")
    def test_two_solvers_do_not_interfere(self):
        with Solver(name="msat") as s1, Solver(name="msat") as s2:
            s1.add_assertion(self.x)
            s2.add_assertion(Not(self.x))
            self.assertTrue(s1.solve())
            self.assertTrue(s2.solve())

    @skipIfSolverNotAvailable("msat")
    def test_uf(self):
        f = Symbol("f", FunctionType(INT, [INT]))
        app = Function(f, [self.i])
        self.assertTrue(app.is_function_application())
        self.assertIs(app.function_name(), f)
        self.assertEqual(f.symbol_type(), FunctionType(INT, [INT]))
        self.assertEqual(app.get_type(), INT)
        self.assertTrue(is_valid(Implies(Equals(self.i, self.j),
                                         Equals(app, Function(f, [self.j]))),
                                 solver_name="msat"))

    @skipIfSolverNotAvailable("msat")
    def test_type_errors(self):
        with self.assertRaises(PysmtTypeError):
            Plus(self.i, self.x)
        b8, b4 = Symbol("b8", BVType(8)), Symbol("b4", BVType(4))
        with self.assertRaises(PysmtTypeError):
            BVAdd(b8, b4)

    @skipIfSolverNotAvailable("msat")
    def test_int_real_are_strict(self):
        # pysmt typing: Int is not accepted where Real is expected
        with self.assertRaises(PysmtTypeError):
            Plus(self.r, self.i)
        with self.assertRaises(PysmtTypeError):
            Equals(self.r, Int(0))

    @skipIfSolverNotAvailable("msat")
    def test_toreal_is_a_real_view(self):
        # MathSAT folds ToReal(i) into i: same term, different node
        ti = ToReal(self.i)
        self.assertIsNot(ti, self.i)
        self.assertIs(ti._term, self.i._term)
        self.assertTrue(ti.is_toreal())
        self.assertIs(ti.arg(0), self.i)
        self.assertEqual(ti.get_type(), REAL)
        self.assertIs(ti, ToReal(self.i))
        self.assertIsNot(Real(0), Int(0))
        self.assertTrue(Real(0).is_real_constant(0))
        self.assertTrue(Int(0).is_int_constant(0))
        f = Plus(self.r, ti)
        self.assertEqual(f.get_type(), REAL)
        self.assertTrue(is_valid(Equals(f, Plus(ti, self.r)), solver_name="msat"))

    @skipIfSolverNotAvailable("msat")
    def test_decoded_terms_are_well_typed(self):
        # MathSAT builds (+_rat i r): decoding restores ToReal(i)
        f = Plus(self.r, ToReal(self.i))
        self.assertIn(ToReal(self.i), f.args())
        # MathSAT passes i to the Real UF as it is: decoding restores ToReal(i)
        h = Symbol("h", FunctionType(REAL, [REAL]))
        app = Function(h, [ToReal(self.i)])
        self.assertIs(app.arg(0), ToReal(self.i))
        a = Symbol("a", ArrayType(INT, REAL))
        st = Store(a, self.i, Real(1))
        self.assertIs(st.arg(2), Real(1))
        # A plain pysmt walk agrees with the seeded types
        from pysmt.type_checker import SimpleTypeChecker
        stc = SimpleTypeChecker(self.env)
        for g in (f, app, st, LE(Real(0), self.r)):
            self.assertEqual(stc.get_type(g), g.get_type())

    @skipIfSolverNotAvailable("msat")
    @skipIfSolverNotAvailable("z3")
    def test_other_solvers_accept_native_nodes(self):
        f = And(GT(Plus(self.r, ToReal(self.i)), Real(0)), LT(self.i, Int(2)))
        self.assertTrue(is_sat(f, solver_name="z3"))

    @skipIfSolverNotAvailable("msat")
    def test_unsupported(self):
        with self.assertRaises(NotImplementedError):
            ForAll([self.x], self.x)
        with self.assertRaises(NotImplementedError):
            String("abc")
        with self.assertRaises(NotImplementedError):
            Symbol("g", FunctionType(INT, [BOOL]))

    @skipIfSolverNotAvailable("msat")
    def test_theories(self):
        self.assertEquivalent(Ite(self.x, self.y, Not(self.y)), Iff(self.x, self.y))
        self.assertTrue(is_valid(LE(Times(Div(self.i, Int(2)), Int(2)), self.i),
                                 solver_name="msat"))
        b = Symbol("b", BVType(8))
        e = BVExtract(BVAdd(b, BV(3, 8)), 0, 3)
        self.assertEqual(e.bv_width(), 4)
        self.assertEqual(BVZExt(b, 4).bv_width(), 12)
        self.assertTrue(is_sat(BVULT(b, BV(3, 8)), solver_name="msat"))
        a = Symbol("a", ArrayType(INT, INT))
        self.assertTrue(is_valid(Equals(Select(Store(a, self.i, self.j), self.i),
                                        self.j),
                                 solver_name="msat"))

    @skipIfSolverNotAvailable("msat")
    def test_fnode_api_is_equivalent(self):
        f = And(Or(self.x, self.y), LT(self.i, self.j), GT(self.r, Real(1)))
        self.assertEqual(f.get_free_variables(),
                         frozenset([self.x, self.y, self.i, self.j, self.r]))
        self.assertEquivalent(f, f.simplify())
        g = f.substitute({self.i: Int(1), self.x: TRUE()})
        self.assertEquivalent(g, And(LT(Int(1), self.j), GT(self.r, Real(1))))
        # Serialize to SMT-LIB and parse back into the native environment
        buf = StringIO()
        smtlibscript_from_formula(f).serialize(buf)
        parsed = SmtLibParser().get_script(StringIO(buf.getvalue())).get_last_formula()
        self.assertEquivalent(f, parsed)

    @skipIfSolverNotAvailable("msat")
    def test_interpolation(self):
        a = And(LT(self.i, self.j), LT(self.j, Int(0)))
        b = GT(self.i, Int(5))
        itp = binary_interpolant(a, b, solver_name="msat")
        self.assertIn(itp, self.env.formula_manager)
        self.assertTrue(is_valid(Implies(a, itp), solver_name="msat"))
        self.assertFalse(is_sat(And(itp, b), solver_name="msat"))


if __name__ == "__main__":
    main()
