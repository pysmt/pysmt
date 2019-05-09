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
from six.moves import xrange
from six.moves import cStringIO

import pysmt.logics as logics
import pysmt.smtlib.commands as smtcmd
from pysmt.shortcuts import (Real, Plus, Symbol, Equals, And, Bool, Or, Not,
                             Div, LT, LE, Int, ToReal, Iff, Exists, Times, FALSE,
                             BVLShr, BVLShl, BVAShr, BV, BVAdd, BVULT, BVMul,
                             Select, Array, Ite, String)
from pysmt.shortcuts import Solver, get_env, qelim, get_model, TRUE, ExactlyOne
from pysmt.typing import REAL, BOOL, INT, BVType, FunctionType, ArrayType
from pysmt.test import (TestCase, skipIfSolverNotAvailable, skipIfNoSolverForLogic,
                        skipIfNoQEForLogic)
from pysmt.test import main
from pysmt.exceptions import ConvertExpressionError, PysmtValueError, PysmtTypeError
from pysmt.test.examples import get_example_formulae
from pysmt.environment import Environment
from pysmt.rewritings import cnf_as_set
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.commands import DECLARE_FUN
from pysmt.smtlib.script import SmtLibCommand
from pysmt.logics import get_closer_smtlib_logic
from pysmt.constants import Fraction


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

    @skipIfNoSolverForLogic(logics.QF_UFLIRA)
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

        for name in get_env().factory.all_solvers(logic=logics.QF_BOOL):
            self.assertSat(f_and_one, solver_name=name)
            self.assertSat(f_or_one, solver_name=name)
            self.assertSat(f_and_many, solver_name=name)
            self.assertSat(f_or_many, solver_name=name)

        for name in get_env().factory.all_solvers(logic=logics.QF_UFLIRA):
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

    @skipIfNoQEForLogic(logics.LIA)
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
            self.assertTrue("%2" in str(ex.expression) or \
                            "int_mod_congr" in str(ex.expression))

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

        self.assertEqual(f1, f2)

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
                    self.assertEqual(nf, l_test[i])

    def test_is_one(self):
        self.assertTrue(Int(1).is_one())
        self.assertTrue(Real(1).is_one())
        self.assertTrue(Int(0).is_zero())
        self.assertTrue(Real(0).is_zero())

    def test_cnf_as_set(self):
        r = cnf_as_set(Symbol("x"))
        self.assertTrue(type(r) == frozenset)

    def test_substitute_to_real(self):
        p = Symbol("p", INT)
        f = LT(ToReal(p), Real(0))

        new_f = f.substitute({p: Real(1)}).simplify()
        self.assertEqual(new_f, Bool(False))

    def test_empty_string_symbol(self):
        with self.assertRaises(PysmtValueError):
            Symbol("")

    def test_smtlib_info_quoting(self):
        cmd = SmtLibCommand(smtcmd.SET_INFO, [":source", "This\nis\nmultiline!"])
        output = cmd.serialize_to_string()
        self.assertEqual(output, "(set-info :source |This\nis\nmultiline!|)")

    def test_parse_define_fun(self):
        smtlib_input = "(declare-fun z () Bool)"\
                       "(define-fun .def_1 ((z Bool)) Bool (and z z))"
        parser = SmtLibParser()
        buffer_ = cStringIO(smtlib_input)
        parser.get_script(buffer_)

    def test_parse_define_fun_bind(self):
        smtlib_input = "(declare-fun y () Bool)"\
                       "(define-fun .def_1 ((z Bool)) Bool (and z z))"
        parser = SmtLibParser()
        buffer_ = cStringIO(smtlib_input)
        parser.get_script(buffer_)

    def test_parse_bvx_var(self):
        """bvX is a valid identifier."""
        smtlib_input = """
        (declare-fun bv1 () (_ BitVec 8))
        (assert (bvult (_ bv0 8) (bvmul (bvadd bv1 (_ bv1 8)) (_ bv5 8))))
        (check-sat)"""
        parser = SmtLibParser()
        buffer_ = cStringIO(smtlib_input)
        script = parser.get_script(buffer_)
        # Check Parsed result
        iscript = iter(script)
        cmd = next(iscript)
        self.assertEqual(cmd.name, DECLARE_FUN)
        bv1 = cmd.args[0]
        self.assertEqual(bv1.symbol_type().width, 8)
        cmd = next(iscript)
        parsed_f = cmd.args[0]
        target_f = BVULT(BV(0, 8),
                         BVMul(BVAdd(bv1, BV(1, 8)), BV(5, 8)))
        self.assertEqual(parsed_f, target_f)


    def test_simplify_times(self):
        a,b = Real(5), Real((1,5))
        f = Times(a,b).simplify()
        self.assertEqual(f.constant_value(), 1)

    @skipIfSolverNotAvailable("yices")
    def test_yices_push(self):
        with Solver(name="yices") as solver:
            solver.add_assertion(FALSE())
            res = solver.solve()
            self.assertFalse(res)
            solver.push()
            solver.add_assertion(TRUE())
            res = solver.solve()
            self.assertFalse(res)
            solver.pop()

    def test_qf_bool_smt2(self):
        # QF_BOOL does not exist in SMT-LIB
        # This test is to enforce the consistent choice of QF_UF
        close_l = get_closer_smtlib_logic(logics.QF_BOOL)
        self.assertEqual(close_l, logics.QF_UF)
        # For BOOL we use LRA
        close_l = get_closer_smtlib_logic(logics.BOOL)
        self.assertEqual(close_l, logics.LRA)

    def test_exactly_one_unpacking(self):
        s1,s2 = Symbol("x"), Symbol("y")
        f1 = ExactlyOne((s for s in [s1,s2]))
        f2 = ExactlyOne([s1,s2])
        f3 = ExactlyOne(s1,s2)

        self.assertEqual(f1,f2)
        self.assertEqual(f2,f3)

    @skipIfSolverNotAvailable("btor")
    def test_btor_bitwidth_bug_in_shift(self):
        # (384, 384, 9)
        # (x69 >> 1_384)
        s = Solver(name="btor")
        x69 = Symbol("x69", BVType(384))
        # BVLShr
        f = BVLShr(x69, BV(1, 384))
        c = s.converter.convert(f)
        self.assertIsNotNone(c)
        # BVLShl
        f = BVLShl(x69, BV(1, 384))
        c = s.converter.convert(f)
        self.assertIsNotNone(c)
        # BVAShr
        f = BVAShr(x69, BV(1, 384))
        c = s.converter.convert(f)
        self.assertIsNotNone(c)

    @skipIfSolverNotAvailable("btor")
    def test_btor_get_non_bool_value(self):
        with Solver(name="btor") as s:
            x = Symbol("x", BVType(16))
            s.add_assertion(Equals(x, BV(1, 16)))
            self.assertTrue(s.solve())
            self.assertEqual(s.get_value(Equals(x, BV(1, 16))), TRUE())
            self.assertEqual(s.get_value(BVAdd(x, BV(1, 16))), BV(2, 16))

    @skipIfSolverNotAvailable("btor")
    def test_btor_get_array_element(self):
        with Solver(name="btor") as s:
            x = Symbol("a", ArrayType(BVType(16), BVType(16)))
            s.add_assertion(Equals(Select(x, BV(1, 16)), BV(1, 16)))
            s.add_assertion(Equals(Select(x, BV(2, 16)), BV(3, 16)))
            self.assertTrue(s.solve())
            self.assertEqual(s.get_value(Select(x, BV(1, 16))), BV(1, 16))
            self.assertIsNotNone(s.get_value(x))


    def test_smtlib_define_fun_serialization(self):
        smtlib_input = "(define-fun init ((x Bool)) Bool (and x (and x (and x (and x (and x (and x x)))))))"
        parser = SmtLibParser()
        buffer_ = cStringIO(smtlib_input)
        s = parser.get_script(buffer_)
        for c in s:
            res = c.serialize_to_string(daggify=False)
        self.assertEqual(res.replace('__x0', 'x'), smtlib_input)

    @skipIfSolverNotAvailable("z3")
    def test_z3_nary_back(self):
        from z3 import Tactic
        r = Symbol("r", REAL)
        s = Symbol("s", REAL)
        t = Symbol("t", REAL)
        f = Equals(Times(r,s,t), Real(0))

        with Solver(name="z3") as solver:
            z3_f = solver.converter.convert(f)
            z3_f = Tactic('simplify', solver.z3.ctx)(z3_f).as_expr()
            fp = solver.converter.back(z3_f)
            self.assertValid(Iff(f, fp), (f, fp))

    def test_array_initialization_printing(self):
        self.assertEqual(str(Array(INT, Int(0), {Int(1):Int(2)})), "Array{Int, Int}(0)[1 := 2]")

    @skipIfSolverNotAvailable("btor")
    def test_boolector_assumptions(self):
        with Solver(name='btor') as solver:
            x = Symbol('x')
            y = Symbol('y')
            solver.add_assertion(Or(x, y))
            solver.solve([Not(x), Not(y)])
            btor_notx = solver.converter.convert(Not(x))
            btor_noty = solver.converter.convert(Not(y))
            self.assertEqual(solver.btor.Failed(btor_notx, btor_noty),
                             [True, True])

    def test_parse_declare_const(self):
        smtlib_input = """
        (declare-const s Int)
        (check-sat)"""
        parser = SmtLibParser()
        buffer_ = cStringIO(smtlib_input)
        script = parser.get_script(buffer_)
        self.assertIsNotNone(script)

    @skipIfSolverNotAvailable("z3")
    def test_z3_conversion_ite(self):
        with Solver(name='z3') as solver:
            x = Symbol('x')
            y = Symbol('y')
            f = Ite(x, y, FALSE())
            solver.add_assertion(f)
            self.assertTrue(solver.solve())

    def test_parse_exception(self):
        from pysmt.exceptions import PysmtSyntaxError
        smtlib_input = "(declare-const x x x Int)" +\
                       "(check-sat)"
        parser = SmtLibParser()
        buffer_ = cStringIO(smtlib_input)
        try:
            parser.get_script(buffer_)
            self.assertFalse(True)
        except PysmtSyntaxError as ex:
            self.assertEqual(ex.pos_info[0], 0)
            self.assertEqual(ex.pos_info[1], 19)

    def test_parse_bvconst_width(self):
        smtlib_input = "(assert (> #x10 #x10))"
        parser = SmtLibParser()
        buffer_ = cStringIO(smtlib_input)
        expr = parser.get_script(buffer_).get_last_formula()
        const = expr.args()[0]
        self.assertEqual(const.bv_width(), 8, const.bv_width())

    def test_equality_typing(self):
        x = Symbol('x', BOOL)
        y = Symbol('y', BOOL)
        with self.assertRaises(PysmtTypeError):
            Equals(x, y)
        with self.assertRaises(PysmtTypeError):
            LE(x, y)

    def test_string_constant_quote_escaping_hr_printer(self):
        x = String('a"b')
        y = String('""')
        z = String('"')
        self.assertEqual('"a""b"', str(x))
        self.assertEqual('""""""', str(y))
        self.assertEqual('""""', str(z))

    def test_string_constant_quote_escaping_smtlib_printer(self):
        x = String('a"b')
        y = String('""')
        z = String('"')
        self.assertEqual('"a""b"', x.to_smtlib())
        self.assertEqual('""""""', y.to_smtlib())
        self.assertEqual('""""', z.to_smtlib())

    def test_string_constant_quote_escaping_parsing(self):
        script = """
        (declare-const x String)
        (assert (= x "a""b"))
        (assert (= x "\"\""))
        (assert (= x "\"\"\"\""))
        """

        p = SmtLibParser()
        buffer = cStringIO(script)
        s = p.get_script(buffer)
        self.assertEqual('a"b', s.commands[1].args[0].arg(1).constant_value())
        self.assertEqual('"', s.commands[2].args[0].arg(1).constant_value())
        self.assertEqual('""', s.commands[3].args[0].arg(1).constant_value())

    def test_pysmt_syntax_error(self):
        from pysmt.exceptions import PysmtSyntaxError
        try:
            raise PysmtSyntaxError("'define-fun' expected", (5,5))
        except PysmtSyntaxError as ex:
            self.assertEqual(str(ex), "Line 5, Col 5: 'define-fun' expected")


if __name__ == "__main__":
    main()
