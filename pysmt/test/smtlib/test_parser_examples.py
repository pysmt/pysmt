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
import os
from tempfile import mkstemp

from io import StringIO

import pysmt.logics as logics
from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.test.examples import get_example_formulae
from pysmt.smtlib.parser import SmtLibParser, Tokenizer
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.shortcuts import Iff, Symbol, And, Implies, Xor, LT, GE, Equals, \
    Plus, Minus, Times, Div, AllDifferent, BVXor, BVConcat
from pysmt.shortcuts import read_smtlib, write_smtlib, get_env
from pysmt.exceptions import PysmtSyntaxError
from pysmt.smtlib.commands import ASSERT
from pysmt.typing import INT, REAL, BV8


class TestSMTParseExamples(TestCase):

    def test_parse_examples(self):
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic == logics.QF_BV:
                # See test_parse_examples_bv
                continue
            buf = StringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf)

            buf.seek(0)
            parser = SmtLibParser()
            script_in = parser.get_script(buf)
            f_in = script_in.get_last_formula()
            self.assertEqual(f_in.simplify(), f_out.simplify())

    @skipIfNoSolverForLogic(logics.QF_BV)
    def test_parse_examples_bv(self):
        """For BV we represent a superset of the operators defined in SMT-LIB.

        We verify the correctness of the serialization process by
        checking the equivalence of the original and serialized
        expression.
        """
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic != logics.QF_BV:
                continue
            buf_out = StringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out)

            buf_in = StringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            f_in = script_in.get_last_formula()

            self.assertValid(Iff(f_in, f_out))

    def test_parse_examples_daggified(self):
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic == logics.QF_BV:
                # See test_parse_examples_daggified_bv
                continue
            buf_out = StringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out, daggify=True)
            buf_in = StringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            f_in = script_in.get_last_formula()
            self.assertEqual(f_in.simplify(), f_out.simplify())

    @skipIfNoSolverForLogic(logics.QF_BV)
    def test_parse_examples_daggified_bv(self):
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            if logic != logics.QF_BV:
                # See test_parse_examples_daggified
                continue
            buf_out = StringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out, daggify=True)
            buf_in = StringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            f_in = script_in.get_last_formula()
            self.assertValid(Iff(f_in, f_out), f_in.serialize())

    def test_dumped_logic(self):
        # Dumped logic matches the logic in the example.
        #
        # There are a few cases where we use a logic
        # that does not exist in SMT-LIB, and the SMT-LIB
        # serialization logic will find a logic that
        # is more expressive. We need to adjust the test
        # for those cases (see rewrite dict below).
        rewrite = {
            logics.QF_BOOL: logics.QF_UF,
            logics.BOOL: logics.LRA,
            logics.QF_NIRA: logics.AUFNIRA,
            logics.QF_LIRA: logics.QF_UFLIRA,
        }
        fs = get_example_formulae()

        for (f_out, _, _, logic) in fs:
            buf_out = StringIO()
            script_out = smtlibscript_from_formula(f_out)
            script_out.serialize(outstream=buf_out)
            buf_in = StringIO(buf_out.getvalue())
            parser = SmtLibParser()
            script_in = parser.get_script(buf_in)
            for cmd in script_in:
                if cmd.name == "set-logic":
                    logic_in = cmd.args[0]
                    self.assertEqual(logic_in, rewrite.get(logic, logic))
                    break
            else:  # Loops exited normally
                print("-"*40)
                print(script_in)

    def test_read_and_write_shortcuts(self):
        fs = get_example_formulae()

        fdi, tmp_fname = mkstemp()
        os.close(fdi)  # Close initial file descriptor
        for (f_out, _, _, _) in fs:
            write_smtlib(f_out, tmp_fname)
            # with open(tmp_fname) as fin:
            #     print(fin.read())

            f_in = read_smtlib(tmp_fname)
            self.assertEqual(f_out.simplify(), f_in.simplify())
        # Clean-up
        os.remove(tmp_fname)

    def test_incomplete_stream(self):
        txt = """
        (declare-fun A () Bool)
        (declare-fun B () Bool)
        (assert (and A
        """
        parser = SmtLibParser()
        with self.assertRaises(PysmtSyntaxError):
            parser.get_script(StringIO(txt))

    def test_parse_consume(self):
        smt_script = """
        (model
        (define-fun STRING_cmd_line_arg_1_1000 () String "AAAAAAAAAAAA")
        )
        """
        tokens = Tokenizer(StringIO(smt_script), interactive=True)
        parser = SmtLibParser()
        tokens.consume()
        tokens.consume()
        next_token = tokens.consume()
        tokens.add_extra_token(next_token)
        tokens.consume()

    def test_parser_params(self):
        txt = """
        (define-fun x ((y Int)) Bool (> y 0))
        (declare-fun z () Int)
        (declare-fun y () Bool)
        (assert (and y (x z)))
        """
        parser = SmtLibParser()
        script = parser.get_script(StringIO(txt))
        self.assertEqual(len(get_env().formula_manager.get_all_symbols()),
                         len(script.get_declared_symbols()) + len(script.get_define_fun_parameter_symbols()))

    @skipIfNoSolverForLogic(logics.QF_ABV)
    def test_nary_bvconcat(self):
        txt = """
        (set-logic QF_BV )
        (declare-fun INPUT () (Array (_ BitVec 32) (_ BitVec 8) ) )
        (declare-fun A () (_ BitVec 64))(assert (= A (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) (select INPUT #x00000000))) #x0000000000000000))))
        (declare-fun B () (_ BitVec 64))(assert (= B (concat ((_ extract 63 56) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) (select INPUT #x00000000))) #x0000000000000000))))) #x0000000000000000))) ((_ extract 55 48) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) (select INPUT #x00000000))) #x0000000000000000))))) #x0000000000000000))) ((_ extract 47 40) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) (select INPUT #x00000000))) #x0000000000000000))))) #x0000000000000000))) ((_ extract 39 32) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) (select INPUT #x00000000))) #x0000000000000000))))) #x0000000000000000))) ((_ extract 31 24) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) (select INPUT #x00000000))) #x0000000000000000))))) #x0000000000000000))) ((_ extract 23 16) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) (select INPUT #x00000000))) #x0000000000000000))))) #x0000000000000000))) ((_ extract 15 8) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) (select INPUT #x00000000))) #x0000000000000000))))) #x0000000000000000))) ((_ extract 7 0) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) ((_ extract 7 0) (bvor #x0000000000000000 (bvshl ((_ zero_extend 32) ((_ zero_extend 24) (select INPUT #x00000000))) #x0000000000000000))))) #x0000000000000000))))))
        (assert (=  A B))
        (check-sat)"""
        parser = SmtLibParser()
        script = parser.get_script(StringIO(txt))
        f_in = script.get_last_formula()
        self.assertSat(f_in)

    def test_int_promotion_define_fun(self):
        script = """
        (define-fun x () Int 8)
        (define-fun y () Real 8)
        """
        p = SmtLibParser()
        buffer = StringIO(script)
        s = p.get_script(buffer)

        get_type = get_env().stc.get_type
        for cmd in s:
            self.assertEqual(cmd.args[2], get_type(cmd.args[3]))

    def test_nary_operators(self):
        """All the SMT-LIB n-ary operators are expanded as the standard
        prescribes: see https://github.com/pysmt/pysmt/issues/638"""
        INT_DECLS = "(declare-fun a () Int)(declare-fun b () Int)" \
                    "(declare-fun c () Int)(declare-fun d () Int)"
        BOOL_DECLS = "(declare-fun p () Bool)(declare-fun q () Bool)" \
                     "(declare-fun r () Bool)"
        BV_DECLS = "(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))" \
                   "(declare-fun z () (_ BitVec 8))"

        # (declarations, n-ary application, expected expansion)
        cases = [
            # :right-assoc
            (BOOL_DECLS, "(=> p q r)", "(=> p (=> q r))"),
            (BOOL_DECLS, "(=> p q r p)", "(=> p (=> q (=> r p)))"),
            # :left-assoc
            (BOOL_DECLS, "(xor p q r)", "(xor (xor p q) r)"),
            (BOOL_DECLS, "(<-> p q r)", "(<-> (<-> p q) r)"),
            (INT_DECLS, "(- a b c)", "(- (- a b) c)"),
            (INT_DECLS, "(- a b c d)", "(- (- (- a b) c) d)"),
            (INT_DECLS, "(/ a b c)", "(/ (/ a b) c)"),
            (INT_DECLS, "(div a b c)", "(div (div a b) c)"),
            (BV_DECLS, "(bvxor x y z)", "(bvxor (bvxor x y) z)"),
            (BV_DECLS, "(bvxnor x y z)", "(bvxnor (bvxnor x y) z)"),
            # :chainable
            (INT_DECLS, "(> a b c)", "(and (> a b) (> b c))"),
            (INT_DECLS, "(>= a b c d)", "(and (>= a b) (>= b c) (>= c d))"),
            (INT_DECLS, "(< a b c)", "(and (< a b) (< b c))"),
            (INT_DECLS, "(<= a b c)", "(and (<= a b) (<= b c))"),
            (INT_DECLS, "(= a b c)", "(and (= a b) (= b c))"),
            (BOOL_DECLS, "(= p q r)", "(and (<-> p q) (<-> q r))"),
            # unary applications: identity for the associative operators,
            # vacuously true for the chainable ones
            (BOOL_DECLS, "(=> p)", "p"),
            (BOOL_DECLS, "(xor p)", "p"),
            (INT_DECLS, "(/ a)", "a"),
            (INT_DECLS, "(= a)", "true"),
            (INT_DECLS, "(< a)", "true"),
        ]
        for decls, nary, expected in cases:
            self.assertEqual(self._parse_assertion(decls, nary),
                             self._parse_assertion(decls, expected),
                             "wrong expansion of %s" % nary)

    def test_nary_operators_end_to_end(self):
        """Parse a whole SMT-LIB2 script using the n-ary operators and check
        the resulting formulae against the ones built with the pySMT API"""
        script = """
        ; no set-logic: no pySMT logic covers BV + non-linear Int/Real at once
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Int)
        (declare-fun r () Real)
        (declare-fun s () Real)
        (declare-fun t () Real)
        (declare-fun p () Bool)
        (declare-fun q () Bool)
        (declare-fun u () Bool)
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (declare-fun z () (_ BitVec 8))
        (assert (< a b c))
        (assert (>= a b c))
        (assert (= a b c))
        (assert (= p q u))
        (assert (= (- a b c) (+ a b c)))
        (assert (= (div a b c) (* a b c)))
        (assert (= (/ r s t) r))
        (assert (=> p q u))
        (assert (xor p q u))
        (assert (distinct a b c))
        (assert (= (bvxor x y z) x))
        (assert (= (concat x y z) (concat z y x)))
        (check-sat)
        """
        a, b, c = (Symbol(name, INT) for name in "abc")
        r, s, t = (Symbol(name, REAL) for name in "rst")
        p, q, u = (Symbol(name) for name in "pqu")
        x, y, z = (Symbol(name, BV8) for name in "xyz")

        expected = [
            # :chainable
            And(LT(a, b), LT(b, c)),
            And(GE(a, b), GE(b, c)),
            And(Equals(a, b), Equals(b, c)),
            And(Iff(p, q), Iff(q, u)),
            # :left-assoc ('+' and '*' stay flat n-ary)
            Equals(Minus(Minus(a, b), c), Plus(a, b, c)),
            Equals(Div(Div(a, b), c), Times(a, b, c)),
            Equals(Div(Div(r, s), t), r),
            # :right-assoc
            Implies(p, Implies(q, u)),
            # :left-assoc
            Xor(Xor(p, q), u),
            # :pairwise
            AllDifferent(a, b, c),
            # bit-vectors
            Equals(BVXor(BVXor(x, y), z), x),
            Equals(BVConcat(x, y, z), BVConcat(z, y, x)),
        ]

        parser = SmtLibParser()
        parsed = [cmd.args[0] for cmd in
                  parser.get_script(StringIO(script)).filter_by_command_name(ASSERT)]

        self.assertEqual(len(parsed), len(expected))
        for got, exp in zip(parsed, expected):
            self.assertEqual(got, exp)
        # ...and the conjunction of all of them is what the script means
        self.assertEqual(
            SmtLibParser().get_script(StringIO(script)).get_last_formula(),
            And(expected))

    def test_nary_div_is_integer_division(self):
        """'div' is the Ints division, so it must not be promoted to Real"""
        f = self._parse_assertion("(declare-fun a () Int)", "(div a 2 3)")
        self.assertEqual(get_env().stc.get_type(f), INT)

    @staticmethod
    def _parse_assertion(declarations, expression):
        script = "%s (assert %s)" % (declarations, expression)
        parser = SmtLibParser()
        return parser.get_script(StringIO(script)).get_last_formula()

    def test_typing_define_fun(self):
        script = """
        (define-fun x () Int 8.2)
        """
        p = SmtLibParser()
        buffer = StringIO(script)
        with self.assertRaises(PysmtSyntaxError):
            p.get_script(buffer)


if __name__ == "__main__":
    main()
