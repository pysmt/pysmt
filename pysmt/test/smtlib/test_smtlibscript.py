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
from six.moves import cStringIO

import pysmt.smtlib.commands as smtcmd
from pysmt.shortcuts import And, Or, Symbol, GT, Real, Not
from pysmt.typing import REAL
from pysmt.test import TestCase, main
from pysmt.smtlib.script import SmtLibScript, SmtLibCommand
from pysmt.smtlib.script import smtlibscript_from_formula, evaluate_command
from pysmt.smtlib.parser import get_formula_strict, get_formula, SmtLibParser
from pysmt.solvers.smtlib import SmtLibIgnoreMixin
from pysmt.logics import QF_UFLIRA
from pysmt.exceptions import UndefinedLogicError, PysmtValueError



class TestSmtLibScript(TestCase):

    def test_basic_operations(self):
        script = SmtLibScript()
        script.add(name=smtcmd.SET_LOGIC,
                   args=[None])

        self.assertIsNotNone(SmtLibScript())
        self.assertTrue(len(script) > 0)

        res = script.contains_command(smtcmd.SET_LOGIC)
        self.assertTrue(res)

        res = script.contains_command(smtcmd.CHECK_SAT)
        self.assertFalse(res)

        res = script.count_command_occurrences(smtcmd.CHECK_SAT)
        self.assertEqual(res, 0, "Was expecting 0 occurrences of check-sat")

        res = script.count_command_occurrences(smtcmd.SET_LOGIC)
        self.assertEqual(res, 1, "Was expecting 1 occurrences of set-logic")

        res = script.filter_by_command_name([smtcmd.SET_LOGIC])
        self.assertEqual(len(list(res)), 1)


    def test_declare_sort(self):
        class SmtLibIgnore(SmtLibIgnoreMixin):
            declare_sort_history = []
            def declare_sort(self, name, arity):
                self.declare_sort_history.append((name, arity))

        mock = SmtLibIgnore()
        parser = SmtLibParser()
        smtlib_script = '\n'.join(['(declare-sort s0 0)', \
                                   '(declare-sort s1 1)', \
                                   '(declare-const c0 s0)', \
                                   '(declare-const c1 (s1 Int))'])
        outstream = cStringIO(smtlib_script)
        script = parser.get_script(outstream)
        script.evaluate(solver=mock)

        self.assertEqual(len(mock.declare_sort_history), 2)
        s0_name, s0_arity = mock.declare_sort_history[0]
        s1_name, s1_arity = mock.declare_sort_history[1]
        self.assertEqual(s0_name, "s0")
        self.assertEqual(s0_arity, 0)
        self.assertEqual(s1_name, "s1")
        self.assertEqual(s1_arity, 1)


    def test_from_formula(self):
        x, y = Symbol("x"), Symbol("y")
        f = And(x, Or(y, x))
        script = smtlibscript_from_formula(f)

        self.assertIsNotNone(script)
        outstream = cStringIO()
        script.serialize(outstream)
        output = outstream.getvalue()
        self.assertIn("(set-logic ", output)
        self.assertIn("(declare-fun x () Bool)", output)
        self.assertIn("(declare-fun y () Bool)", output)
        self.assertIn("(check-sat)", output)

        # Use custom logic (as str)
        script2 = smtlibscript_from_formula(f, logic="BOOL")
        outstream = cStringIO()
        script2.serialize(outstream)
        output = outstream.getvalue()
        self.assertIn("(set-logic BOOL)", output)

        # Use custom logic (as Logic obj)
        script3 = smtlibscript_from_formula(f, logic=QF_UFLIRA)
        outstream = cStringIO()
        script3.serialize(outstream)
        output = outstream.getvalue()
        self.assertIn("(set-logic QF_UFLIRA)", output)

        # Custom logic must be a Logic or Str
        with self.assertRaises(UndefinedLogicError):
            smtlibscript_from_formula(f, logic=4)


    def test_get_strict_formula(self):

        smtlib_single = """
(set-logic UF_LIRA)
(declare-fun x () Bool)
(declare-fun y () Bool)
(declare-fun r () Real)
(assert (> r 0.0))
(assert x)
(check-sat)
"""
        smtlib_double = smtlib_single + """
(assert (not y))
(check-sat)
"""

        r = Symbol("r", REAL)
        x, y = Symbol("x"), Symbol("y")
        target_one = And(GT(r, Real(0)), x)
        target_two = And(GT(r, Real(0)), x, Not(y))

        stream_in = cStringIO(smtlib_single)
        f = get_formula(stream_in)
        self.assertEqual(f, target_one)

        stream_in = cStringIO(smtlib_double)
        f = get_formula(stream_in)
        self.assertEqual(f, target_two)

        stream_in = cStringIO(smtlib_double)
        with self.assertRaises(PysmtValueError):
            f = get_formula_strict(stream_in)


    def test_define_funs_same_args(self):
        # n is defined once as an Int and once as a Real
        smtlib_script = "\n".join(['(define-fun f ((n Int)) Int n)', '(define-fun f ((n Real)) Real n)'])
        stream = cStringIO(smtlib_script)
        parser = SmtLibParser()
        _ = parser.get_script(stream)
        # No exceptions are thrown
        self.assertTrue(True)


    def test_define_funs_arg_and_fun(self):
        smtlib_script = "\n".join(['(define-fun f ((n Int)) Int n)', '(declare-fun n () Real)'])
        stream = cStringIO(smtlib_script)
        parser = SmtLibParser()
        _ = parser.get_script(stream)
        # No exceptions are thrown
        self.assertTrue(True)


    def test_evaluate_command(self):
        class SmtLibIgnore(SmtLibIgnoreMixin):
            pass

        mock = SmtLibIgnore()
        for cmd_name in [ smtcmd.SET_INFO,
                          smtcmd.ASSERT,
                          smtcmd.CHECK_SAT,
                          smtcmd.EXIT,
                          smtcmd.SET_LOGIC,
                          smtcmd.DECLARE_CONST,
                          smtcmd.PUSH,
                          smtcmd.POP]:

            evaluate_command(SmtLibCommand(cmd_name, [None, None]),
                             solver=mock)

        evaluate_command(SmtLibCommand(smtcmd.DECLARE_FUN,
                                       [None, None, None]),
                         solver=mock)

        evaluate_command(SmtLibCommand(smtcmd.DEFINE_FUN,
                                       [None, None, None, None]),
                         solver=mock)


    def test_smtlibignore_mixin(self):
        """In SmtLibIgnoreMixin, all SMT-LIB methods return None."""
        class SmtLibIgnore(SmtLibIgnoreMixin):
            pass

        solver = SmtLibIgnore()
        self.assertIsNone(solver.set_logic(None))
        self.assertIsNone(solver.declare_fun(None))
        self.assertIsNone(solver.declare_const(None))
        self.assertIsNone(solver.define_fun(None, None, None, None))
        self.assertIsNone(solver.declare_sort(None, None))
        self.assertIsNone(solver.define_sort(None, None, None))
        self.assertIsNone(solver.assert_(None))
        self.assertIsNone(solver.get_assertions())
        self.assertIsNone(solver.check_sat())
        self.assertIsNone(solver.get_proof())
        self.assertIsNone(solver.get_unsat_core())
        self.assertIsNone(solver.get_values(None))
        self.assertIsNone(solver.get_assignment())
        self.assertIsNone(solver.push())
        self.assertIsNone(solver.pop())
        self.assertIsNone(solver.get_option(None))
        self.assertIsNone(solver.set_option(None, None))
        self.assertIsNone(solver.get_info(None))
        self.assertIsNone(solver.set_info(None, None))
        self.assertIsNone(solver.exit())

    def test_all_parsing(self):
        # Create a small file that tests all commands of smt-lib 2
        parser = SmtLibParser()

        nie = 0
        for cmd in DEMO_SMTSCRIPT:
            try:
                next(parser.get_command_generator(cStringIO(cmd)))
            except NotImplementedError:
                nie += 1
        # There are currently 3 not-implemented commands
        self.assertEqual(nie, 3)

DEMO_SMTSCRIPT = [ "(declare-fun a () Bool)",
                   "(declare-fun b () Bool)",
                   "(declare-fun c () Bool)",
                   "(assert true)",
                   "(assert (not a))",
                   "(check-sat)",
                   "(check-sat-assuming (a b c))",
                   "(check-sat-assuming ((not a) b (not c)))",
                   "(declare-const d Bool)",
                   "(declare-fun abc () Int)",
                   "(declare-sort A 0)",
                   "(declare-sort B 0)",
                   "(declare-sort C 0)",
                   "(declare-sort D 1)",
                   "(define-sort E () (D Int))",
                   "(declare-sort F 2)",
                   "(define-sort G (H) (F Int H))",
                   "(define-fun f ((a Bool)) B a)",
                   "(define-fun g ((a Bool)) B (f a))",
                   "(define-fun h ((a Int)) Int a)",
                   "(declare-const x Bool)",
                   "(declare-const y Int)",
                   "(assert (= (h y) y))",
                   "(assert (= (f x) x))",
                   "(check-sat)",
                   "(define-fun-rec f ((a A)) B a)",
                   "(define-fun-rec g ((a A)) B (g a))",
                   """(define-funs-rec ((h ((a A)) B) (i ((a A)) B) )
                                       ( (i a) (h a))
                   )
                   """,
                   "(define-sort A () B)",
                   "(define-sort A (B C) (Array B C))",
                   "(echo \"hello world\")",
                   "(exit)",
                   "(get-assertions)",
                   "(get-assignment)",
                   "(get-info :name)",
                   "(get-model)",
                   "(get-option :keyword)",
                   "(get-proof)",
                   "(get-unsat-assumptions)",
                   "(get-unsat-core)",
                   "(get-value (x y z))",
                   "(pop 42)",
                   "(push 42)",
                   "(reset)",
                   "(reset-assertions)",
                   "(set-info :number 42)",
                   "(set-logic QF_LIA)",
                   "(set-option :produce-models true)",
               ]

if __name__ == "__main__":
    main()
