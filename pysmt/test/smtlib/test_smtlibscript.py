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
        with self.assertRaises(AssertionError):
            f = get_formula_strict(stream_in)


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


    def test_all_parsing(self):
        # Create a small file that tests all commands of smt-lib 2
        parser = SmtLibParser()

        nie = 0
        for cmd in DEMO_SMTSCRIPT:
            try:
                out = next(parser.get_command_generator(cStringIO(cmd)))
                #print(out)
            except NotImplementedError:
                #print(cmd)
                nie += 1
        # There are currently 10 not-implemented commands
        self.assertEquals(nie, 9)

DEMO_SMTSCRIPT = [ "(declare-fun a () Bool)",
                   "(declare-fun b () Bool)",
                   "(declare-fun c () Bool)",
                   "(assert true)",
                   "(assert (not a))",
                   "(check-sat)",
                   "(check-sat-assuming (a b c))",
                   "(check-sat-assuming ((not a) b (not c)))",
                   "(declare-const d Bool)",
                   "(declare-fun xyz (A B) C)", # Shouldn't this raise an error?
                   "(declare-fun abc () Int)",
                   "(declare-sort A 0)",
                   "(define-fun f ((a Bool)) B a)",
                   "(define-fun g ((a Bool)) B (f a))",
                   "(define-fun-rec f ((a A)) B a)",
                   "(define-fun-rec g ((a A)) B (g a))",
                   """(define-funs-rec ((h ((a A)) B) (i ((a A)) B) )
                                       ( (i a) (h a))
                   )
                   """,
                   "(define-sort A () B)",
                   "(define-sort A (B C) (Array B C))",
                   "(echo 'hello world')",
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
