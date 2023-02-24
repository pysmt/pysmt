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

from io import StringIO

from pysmt.shortcuts import reset_env
from pysmt.test import TestCase
from pysmt.smtlib.parser import SmtLibParser
from pysmt.exceptions import PysmtSyntaxError


class TestSmtLibParserOMT(TestCase):

    def test_parse_omt(self):
        for file_id, expected, script in self.examples():
            for i, cmd in enumerate(script):
                self.assertEqual(cmd.name, expected[i],
                                 "Test %d: %s != %s " %
                                 (file_id, cmd.name, expected[i]))
            # Serialize
            buf = StringIO()
            script.serialize(buf)
            parser = SmtLibParser()
            new_script = parser.get_script(StringIO(buf.getvalue()))
            self.assertEqual([cmd.name for cmd in script], [cmd.name for cmd in new_script])

    def test_omt_parsing_exception(self):
        parser = SmtLibParser()
        with self.assertRaises(PysmtSyntaxError):
            parser.get_script(StringIO("(assert-soft false :weight (+ 3 (- 4 2)) :id goal :id goal)"))
        with self.assertRaises(PysmtSyntaxError):
            parser.get_script(StringIO("(assert-soft false :weight (+ 3 (- 4 2)) :id goal :weight z )"))
        with self.assertRaises(PysmtSyntaxError):
            parser.get_script(StringIO("(assert-soft false :weight (+ 3 (- 4 2)) :id goal :not-implemented 12)"))
        with self.assertRaises(PysmtSyntaxError):
            parser.get_script(StringIO("(assert-soft false :not-implemented 12)"))
        with self.assertRaises(PysmtSyntaxError):
            parser.get_script(StringIO("(maximize z :upper 50 :lower 50 :id abc"))

    def test_command_option_value_correctness(self):
        for input_command, command, len_args in TestSmtLibParserOMT.snippet_examples():
            parser = SmtLibParser()
            script = parser.get_script(StringIO(input_command))
            cmd = next(iter(script))
            self.assertEqual(cmd.name, command)
            self.assertEqual(len(cmd.args), len_args)

    def parse_from_file(self, file_id):
        fname = OMT_FILE_PATTERN % file_id
        reset_env()
        parser = SmtLibParser()
        script = parser.get_script_fname(fname)
        self.assertIsNotNone(script)
        return script

    def examples(self):
        for file_id in TEST_FILES:
            script = self.parse_from_file(file_id)
            yield file_id, TEST_FILES[file_id], script

    @staticmethod
    def snippet_examples():
        for input_command, command, len_args in TEST_SNIPPETS:
            yield input_command, command, len_args


OMT_FILE_PATTERN = "pysmt/test/smtlib/omt/omt_test%d.smt2.bz2"

TEST_SNIPPETS = [
    ("(assert-soft false :weight 2 :id goal)", "assert-soft", 2),
    ("(maximize z)", "maximize", 2),
    ("(maximize z :signed :id abc)", "maximize", 2),
    ("(check-allsat ( a b c ))", "check-allsat", 3),
    ("(load-objective-model 1)", "load-objective-model", 1),
    ("(get-objectives)", "get-objectives", 0)
]

TEST_FILES = {
    1: ["set-option",
        "set-logic",
        "define-fun",
        "declare-fun",
        "declare-fun",
        "declare-fun",
        "declare-fun",
        "assert-soft",
        "assert-soft",
        "assert-soft",
        "assert-soft",
        "assert-soft",
        "assert-soft",
        "assert-soft",
        "assert-soft",
        "assert-soft",
        "assert",
        "check-allsat",
        "exit",
        ],

    2: [
        "set-option",
        "declare-fun",
        "declare-fun",
        "declare-fun",
        "assert",
        "minimize",
        "maximize",
        "maximize",
        "maximize",
        "maximize",
        "check-sat",
        "get-objectives",
        "load-objective-model",
        "exit"
    ],

    3: [
        "set-option",
        "set-option",
        "declare-fun",
        "assert",
        "minimize",
        "minimize",
        "check-sat",
        "get-objectives",
        "exit"
    ]
}
