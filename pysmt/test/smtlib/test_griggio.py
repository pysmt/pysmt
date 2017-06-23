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

from six import StringIO

from pysmt.shortcuts import reset_env
from pysmt.test import TestCase
from pysmt.smtlib.parser import SmtLibParser

class TestSmtLibParserGriggio(TestCase):

    def test_griggio(self):
        for file_id in range(1,7):
            # Parse
            script = self.parse(file_id)
            # Check cmds
            for i, cmd in enumerate(script):
                self.assertEqual(cmd.name, TESTS[file_id][i],
                                 "Test %d: %s != %s " %
                                 (file_id, cmd.name, TESTS[file_id][i]))
            # Serialize
            buf = StringIO()
            script.serialize(buf)
            self.assertTrue(True)

    def parse(self, file_id):
        fname = SMTLIB_FILE_PATTERN % file_id
        reset_env()
        parser = SmtLibParser()
        script = parser.get_script_fname(fname)
        self.assertIsNotNone(script)
        return script


SMTLIB_FILE_PATTERN = "pysmt/test/smtlib/griggio/test%d.smt2.bz2"

TESTS = {

    1 : ["declare-fun",
         "set-option",
         "declare-sort",
         "declare-fun",
         "declare-fun",
         "assert",
         "assert",
         "push",
         "define-fun",
         "assert",
         "check-sat",
         "pop",
         "define-fun",
         "exit",
    ],

    2 : ["push",
         "declare-sort",
         "pop",
         "declare-fun",
         "exit",
    ],

    3 : [ "set-option",
          "declare-fun",
          "declare-fun",
          "assert",
          "assert",
          "assert",
          "check-sat",
          "get-unsat-core",
          "exit",
    ],

    4 : [ "set-option",
         "declare-fun",
         "declare-fun",
         "assert",
         "assert",
         "assert",
         "check-sat",
         "get-assignment",
         "exit",
    ],

    5 : ["set-option",
         "declare-fun",
         "declare-fun",
         "declare-fun",
         "assert",
         "assert",
         "assert",
         "assert",
         "check-sat",
         "get-value",
         "exit",
    ],

    6 : ["declare-sort",
         "define-sort",
         "declare-fun",
         "declare-fun",
         "assert",
         "check-sat",
         "exit",
    ]
}
