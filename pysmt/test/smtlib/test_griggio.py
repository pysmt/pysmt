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

from pysmt.shortcuts import reset_env
from pysmt.test import TestCase
from pysmt.smtlib.parser import SmtLibParser


class TestSmtLibParserGriggio(TestCase):

    def test_files(self):
        failed = []
        for fname in ("test%d.smt2.bz2" %d for d in range(1,7)):
            try:
                self.parse(os.path.join(SMTLIB_DIR, fname))
            except NotImplementedError as ex:
                print("Ignoring not implemented SMT command error: %s"\
                      % str(ex))
            except Exception as ex:
                failed.append((fname, ex))
        if len(failed) != 0:
            for fname, ex in failed:
                print(fname, ex)
                print("-"*50)
        self.assertTrue(len(failed) == 0, "%d/6" % len(failed))

    def parse(self, fname):
        reset_env()
        parser = SmtLibParser()
        script = parser.get_script_fname(fname)
        self.assertIsNotNone(script)

SMTLIB_DIR = "pysmt/test/smtlib/griggio"
