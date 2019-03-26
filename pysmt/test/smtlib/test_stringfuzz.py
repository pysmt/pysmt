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
from pysmt.smtlib.parser import SmtLibParser, get_formula_fname


class TestStringsTheoryViaSmtLib(TestCase):

    def test_parse_and_dump(self):
        for fname in FILES:
            reset_env()
            script = self.parse(fname)
            buf = StringIO()
            script.serialize(buf)
            self.assertTrue(len(buf.getvalue()) > 1)

    def test_parse_and_simplify(self):
        for fname in FILES:
            reset_env()
            formula = get_formula_fname(fname)
            formula.simplify()

    def parse(self, fname):
        parser = SmtLibParser()
        script = parser.get_script_fname(fname)
        self.assertIsNotNone(script)
        return script


SMTLIB_DIR = "pysmt/test/smtlib/stringfuzz"
FILES =  [os.path.join(SMTLIB_DIR, _fname)
          for _fname in
          ["many-regexes-00016-1.smt25",
           "concats-small-00004-0.smt25",
           "regex-deep-00008-0.smt25",
           "concats-balanced-00010-8.smt25",
           "lengths-concats-00001-0.smt25",
           "regex-deep-00000-0.smt25",
           "regex-deep-00003-0.smt25",
           "concats-extracts-big-00001-0.smt25",
           "regex-deep-00013-0.smt25",
           "regex-deep-00005-0.smt25",
           "different-prefix-00002-0.smt25",
           "overlaps-big-00046-1.smt25",
           "regex-deep-00010-0.smt25",
           "regex-deep-00011-0.smt25",
           "regex-deep-00009-0.smt25",
           "regex-deep-00007-0.smt25",
           "regex-deep-00002-0.smt25",
           "regex-deep-00006-0.smt25",
           "regex-lengths-00051-1.smt25",
           "regex-deep-00014-0.smt25",
           "regex-deep-00004-0.smt25",
           "regex-big-00106-1.smt25",
           "regex-pair-00001-1.smt25",
           "regex-deep-00012-0.smt25",
           "regex-deep-00001-0.smt25",
          ]]
