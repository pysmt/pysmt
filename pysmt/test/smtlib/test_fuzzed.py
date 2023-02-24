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

import pytest

from io import StringIO

from pysmt.shortcuts import reset_env
from pysmt.test import TestCase
from pysmt.smtlib.parser import SmtLibParser


class TestSmtLibParserFuzzer(TestCase):

    @pytest.mark.slow
    def test_fuzzed(self):
        for fname in FUZZED_FILES:
            script = self.parse(os.path.join(SMTLIB_DIR, fname))
            buf = StringIO()
            script.serialize(buf)
            #print(buf.getvalue())
            self.assertTrue(len(buf.getvalue()) > 1)

    def parse(self, fname):
        reset_env()
        parser = SmtLibParser()
        script = parser.get_script_fname(fname)
        self.assertIsNotNone(script)
        return script
#


SMTLIB_DIR = "pysmt/test/smtlib/fuzzed"
FUZZED_FILES = ["AUFLIA.smt2.bz2",
                "QF_AUFBV.smt2.bz2",
                "QF_LRA.smt2.bz2",
                "QF_UFLIA.smt2.bz2",
                "AUFLIRA.smt2.bz2",
                "QF_AUFLIA.smt2.bz2",
                "QF_NIA.smt2.bz2",
                "QF_UFLRA.smt2.bz2",
                "AUFNIRA.smt2.bz2",
                "QF_AX.smt2.bz2",
                "QF_NRA.smt2.bz2",
                "QF_UFNRA.smt2.bz2",
                "QF_BV.smt2.bz2",
                "QF_RDL.smt2.bz2",
                "QF_UFRDL.smt2.bz2",
                "QF_IDL.smt2.bz2",
                "QF_UFBV.smt2.bz2",
                "QF_UF.smt2.bz2",
                "QF_LIA.smt2.bz2",
                "QF_UFIDL.smt2.bz2",
                ]
