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
import unittest

from pysmt.test.smtlib.parser_utils import SMTLIB_DIR
from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import reset_env
from pysmt.test import TestCase

class TestBasic(TestCase):

    def test_vmt(self):
        reset_env()
        parser = SmtLibParser()
        fname = os.path.join(SMTLIB_DIR, "small_set/vmt/c432_0f.vmt")
        script = parser.get_script_fname(fname)

        self.assertIn("A_1__AT0 ->", str(script.annotations))


if __name__ == '__main__':
    unittest.main()
