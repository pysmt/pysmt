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

from pysmt.test import TestCase, main
from pysmt.smtlib.parser import SmtLibParser
from pysmt.exceptions import PysmtTypeError

class TestTypeError(TestCase):

    def test_wrong(self):
        d = os.path.dirname(os.path.realpath(__file__))
        smtfile = d + "/small_set/negative/wrong1.smt2.bz2"
        parser = SmtLibParser()
        with self.assertRaises(PysmtTypeError):
            parser.get_script_fname(smtfile)



if __name__ == '__main__':
    main()
