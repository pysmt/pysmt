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
import pytest

from pysmt.logics import QF_UFBV
from pysmt.test.smtlib.parser_utils import execute_script_fname, smtlib_tests

@pytest.mark.parametrize("smtfile, logic, expected_result", smtlib_tests(lambda x: x == QF_UFBV))
def test_qf_ufbv(smtfile, logic, expected_result):
    execute_script_fname(smtfile, logic, expected_result)
