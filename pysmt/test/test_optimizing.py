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
from pysmt.test import TestCase, skipIfNoOptimizerForLogic
from pysmt.test import main
from pysmt.test.omt_examples import get_full_example_omt_formuale, solve_given_examples

class TestOptimization(TestCase):
    def test_given_examples(self):
        optimization_examples = get_full_example_omt_formuale()
        solve_given_examples(self, optimization_examples, {})
