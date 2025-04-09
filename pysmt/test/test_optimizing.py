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

from pysmt.test import TestCase
from pysmt.test.omt_examples import get_full_example_omt_formuale, solve_given_examples, OptimizationTypes

class TestOptimization(TestCase):
    def test_fast_examples(self):
        optimization_examples = get_full_example_omt_formuale(slow=False)
        test_to_skip = {}
        solve_given_examples(self, optimization_examples, test_to_skip)

    @pytest.mark.slow
    def test_slow_examples(self):
        optimization_examples = get_full_example_omt_formuale(fast=False)
        test_to_skip = {}
        solve_given_examples(self, optimization_examples, test_to_skip)
