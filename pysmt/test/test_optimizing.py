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

from pysmt.environment import push_env, pop_env
from pysmt.test.omt_examples import get_full_example_omt_formuale
from pysmt.test.optimization_utils import generate_examples_with_solvers, solve_given_example

test_to_skip = set()

@pytest.mark.parametrize(
    "optimization_example, solver_name",
    generate_examples_with_solvers(get_full_example_omt_formuale(slow=False)),
)
def test_fast_examples(optimization_example, solver_name):
    push_env()
    solve_given_example(
        optimization_example,
        solver_name,
        test_to_skip,
    )
    pop_env()


@pytest.mark.slow
@pytest.mark.parametrize(
    "optimization_example, solver_name",
    generate_examples_with_solvers(get_full_example_omt_formuale(fast=False)),
)
def test_slow_examples(optimization_example, solver_name):
    push_env()
    solve_given_example(
        optimization_example,
        solver_name,
        test_to_skip,
    )
    pop_env()
