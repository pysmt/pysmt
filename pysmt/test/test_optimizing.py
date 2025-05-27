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

from pysmt.test.omt_examples import get_full_example_omt_formuale
from pysmt.test.optimization_utils import generate_examples_with_solvers, solve_given_example, OptimizationTypes

test_to_skip = {
    ("QF_LIA 2 int 2 bools multiple objective", OptimizationTypes.PARETO, "optimsat"), # weird error, this test fails only if executed test_omt_lib_solver (skipping ("QF_LIA - smtlib2_load_objective_model.smt2", OptimizationTypes.PARETO, "optimsat") this skip becomes necessary, otherwise not). The cost returned is 0 when it should be 1
    ("QF_LIA 2 variables multiple objective", OptimizationTypes.PARETO, "optimsat"), # weird error, this test fails only if executed after test_optimization, while it works on it's own
}

@pytest.mark.parametrize(
    "optimization_example, solver_name",
    generate_examples_with_solvers(get_full_example_omt_formuale(slow=False)),
)
def test_fast_examples(optimization_example, solver_name):
    solve_given_example(
        optimization_example,
        solver_name,
        test_to_skip,
    )


@pytest.mark.slow
@pytest.mark.parametrize(
    "optimization_example, solver_name",
    generate_examples_with_solvers(get_full_example_omt_formuale(fast=False)),
)
def test_slow_examples(optimization_example, solver_name):
    solve_given_example(
        optimization_example,
        solver_name,
        test_to_skip,
    )
