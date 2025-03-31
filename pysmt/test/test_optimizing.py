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
from pysmt.test.omt_examples import get_full_example_omt_formuale, OptimizationTypes

from pysmt.shortcuts import Optimizer, GE, Int, Symbol, INT, LE, GT, REAL, Real, Equals, Times, Solver, Or, Div
from pysmt.shortcuts import BVType, BVUGE, BVSGE, BVULE, BVSLE, BVUGT, BVSGT, BVULT, BVSLT, BVZero, BVOne, BV
from pysmt.shortcuts import And, Plus, Minus, get_env
from pysmt.logics import QF_LIA, QF_LRA, QF_BV, QF_NRA, QF_NIA
from pysmt.optimization.goal import MaximizationGoal, MinimizationGoal, \
    MinMaxGoal, MaxMinGoal, MaxSMTGoal

from pysmt.exceptions import PysmtUnboundedOptimizationError

class TestOptimization(TestCase):
    def test_given_examples(self):
        optimization_examples = get_full_example_omt_formuale()
        solve_given_examples(self, optimization_examples, {})


def solve_given_examples(pytest_test_case, optimization_examples, test_to_skip):
    for test_case in optimization_examples:
        for oname in get_env().factory.all_optimizers(logic=test_case.logic):
            for (goals, optimization_type), goals_values in test_case.goals.items():
                # TODO decomment
                if (test_case.name, optimization_type, oname) in test_to_skip:
                    continue
                # Cde to test only 1 case. Comment above
                # if (
                #     (test_case.name, optimization_type, oname) !=
                #     ("QF_BV - smtlib2_bitvector.smt2", OptimizationTypes.BASIC, "z3_sua")
                # ):
                #     continue
                test_id_str = f"test: {test_case.name}; solver: {oname}"
                print(test_id_str, optimization_type.name)
                with Optimizer(name=oname) as opt:
                    for assertion in test_case.assertions:
                        opt.add_assertion(assertion)
                    if optimization_type == OptimizationTypes.LEXICOGRAPHIC:
                        print(goals)
                        for g in goals:
                            print(g.signed)
                        _test_lexicographic(pytest_test_case, opt, goals, goals_values, test_id_str)
                    elif optimization_type == OptimizationTypes.PARETO:
                        _test_pareto(pytest_test_case, opt, goals, goals_values, test_id_str)
                    elif optimization_type == OptimizationTypes.BOXED:
                        _test_boxed(pytest_test_case, opt, goals, goals_values, test_id_str)
                    elif optimization_type == OptimizationTypes.BASIC:
                        _test_basic(pytest_test_case, opt, goals, goals_values, test_id_str)
                    else:
                        raise NotImplementedError(f"Unknown optimization type: {optimization_type}")

    # assert False


def _check_oracle_goals(pytest_test_case, goals, goals_values, costs, test_id_str):
    assert len(goals) == len(goals_values) == len(costs), test_id_str
    for goal, goal_value, cost in zip(goals, goals_values, costs):
        print(goal.signed)
        pytest_test_case.assertEqual(
            str(goal_value),
            str(cost),
            f"test_id: {test_id_str}, goal: {goal}, oracle value: {goal_value}, cost returned: {cost}"
        )


def _test_lexicographic(pytest_test_case, optimizer, goals, goals_values, test_id_str):
    retval = optimizer.lexicographic_optimize(goals)
    pytest_test_case.assertIsNotNone(retval, test_id_str)
    _, costs = retval
    _check_oracle_goals(pytest_test_case, goals, goals_values, costs, test_id_str)


def _test_pareto(pytest_test_case, optimizer, goals, goals_values, test_id_str):
    retval = optimizer.pareto_optimize(goals)
    pytest_test_case.assertIsNotNone(retval, test_id_str)
    sorted_costs = sorted((costs for _, costs in retval), key=str)
    sorted_goals_values = sorted(goals_values, key=str)
    # TODO debug on pareto of BV problem not returning the correct result
    # print(retval)
    # print(sorted_costs)
    # print(sorted_goals_values)
    pytest_test_case.assertEqual(len(sorted_costs), len(sorted_goals_values), test_id_str)
    for costs, goals_values in zip(sorted_costs, sorted_goals_values):
        _check_oracle_goals(pytest_test_case, goals, goals_values, costs, test_id_str)


def _test_boxed(pytest_test_case, optimizer, goals, goals_values, test_id_str):
    retval = optimizer.boxed_optimize(goals)
    pytest_test_case.assertIsNotNone(retval, test_id_str)
    for goal, goal_value in zip(goals, goals_values):
        _, cost = retval[goal]
        pytest_test_case.assertEqual(
            str(goal_value),
            str(cost),
            f"test_id: {test_id_str}, goal: {goal}, oracle value: {goal_value}, cost returned: {cost}"
        )


def _test_basic(pytest_test_case, optimizer, goals, goals_values, test_id_str):
    assert len(goals) == len(goals_values) == 1, test_id_str
    goal = goals[0]
    goal_value = goals_values[0]
    retval = optimizer.optimize(goal)
    pytest_test_case.assertIsNotNone(retval, test_id_str)
    _, cost = retval
    pytest_test_case.assertEqual(
        str(goal_value),
        str(cost),
        f"test_id: {test_id_str}, goal: {goal}, oracle value: {goal_value}, cost returned: {cost}"
    )
