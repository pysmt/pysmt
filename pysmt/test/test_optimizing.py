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

    def test_minimization_basic(self):
        optimization_examples = get_full_example_omt_formuale()

        for test_case in optimization_examples:
            for oname in get_env().factory.all_optimizers(logic=QF_LIA):
                with Optimizer(name=oname) as opt:
                    for assertion in test_case.assertions:
                        opt.add_assertion(assertion)
                    for (goals, optimization_type), goals_values in test_case.goals.items():
                        if optimization_type == OptimizationTypes.LEXICOGRAPHIC:
                            self._test_lexicographic(opt, goals, goals_values, test_case.name)
                        elif optimization_type == OptimizationTypes.PARETO:
                            self._test_pareto(opt, goals, goals_values, test_case.name)
                        elif optimization_type == OptimizationTypes.BOXED:
                            self._test_boxed(opt, goals, goals_values, test_case.name)
                        elif optimization_type == OptimizationTypes.BASIC:
                            raise NotImplementedError() #TODO
                        else:
                            raise NotImplementedError() # TODO

    def _check_oracle_goals(self, goals, goals_values, costs, name):
        assert len(goals) == len(goals_values) == len(costs), name
        for goal, goal_value, cost in zip(goals, goals_values, costs):
            self.assertEqual(
                goal_value,
                cost,
                f"name: {name}, goal: {goal}, oracle value: {goal_value}, cost returned: {cost}"
            )

    def _test_lexicographic(self, optimizer, goals, goals_values, name):
        retval = optimizer.lexicographic_optimize(goals)
        self.assertIsNotNone(retval, name)
        _, costs = retval
        self._check_oracle_goals(goals, goals_values, costs, name)

    def _test_pareto(self, optimizer, goals, goals_values, name):
        retval = optimizer.pareto_optimize(goals)
        self.assertIsNotNone(retval, name)
        for _, costs in retval:
            # TODO here iterate over the goals_values and find the correct connection with the costs (probably with a sorting)
            self._check_oracle_goals(goals, goals_values, costs, name)

    def _test_boxed(self, optimizer, goals, goals_values, name):
        retval = optimizer.boxed_optimize(goals)
        self.assertIsNotNone(retval, name)
        _, costs = retval
        self._check_oracle_goals(goals, goals_values, costs, name)
