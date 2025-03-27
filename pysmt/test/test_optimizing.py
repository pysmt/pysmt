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
                for (goals, optimization_type), goals_values in test_case.goals.items():
                    test_id_str = f"test: {test_case.name}; solver: {oname}"
                    if test_case.name == "QF_BV - smtlib2_bitvector.smt2":
                        engines = ["z3", "z3_sua", "z3_incr", "msat_sua", "msat_incr", "optimsat", "optimsat_sua", "optimsat_incr"]
                        engines_to_skip = set(engines) - set([
                            # "z3", "z3_sua", "z3_incr", # working fast
                            # "msat_sua", # blocks with boxed
                            # "msat_incr", # blocks with boxed
                            "optimsat", # works fast
                            "optimsat_sua", #works fast
                            "optimsat_incr" #works fast
                        ])
                        ot_to_not_skip = set([
                            OptimizationTypes.BOXED,
                            OptimizationTypes.LEXICOGRAPHIC,
                            OptimizationTypes.PARETO,
                            OptimizationTypes.BASIC
                        ])
                        if oname in engines_to_skip or optimization_type not in ot_to_not_skip:
                            continue

                        # print(oname)
                        # continue
                        if "z3" in oname:
                            continue
                    else:
                        continue
                    with Optimizer(name=oname) as opt:
                        for assertion in test_case.assertions:
                            opt.add_assertion(assertion)
                        if optimization_type == OptimizationTypes.LEXICOGRAPHIC:
                            if oname == "z3_sua":
                                # TODO: check that this is correct
                                # z3 does not support boxed optimization
                                continue
                            self._test_lexicographic(opt, goals, goals_values, test_id_str)
                        elif optimization_type == OptimizationTypes.PARETO:
                            self._test_pareto(opt, goals, goals_values, test_id_str)
                        elif optimization_type == OptimizationTypes.BOXED:
                            if oname == "z3":
                                # TODO: check that this is correct
                                # z3 does not support boxed optimization
                                continue
                            self._test_boxed(opt, goals, goals_values, test_id_str)
                        elif optimization_type == OptimizationTypes.BASIC:
                            # if oname == "z3":
                            #     continue
                            # TODO creating an optimizer, adding assertions and then using it for all the optimizing calls fails on the basic the second time it gets called
                            # (at least z3 fails, didn't check other optimizers); check why and if it is normal
                            self._test_basic(opt, goals, goals_values, test_id_str)
                        else:
                            raise NotImplementedError(f"Unknown optimization type: {optimization_type}")

        assert False

    def _check_oracle_goals(self, goals, goals_values, costs, test_id_str):
        assert len(goals) == len(goals_values) == len(costs), test_id_str
        for goal, goal_value, cost in zip(goals, goals_values, costs):
            self.assertEqual(
                goal_value,
                cost,
                f"test_id: {test_id_str}, goal: {goal}, oracle value: {goal_value}, cost returned: {cost}"
            )

    def _test_lexicographic(self, optimizer, goals, goals_values, test_id_str):
        retval = optimizer.lexicographic_optimize(goals)
        self.assertIsNotNone(retval, test_id_str)
        _, costs = retval
        self._check_oracle_goals(goals, goals_values, costs, test_id_str)

    def _test_pareto(self, optimizer, goals, goals_values, test_id_str):
        retval = optimizer.pareto_optimize(goals)
        self.assertIsNotNone(retval, test_id_str)
        sorted_costs = sorted((costs for _, costs in retval), key=str)
        sorted_goals_values = sorted(goals_values, key=str)
        self.assertEqual(len(sorted_costs), len(sorted_goals_values), test_id_str)
        for costs, goals_values in zip(sorted_costs, sorted_goals_values):
            self._check_oracle_goals(goals, goals_values, costs, test_id_str)

    def _test_boxed(self, optimizer, goals, goals_values, test_id_str):
        retval = optimizer.boxed_optimize(goals)
        self.assertIsNotNone(retval, test_id_str)
        for goal, goal_value in zip(goals, goals_values):
            _, cost = retval[goal]
            self.assertEqual(
                goal_value,
                cost,
                f"test_id: {test_id_str}, goal: {goal}, oracle value: {goal_value}, cost returned: {cost}"
            )

    def _test_basic(self, optimizer, goals, goals_values, test_id_str):
        assert len(goals) == len(goals_values) == 1, test_id_str
        goal = goals[0]
        goal_value = goals_values[0]
        retval = optimizer.optimize(goal)
        self.assertIsNotNone(retval, test_id_str)
        _, cost = retval
        self.assertEqual(
            goal_value,
            cost,
            f"test_id: {test_id_str}, goal: {goal}, oracle value: {goal_value}, cost returned: {cost}"
        )
