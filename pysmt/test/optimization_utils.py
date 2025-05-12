from enum import Enum, auto
from itertools import chain
import pytest

from pysmt.fnode import FNode
from pysmt.shortcuts import get_env
from pysmt.exceptions import PysmtUnboundedOptimizationError, PysmtInfinitesimalError, PysmtValueError

class OptimizationTypes(Enum):
    BASIC = auto()
    LEXICOGRAPHIC = auto()
    PARETO = auto()
    BOXED = auto()


class OMTTestCase:
    """
    This class stores the info to test the OMT optimization methods over a precise
    set of assertions, set of goals and the expected optimal values for the goals.

    The test case is defined by the following parameters:
    - name: the name of the test case
    - assertions: the assertions to be added to the optimizer
    - logic: the logic to be used by the optimizer
    - solvable: True if the test case is solvable, False otherwise
    - goals: a dictionary with the goals and the expected values for the goals.

    The keys of the dictionary are tuples with the goals and the OptimizationType
    corresponding to that value.
    The values of the dictionary depends on the OptimizationType:
    - BASIC: a list/tuple with only one value, the expected
        value for the goal
    - LEXICOGRAPHIC/BOXED: a list/tuple with as many values as the goals specified
    - PARETO: a list/tuple, where each element is a list/tuple containing as many
        values as the goals specified

    The expected values of the goals can be either a FNode or a string.
    If the expected value is a FNode, it must be a constant value.
    If the expected value is a string, it must be either "unbounded" or "infinitesimal".
    """
    def __init__(self, name, assertions, logic, solvable, goals, env):
        self._name = name
        self._assertions = assertions
        self._logic = logic
        self._solvable = solvable
        self._goals = goals
        self._env = env
        if env is None:
            self._env = get_env(env)

        # consistency checks
        if bool(goals) != solvable:
            raise PysmtValueError(
                "Goals must be specified if and only if the test case is solvable"
            )

        for (current_goals, optimization_type), goals_oracle_values in goals.items():
            if optimization_type == OptimizationTypes.BASIC:
                if len(current_goals) != 1 or len(goals_oracle_values) != 1:
                    raise PysmtValueError("%s optimization accept only one goal" % optimization_type.name)
                single_goal = goals_oracle_values[0]
                if not isinstance(single_goal, FNode):
                    raise PysmtValueError("Wrong type of the goals data structure")
            elif optimization_type in (OptimizationTypes.LEXICOGRAPHIC, OptimizationTypes.BOXED):
                goals_number = len(current_goals)
                if goals_number == 0:
                    raise PysmtValueError("%s needs at least one goal" % optimization_type.name)
                if len(goals_oracle_values) != goals_number:
                    raise PysmtValueError(
                        "In %s optimization the number of goals values must be the same of the number of the given goals: %s, %d" % (optimization_type.name, str(goals_oracle_values), goals_number)
                    )
            elif optimization_type == OptimizationTypes.PARETO:
                goals_number = len(current_goals)
                if goals_number == 0:
                    raise PysmtValueError("%s needs at least one goal" % optimization_type.name)
                for pareto_goals in goals_oracle_values:
                    if not isinstance(pareto_goals, (list, tuple)):
                        raise PysmtValueError("In %s optimization the goals oracle value must be a list or a tuple of FNode" % optimization_type.name)
                    if len(pareto_goals) != goals_number:
                        raise PysmtValueError("In %s optimization the goals number of goal values must equal the number of given goals" % optimization_type.name)
            else:
                raise NotImplementedError("%s optimization is not supported yet" % optimization_type.name)

    @property
    def name(self):
        return self._name

    @property
    def assertions(self):
        return self._assertions

    @property
    def logic(self):
        return self._logic

    @property
    def solvable(self):
        return self._solvable

    @property
    def goals(self):
        return self._goals

    @property
    def environment(self):
        return self._env


# method to solve the given examples
def generate_examples_with_solvers(optimization_examples):
    """
    This method takes a list of OMTTestCases and yields all the possible
    combinations of an OMTTestCase and the name of a solver that support
    the logic of said test.
    """
    has_real_minimization_or_maximization = lambda opt_example: any(
        (g.is_maximization_goal() or g.is_minimization_goal()) and g.term().get_type().is_real_type()
        for goals, _ in opt_example.goals.keys()
        for g in goals
    )
    for optimization_example in optimization_examples:
        env = optimization_example.environment
        for solver_name, solver_class in env.factory.all_optimizers(logic=optimization_example.logic).items():
            if optimization_example.logic.theory.real_arithmetic and has_real_minimization_or_maximization(optimization_example):
                solver = solver_class(env, optimization_example.logic)
                if solver.can_diverge_for_unbounded_cases():
                    continue
            yield optimization_example, solver_name


def solve_given_example(optimization_example, solver_name, test_to_skip=None):
    """
    Method to solve a single OMTTestCase using the given solver.
    """
    # test basic in boxed only if there is no basic optimization explicitly specified
    test_basic_in_boxed = all(ot != OptimizationTypes.BASIC for _, ot in optimization_example.goals.keys())

    for (goals, optimization_type), goals_values in optimization_example.goals.items():
        if test_to_skip is not None and (optimization_example.name, optimization_type, solver_name) in test_to_skip:
            continue
        test_id_str = "test: %s; solver: %s; optimization: %s" % (optimization_example.name, solver_name, optimization_type.name)
        print(test_id_str)
        with optimization_example.environment.factory.Optimizer(
            name=solver_name, logic=optimization_example.logic
        ) as opt:
            for assertion in optimization_example.assertions:
                opt.add_assertion(assertion)
            if optimization_type == OptimizationTypes.LEXICOGRAPHIC:
                _test_lexicographic(opt, goals, goals_values, test_id_str)
            elif optimization_type == OptimizationTypes.PARETO:
                _test_pareto(opt, goals, goals_values, test_id_str)
            elif optimization_type == OptimizationTypes.BOXED:
                _test_boxed(opt, goals, goals_values, test_id_str, test_basic_in_boxed)
            elif optimization_type == OptimizationTypes.BASIC:
                _test_basic(opt, goals[0], goals_values[0], test_id_str)
            else:
                raise NotImplementedError("Unknown optimization type: %s" % optimization_type)


def _check_oracle_goal(goal, goal_value, cost, test_id_str):
    # converts the goal value and cost to constants and then checks if they are equal
    assert goal_value.is_constant() and cost.is_constant(), "test: %s, goal: %s, goal_value: %s, cost: %s" % (test_id_str, str(goal), str(goal_value), str(cost))

    if goal_value.is_bv_constant():
        assert cost.is_bv_constant(), "test: %s, goal: %s, goal_value: %s, cost: %s" % (test_id_str, str(goal), str(goal_value), str(cost))
        if goal.signed:
            goal_value_constant = goal_value.bv_signed_value()
            cost_constant = cost.bv_signed_value()
        else:
            goal_value_constant = goal_value.bv_unsigned_value()
            cost_constant = cost.bv_unsigned_value()
    else:
        assert goal_value.is_real_constant() or goal_value.is_int_constant(), "test: %s, goal: %s, goal_value: %s, cost: %s" % (test_id_str, str(goal), str(goal_value), str(cost))
        assert cost.is_real_constant() or cost.is_int_constant(), "test: %s, goal: %s, goal_value: %s, cost: %s" % (test_id_str, str(goal), str(goal_value), str(cost))
        goal_value_constant = goal_value.constant_value()
        cost_constant = cost.constant_value()
    assert goal_value_constant == cost_constant, (
        "test_id: %s, goal: %s, oracle value: %s, cost returned: %s" % (test_id_str, str(goal), str(goal_value), str(cost))
    )


def _get_expected_raised_class(goals_value):
    raised_class = None
    if isinstance(goals_value, str):
        if goals_value == "unbounded":
            raised_class = PysmtUnboundedOptimizationError
        elif goals_value == "infinitesimal":
            raised_class = PysmtInfinitesimalError
        else:
            raise ValueError("Unknown value for goals_values")
    return raised_class


def _test_lexicographic(optimizer, goals, goals_values, test_id_str):
    raised_class = _get_expected_raised_class(goals_values[0])
    assert raised_class is None or len(goals_values) == 1, "test: %s, goals_values: %s" % (test_id_str, str(goals_values))
    if raised_class is None:
        retval = optimizer.lexicographic_optimize(goals)
        assert retval is not None, test_id_str
        _, costs = retval
        assert len(goals) == len(goals_values) == len(costs), test_id_str
        for goal, goal_value, cost in zip(goals, goals_values, costs):
            _check_oracle_goal(goal, goal_value, cost, test_id_str)
    elif not optimizer.can_diverge_for_unbounded_cases():
        with pytest.raises(raised_class):
            optimizer.lexicographic_optimize(goals)


def _test_pareto(optimizer, goals, goals_values, test_id_str):
    raised_class = _get_expected_raised_class(goals_values[0])
    assert raised_class is None or len(goals_values) == 1, "test: %s, goals_values: %s" % (test_id_str, str(goals_values))
    if raised_class is None:
        retval = optimizer.pareto_optimize(goals)
        assert retval is not None, test_id_str

        sorted_costs = sorted((costs for _, costs in retval), key=str)
        sorted_goals_values = sorted(goals_values, key=str)

        assert len(sorted_costs) == len(sorted_goals_values), test_id_str
        for costs, goals_values in zip(sorted_costs, sorted_goals_values):
            assert len(goals) == len(costs) == len(goals_values), test_id_str

            for goal, goal_value, cost in zip(goals, goals_values, costs):
                _check_oracle_goal(goal, goal_value, cost, test_id_str)
    elif not optimizer.can_diverge_for_unbounded_cases():
        with pytest.raises(raised_class):
            optimizer.pareto_optimize(goals)


def _test_boxed(optimizer, goals, goals_values, test_id_str, test_basic):
    # extract which class should be raised by the boxed optimization
    raised_class = None
    for goal_value in goals_values:
        current_raised_class = _get_expected_raised_class(goal_value)
        if current_raised_class is not None:
            raised_class = current_raised_class
            break

    # check the boxed optimization
    if raised_class is None:
        retval = optimizer.boxed_optimize(goals)
        assert retval is not None, test_id_str
        for goal, goal_value in zip(goals, goals_values):
            _, cost = retval[goal]
            _check_oracle_goal(goal, goal_value, cost, test_id_str)
    elif not optimizer.can_diverge_for_unbounded_cases():
        with pytest.raises(raised_class):
            optimizer.boxed_optimize(goals)

    # test single optimizations separately
    if test_basic:
        for goal, goal_value in zip(goals, goals_values):
            _test_basic(optimizer, goal, goal_value, test_id_str)


def _test_basic(optimizer, goal, goal_value, test_id_str):
    raised_class = _get_expected_raised_class(goal_value)
    if raised_class is None:
        retval = optimizer.optimize(goal)
        assert retval is not None, test_id_str
        _, cost = retval
        _check_oracle_goal(goal, goal_value, cost, test_id_str)
    elif not optimizer.can_diverge_for_unbounded_cases():
        with pytest.raises(raised_class):
            optimizer.optimize(goal)
