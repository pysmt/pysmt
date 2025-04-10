from enum import Enum, auto
import os.path as path
import warnings

from pysmt.environment import get_env
from pysmt.optimization.goal import Goal
from pysmt.logics import Logic
from pysmt.fnode import FNode
from pysmt.shortcuts import Optimizer, GE, Int, Symbol, INT, LE, GT, REAL, Real, Equals, Times, Solver, Or, Div
from pysmt.shortcuts import BVType, BVUGE, BVSGE, BVULE, BVSLE, BVUGT, BVSGT, BVULT, BVSLT, BVZero, BVOne, BV, Ite
from pysmt.shortcuts import And, Plus, Minus, get_env, BOOL, Implies, SBV
from pysmt.logics import QF_LIA, QF_LRA, QF_BV, QF_NRA, QF_NIA
from pysmt.optimization.goal import MaximizationGoal, MinimizationGoal, \
    MinMaxGoal, MaxMinGoal, MaxSMTGoal
from pysmt.smtlib.script import InterpreterOMT
from pysmt.smtlib.parser.parser import SmtLib20Parser
from pysmt.smtlib.commands import ASSERT, CHECK_SAT, CHECK_ALLSAT, MAXIMIZE, MINIMIZE
from pysmt.exceptions import PysmtUnboundedOptimizationError, PysmtInfinitesimalError


test_folder = path.dirname(path.abspath(__file__))
omt_smt2_files_folder = path.join(test_folder, "smtlib", "omt")

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
    # TODO add doc
    # name: str
    # assertions: List[FNode]
    # logic: Logic
    # solvable: bool
    # goals: Optional[Dict[Tuple[Tuple[Goal, ...], OptimizationTypes], List[Union[FNode, List[FNode],
    #                                               "unbounded", "infinitesimal"]]]] -> if there is the string expect an exception
    #
    def __init__(self, name, assertions, logic, solvable, goals):
        self._name = name
        self._assertions = assertions
        self._logic = logic
        self._solvable = solvable
        self._goals = goals

        # consistency checks
        assert bool(goals) == solvable, "Goals must be specified if and only if the test case is solvable"

        for (current_goals, optimization_type), goals_oracle_values in goals.items():
            if optimization_type == OptimizationTypes.BASIC:
                assert len(current_goals) == 1, f"{optimization_type.name} optimization accept only one goal"
                assert len(goals_oracle_values) == 1, f"{optimization_type.name} optimization accept only one goal"
                single_goal = goals_oracle_values[0]
                assert isinstance(single_goal, FNode), "Wrong type of the goals data structure"
            elif optimization_type in (OptimizationTypes.LEXICOGRAPHIC, OptimizationTypes.BOXED):
                goals_number = len(current_goals)
                assert goals_number > 0, f"{optimization_type.name} needs at least one goal"
                assert len(goals_oracle_values) == goals_number, f"In {optimization_type.name} optimization the number of goals values must be the same of the number of the given goals: {goals_oracle_values}, {goals_number}"
            elif optimization_type == OptimizationTypes.PARETO:
                goals_number = len(current_goals)
                assert goals_number > 0, f"{optimization_type.name} needs at least one goal"
                for pareto_goals in goals_oracle_values:
                    assert isinstance(pareto_goals, (list, tuple)), f"In {optimization_type.name} optimization the goals oracle value must be a list or a tuple of FNode"
                    assert len(pareto_goals) == goals_number, f"In {optimization_type.name} optimization the goals number of goal values must equal the number of given goals"
            else:
                raise NotImplementedError(f"{optimization_type.name} optimization is not supported yet")

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


def _fast_examples():
    yield qf_lia_two_variables_multi_obj_example()
    yield qf_lia_2_int_2_bools_multiple_objective()
    yield qf_lra_box_volume()
    yield qf_lia_box_volume()


def _slow_examples():
    yield test_maximize_revenue()


def get_full_example_omt_formuale(environment=None, fast=True, slow=True):
    """Return a list of OMTTestCases using the given environment."""

    if environment is None:
        environment = get_env()
    assert fast or slow, "If neither fast or slow are True this method returns no test cases"

    with environment:
        omt_examples = []
        if fast:
            omt_examples.extend(_fast_examples())
        if slow:
            omt_examples.extend(_slow_examples())
    return omt_examples


# method to solve the given examples
def generate_examples_with_solvers(optimization_examples):
    """
    This method takes a list of OMTTestCases and yields all the possible
    combinations of an OMTTestCase and the name of a solver that support
    the logic of said test.
    """
    for optimization_example in optimization_examples:
        for solver_name in get_env().factory.all_optimizers(logic=optimization_example.logic):
            # is_sua_or_incr is passed to the methods to skip the unbound or infinitesimal cases
            is_sua_or_incr = "_sua" in solver_name or "_incr" in solver_name
            # skip sua and incr algorithms for logics with real
            if optimization_example.logic.theory.real_arithmetic and is_sua_or_incr:
                continue
            yield optimization_example, solver_name


def solve_given_example(pytest_test_case, optimization_example, solver_name, test_to_skip=None):
    """
    Method to solve a single OMTTestCase using the given solver.
    """
    with warnings.catch_warnings():

        # ignore the z3 defining a new symbol warning, since it is raised many times
        warnings.filterwarnings("ignore", r"Defining new symbol: z3name!\d+")

        # ignore the z3 warning on boxed optimization being suboptimal
        warnings.filterwarnings("ignore", r"Boxed optimization is not working in Z3 .*")

        # ignore the MathSAT warning on UF with bool arguments
        warnings.filterwarnings("ignore", r"MathSAT convert\(\): UF with bool arguments have been .*")

        # test basic in boxed only if there is no basic optimization explicitly specified
        test_basic_in_boxed = all(ot != OptimizationTypes.BASIC for _, ot in optimization_example.goals.keys())

        is_sua_or_incr = "_sua" in solver_name or "_incr" in solver_name
        for (goals, optimization_type), goals_values in optimization_example.goals.items():
            if test_to_skip is not None and (optimization_example.name, optimization_type, solver_name) in test_to_skip:
                continue
            test_id_str = f"test: {optimization_example.name}; solver: {solver_name}; optimization: {optimization_type.name}"
            print(test_id_str)
            with Optimizer(name=solver_name, logic=optimization_example.logic) as opt:
                for assertion in optimization_example.assertions:
                    opt.add_assertion(assertion)
                if optimization_type == OptimizationTypes.LEXICOGRAPHIC:
                    _test_lexicographic(pytest_test_case, opt, goals, goals_values, test_id_str, is_sua_or_incr)
                elif optimization_type == OptimizationTypes.PARETO:
                    _test_pareto(pytest_test_case, opt, goals, goals_values, test_id_str, is_sua_or_incr)
                elif optimization_type == OptimizationTypes.BOXED:
                    _test_boxed(pytest_test_case, opt, goals, goals_values, test_id_str, test_basic_in_boxed, is_sua_or_incr)
                elif optimization_type == OptimizationTypes.BASIC:
                    _test_basic(pytest_test_case, opt, goals[0], goals_values[0], test_id_str, is_sua_or_incr)
                else:
                    raise NotImplementedError(f"Unknown optimization type: {optimization_type}")



def _check_oracle_goal(pytest_test_case, goal, goal_value, cost, test_id_str):
    # converts the goal value and cost to constants and then checks if they are equal
    assert goal_value.is_constant() and cost.is_constant(), f"test: {test_id_str}, goal: {goal}, goal_value: {goal_value}, cost: {cost}"
    if goal_value.is_bv_constant():
        assert cost.is_bv_constant(), f"test: {test_id_str}, goal: {goal}, goal_value: {goal_value}, cost: {cost}"
        if goal.signed:
            goal_value_constant = goal_value.bv_signed_value()
            cost_constant = cost.bv_signed_value()
        else:
            goal_value_constant = goal_value.bv_unsigned_value()
            cost_constant = cost.bv_unsigned_value()
    else:
        assert goal_value.is_real_constant() or goal_value.is_int_constant(), f"test: {test_id_str}, goal: {goal}, goal_value: {goal_value}, cost: {cost}"
        assert cost.is_real_constant() or cost.is_int_constant(), f"test: {test_id_str}, goal: {goal}, goal_value: {goal_value}, cost: {cost}"
        goal_value_constant = goal_value.constant_value()
        cost_constant = cost.constant_value()
    pytest_test_case.assertEqual(
        goal_value_constant,
        cost_constant,
        f"test_id: {test_id_str}, goal: {goal}, oracle value: {goal_value}, cost returned: {cost}"
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


def _test_lexicographic(pytest_test_case, optimizer, goals, goals_values, test_id_str, is_sua_or_incr):
    raised_class = _get_expected_raised_class(goals_values[0])
    assert raised_class is None or len(goals_values) == 1, f"test: {test_id_str}, goals_values: {goals_values}"
    if raised_class is None:
        retval = optimizer.lexicographic_optimize(goals)
        pytest_test_case.assertIsNotNone(retval, test_id_str)
        _, costs = retval
        assert len(goals) == len(goals_values) == len(costs), test_id_str
        for goal, goal_value, cost in zip(goals, goals_values, costs):
            _check_oracle_goal(pytest_test_case, goal, goal_value, cost, test_id_str)
    elif not is_sua_or_incr:
        with pytest_test_case.assertRaises(raised_class, msg=test_id_str):
            optimizer.lexicographic_optimize(goals)


def _test_pareto(pytest_test_case, optimizer, goals, goals_values, test_id_str, is_sua_or_incr):
    raised_class = _get_expected_raised_class(goals_values[0])
    assert raised_class is None or len(goals_values) == 1, f"test: {test_id_str}, goals_values: {goals_values}"
    if raised_class is None:
        retval = optimizer.pareto_optimize(goals)
        pytest_test_case.assertIsNotNone(retval, test_id_str)

        sorted_costs = sorted((costs for _, costs in retval), key=str)
        sorted_goals_values = sorted(goals_values, key=str)

        pytest_test_case.assertEqual(len(sorted_costs), len(sorted_goals_values), test_id_str)
        for costs, goals_values in zip(sorted_costs, sorted_goals_values):
            assert len(goals) == len(costs) == len(goals_values), test_id_str

            for goal, goal_value, cost in zip(goals, goals_values, costs):
                _check_oracle_goal(pytest_test_case, goal, goal_value, cost, test_id_str)
    elif not is_sua_or_incr:
        with pytest_test_case.assertRaises(raised_class, msg=test_id_str):
            optimizer.pareto_optimize(goals)


def _test_boxed(pytest_test_case, optimizer, goals, goals_values, test_id_str, test_basic, is_sua_or_incr):
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
        pytest_test_case.assertIsNotNone(retval, test_id_str)
        for goal, goal_value in zip(goals, goals_values):
            _, cost = retval[goal]
            _check_oracle_goal(pytest_test_case, goal, goal_value, cost, test_id_str)
    elif not is_sua_or_incr:
        with pytest_test_case.assertRaises(raised_class, msg=test_id_str):
            optimizer.boxed_optimize(goals)

    # test single optimizations separately
    if test_basic:
        for goal, goal_value in zip(goals, goals_values):
            _test_basic(pytest_test_case, optimizer, goal, goal_value, test_id_str, is_sua_or_incr)


def _test_basic(pytest_test_case, optimizer, goal, goal_value, test_id_str, is_sua_or_incr):
    raised_class = _get_expected_raised_class(goal_value)
    if raised_class is None:
        retval = optimizer.optimize(goal)
        pytest_test_case.assertIsNotNone(retval, test_id_str)
        _, cost = retval
        _check_oracle_goal(pytest_test_case, goal, goal_value, cost, test_id_str)
    elif not is_sua_or_incr:
        with pytest_test_case.assertRaises(raised_class, msg=test_id_str):
            optimizer.optimize(goal)


# Methods that create an OMTTestCase
def qf_lia_two_variables_multi_obj_example():
    x = Symbol("x", INT)
    y = Symbol("y", INT)

    int_0, int_3, int_4 = Int(0), Int(3), Int(4)

    x_boundaries = And(GE(x, int_0), LE(x, int_3))
    y_boundaries = And(GE(y, int_0), LE(y, int_3))

    x_plus_y_le_4 = LE(Plus(x, y), int_4)

    assertions = [x_boundaries, y_boundaries, x_plus_y_le_4]

    maximize_x = MaximizationGoal(x)
    maximize_y = MaximizationGoal(y)

    goals_dict = {}

    # lexicographic
    goals = (maximize_x, maximize_y)
    goal_values = [int_3, Int(1)]
    goals_dict[(goals, OptimizationTypes.LEXICOGRAPHIC)] = goal_values

    # pareto
    goal_values = [(int_3, Int(1)), (Int(2), Int(2)), (Int(1), int_3)]
    goals_dict[(goals, OptimizationTypes.PARETO)] = goal_values

    # boxed
    goal_values = [int_3, int_3]
    goals_dict[(goals, OptimizationTypes.BOXED)] = goal_values

    # basic
    goal_values = [int_3]
    goals_dict[((maximize_x, ), OptimizationTypes.BASIC)] = goal_values
    goals_dict[((maximize_y, ), OptimizationTypes.BASIC)] = goal_values

    return OMTTestCase(
        "QF_LIA 2 variables multiple objective",
        assertions,
        QF_LIA,
        True,
        goals_dict
    )


def qf_lia_2_int_2_bools_multiple_objective():
    x = Symbol("x", INT)
    y = Symbol("y", INT)

    r1 = Symbol("r1", BOOL)
    r2 = Symbol("r2", BOOL)

    int_0, int_3, int_4 = Int(0), Int(3), Int(4)

    x_boundaries = And(GE(x, int_0), LE(x, int_3))
    y_boundaries = And(GE(y, int_0), LE(y, int_3))

    x_plus_y_le_4 = LE(Plus(x, y), int_4)

    r1_or_r2 = Or(r1, r2)
    x_plus_y_le_2 = LE(Plus(x, y), Int(2))

    r1_implies_x_plus_y_le_4 = Implies(r1, x_plus_y_le_4)
    r2_implies_x_plus_y_le_2 = Implies(r2, x_plus_y_le_2)

    assertions = [x_boundaries, y_boundaries, r1_or_r2, r1_implies_x_plus_y_le_4, r2_implies_x_plus_y_le_2]

    maximize_x = MaximizationGoal(x)
    maximize_y = MaximizationGoal(y)

    goals_dict = {}

    # lexicographic
    goals = (maximize_x, maximize_y)
    goal_values = [int_3, Int(1)]
    goals_dict[(goals, OptimizationTypes.LEXICOGRAPHIC)] = goal_values

    # pareto
    goal_values = [(int_3, Int(1)), (Int(2), Int(2)), (Int(1), int_3)]
    goals_dict[(goals, OptimizationTypes.PARETO)] = goal_values

    # boxed
    goal_values = [int_3, int_3]
    goals_dict[(goals, OptimizationTypes.BOXED)] = goal_values

    # basic
    goal_values = [int_3]
    goals_dict[((maximize_x, ), OptimizationTypes.BASIC)] = goal_values
    goals_dict[((maximize_y, ), OptimizationTypes.BASIC)] = goal_values

    return OMTTestCase(
        "QF_LIA 2 int 2 bools multiple objective",
        assertions,
        QF_LIA,
        True,
        goals_dict
    )


def qf_lra_box_volume():
    length = Symbol("length_real", REAL)
    width = Symbol("width_real", REAL)
    height = Symbol("height_real", REAL)
    volume = Symbol("volume_real", REAL)

    # as a second objective, maximize y, with y inversely proportional to the volume
    x = Symbol("x_real", REAL)
    y = Symbol("y_real", REAL)

    height_times_2 = Times(height, Real(2.0))

    length_value = Minus(Real(36.0), height_times_2)
    width_value = Minus(Real(24.0), height_times_2)

    # volume_value = Times(length, width, height)
    # switch to sum in order to have a linear problem
    volume_value = Plus(length, width, height)

    length_formula = Equals(length, length_value)
    width_formula = Equals(width, width_value)
    volume_formula = Equals(volume, volume_value)

    positive_length = GE(length, Real(0.0))
    positive_width = GE(width, Real(0.0))
    minimum_height = GE(height, Real(2.0))

    line_1_constraint = Equals(x, y)
    line_2_constraint = Equals(y, Minus(height, x))

    assertions = [length_formula, width_formula, volume_formula, positive_length, positive_width, minimum_height, line_1_constraint, line_2_constraint]

    maximize_volume_goal = MaximizationGoal(volume)
    maximize_y_goal = MaximizationGoal(y)

    return OMTTestCase(
        "QF_LRA Box Volume",
        assertions,
        QF_LRA,
        True,
        {
            ((maximize_volume_goal, maximize_y_goal), OptimizationTypes.LEXICOGRAPHIC): [Real(54.0), Real(1.0)],
            ((maximize_volume_goal, maximize_y_goal), OptimizationTypes.BOXED): [Real(54.0), Real(6.0)],
        }
    )


def qf_lia_box_volume():
    length = Symbol("length", INT)
    width = Symbol("width", INT)
    height = Symbol("height", INT)
    volume = Symbol("volume", INT)

    # as a second objective, maximize y, with y inversely proportional to the volume
    x = Symbol("x", INT)
    y = Symbol("y", INT)

    height_times_2 = Times(height, Int(2))

    length_value = Minus(Int(36), height_times_2)
    width_value = Minus(Int(24), height_times_2)

    # volume_value = Times(length, width, height)
    # switch to sum in order to have a linear problem
    volume_value = Plus(length, width, height)

    length_formula = Equals(length, length_value)
    width_formula = Equals(width, width_value)
    volume_formula = Equals(volume, volume_value)

    positive_length = GE(length, Int(0))
    positive_width = GE(width, Int(0))
    minimum_height = GE(height, Int(2))

    line_1_constraint = Equals(x, y)
    line_2_constraint = Equals(y, Minus(height, x))

    assertions = [length_formula, width_formula, volume_formula, positive_length, positive_width, minimum_height, line_1_constraint, line_2_constraint]

    maximize_volume_goal = MaximizationGoal(volume)
    maximize_y_goal = MaximizationGoal(y)

    return OMTTestCase(
        "QF_LIA Box Volume",
        assertions,
        QF_LIA,
        True,
        {
            ((maximize_volume_goal, maximize_y_goal), OptimizationTypes.LEXICOGRAPHIC): [Int(54), Int(1)],
            ((maximize_volume_goal, maximize_y_goal), OptimizationTypes.PARETO): [
                # all the possible values of the pareto front
                (Int(60-6*h), Int(h))
                for h in range(1, 7)
            ],
            ((maximize_volume_goal, maximize_y_goal), OptimizationTypes.BOXED): [Int(54), Int(6)],
        }
    )


def test_maximize_revenue():
    cost_per_rented_car = Symbol("cost_per_rented_car", INT)
    numbers_of_car_rented = Symbol("numbers_of_car_rented", INT)
    revenue = Symbol("renevue", INT)

    numbers_of_car_rented_value = Minus(Int(1000), Times(Int(5), cost_per_rented_car))
    # revenue_value = Times(cost_per_rented_car, numbers_of_car_rented)
    # make it linear
    revenue_value = Plus(cost_per_rented_car, numbers_of_car_rented)

    cost_per_rented_car_boundaries = And(GE(cost_per_rented_car, Int(50)), LE(cost_per_rented_car, Int(200)))
    numbers_of_car_rented_formula = Equals(numbers_of_car_rented, numbers_of_car_rented_value)
    revenue_formula = Equals(revenue, revenue_value)

    length = Symbol("length", INT)
    width = Symbol("width", INT)
    area = Symbol("area", INT)
    perimeter = Symbol("perimeter", INT)

    # comment to make it linear
    # area_value = Times(length, width)
    width_times_2 = Times(width, Int(2))
    area_value = Plus(
        length,
        Ite(LE(width, Int(200)),
            width_times_2,
            Times(width_times_2, Int(-1))
        )
    )
    perimeter_value = Times(Plus(length, width), Int(2))

    area_formula = Equals(area, area_value)
    perimeter_formula = Equals(perimeter, perimeter_value)

    perimeter_boundaries = LE(perimeter, revenue)


    maximize_area_goal = MaximizationGoal(area)

    maximize_revenue_goal = MaximizationGoal(revenue)

    assertions = [cost_per_rented_car_boundaries, numbers_of_car_rented_formula, revenue_formula, area_formula, perimeter_formula, perimeter_boundaries]

    return OMTTestCase(
        "QF_LIA max revenue",
        assertions,
        QF_LIA,
        True,
        {
            ((maximize_revenue_goal, maximize_area_goal), OptimizationTypes.LEXICOGRAPHIC): [Int(800), Int(600)],
            ((maximize_revenue_goal, maximize_area_goal), OptimizationTypes.PARETO): [(Int(800), Int(600))],
            ((maximize_revenue_goal, maximize_area_goal), OptimizationTypes.BOXED): [Int(800), Int(600)],
        }
    )
