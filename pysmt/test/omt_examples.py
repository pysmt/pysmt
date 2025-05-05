from itertools import chain
import os.path as path

from pysmt.shortcuts import GE, Int, Symbol, INT, LE, REAL, Real, Equals, Times, Or,Ite
from pysmt.shortcuts import And, Plus, Minus, BOOL, Implies, get_env
from pysmt.logics import QF_LIA, QF_LRA
from pysmt.optimization.goal import MaximizationGoal
from pysmt.test.optimization_utils import OMTTestCase, OptimizationTypes
from pysmt.exceptions import PysmtValueError



test_folder = path.dirname(path.abspath(__file__))
omt_smt2_files_folder = path.join(test_folder, "smtlib", "omt")

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

    with environment:
        if fast and slow:
            return chain(_fast_examples(), _slow_examples())
        elif fast:
            return _fast_examples()
        elif slow:
            return _slow_examples()
        else:
            raise PysmtValueError(
                "If neither fast or slow are True this method returns no test cases"
            )


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
        goals_dict,
        get_env()
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
        goals_dict,
        get_env()
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
        },
        get_env()
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
        },
        get_env()
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
        },
        get_env()
    )
