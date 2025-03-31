from enum import Enum, auto
import os.path as path

from pysmt.environment import get_env
from pysmt.optimization.goal import Goal
from pysmt.logics import Logic
from pysmt.fnode import FNode
from pysmt.shortcuts import Optimizer, GE, Int, Symbol, INT, LE, GT, REAL, Real, Equals, Times, Solver, Or, Div
from pysmt.shortcuts import BVType, BVUGE, BVSGE, BVULE, BVSLE, BVUGT, BVSGT, BVULT, BVSLT, BVZero, BVOne, BV
from pysmt.shortcuts import And, Plus, Minus, get_env, BOOL, Implies, SBV
from pysmt.logics import QF_LIA, QF_LRA, QF_BV, QF_NRA, QF_NIA
from pysmt.optimization.goal import MaximizationGoal, MinimizationGoal, \
    MinMaxGoal, MaxMinGoal, MaxSMTGoal
from pysmt.smtlib.script import InterpreterOMT
from pysmt.smtlib.parser.parser import SmtLib20Parser
from pysmt.smtlib.commands import ASSERT, CHECK_SAT, CHECK_ALLSAT, MAXIMIZE, MINIMIZE


test_folder = path.dirname(path.abspath(__file__))
omt_smt2_files_folder = path.join(test_folder, "smtlib", "omt")

class OptimizationTypes(Enum):
    BASIC = auto()
    LEXICOGRAPHIC = auto()
    PARETO = auto()
    BOXED = auto()


class OMTTestCase:
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


def get_full_example_omt_formuale(environment=None):
    """Return a list of OMTTestCases using the given environment."""

    if environment is None:
        environment = get_env()

    with environment:
        omt_examples = [
            qf_lia_two_variables_multi_obj_example(),
            qf_lia_2_int_2_bools_multiple_objective(),
        ]
    return omt_examples


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
