from enum import Enum, auto

from pysmt.environment import get_env
from pysmt.optimization.goal import Goal
from pysmt.logics import Logic
from pysmt.fnode import FNode
from pysmt.shortcuts import Optimizer, GE, Int, Symbol, INT, LE, GT, REAL, Real, Equals, Times, Solver, Or, Div
from pysmt.shortcuts import BVType, BVUGE, BVSGE, BVULE, BVSLE, BVUGT, BVSGT, BVULT, BVSLT, BVZero, BVOne, BV
from pysmt.shortcuts import And, Plus, Minus, get_env
from pysmt.logics import QF_LIA, QF_LRA, QF_BV, QF_NRA, QF_NIA
from pysmt.optimization.goal import MaximizationGoal, MinimizationGoal, \
    MinMaxGoal, MaxMinGoal, MaxSMTGoal

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
    # goals: Optional[Dict[Tuple[Tuple[Goal, ...], OptimizationTypes], List[Union[FNode, List[FNode]]]]]
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
                assert len(goals_oracle_values) == goals_number, f"In {optimization_type.name} optimization the number of goals values must be the same of the number of the given goals"
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

    omt_examples = []
    if environment is None:
        environment = get_env()


    with environment:
        # QF_LIA
        x = Symbol("x", INT)
        y = Symbol("y", INT)

        int_0, int_3, int_4 = Int(0), Int(3), Int(4)

        x_boundaries = And(GE(x, int_0), LE(x, int_3))
        y_boundaries = And(GE(y, int_0), LE(y, int_3))

        x_y_bound = LE(Plus(x, y), int_4)

        assertions = [x_boundaries, y_boundaries, x_y_bound]

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

        omt_examples.append(
            OMTTestCase(
                "QF_LIA 2 variables multiple objective",
                assertions,
                QF_LIA,
                True,
                goals_dict
            )
        )



    return omt_examples
