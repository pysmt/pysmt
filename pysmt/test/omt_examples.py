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

        omt_examples.append(
            OMTTestCase(
                "QF_LIA 2 variables multiple objective",
                assertions,
                QF_LIA,
                True,
                goals_dict
            )
        )

        r1 = Symbol("r1", BOOL)
        r2 = Symbol("r2", BOOL)

        r1_or_r2 = Or(r1, r2)
        x_plus_y_le_2 = LE(Plus(x, y), Int(2))

        r1_implies_x_plus_y_le_4 = Implies(r1, x_plus_y_le_4)
        r2_implies_x_plus_y_le_2 = Implies(r2, x_plus_y_le_2)

        assertions = [x_boundaries, y_boundaries, r1_or_r2, r1_implies_x_plus_y_le_4, r2_implies_x_plus_y_le_2]

        omt_examples.append(
            OMTTestCase(
                "QF_LIA 2 int 2 bools multiple objective",
                assertions,
                QF_LIA,
                True,
                goals_dict
            )
        )

        parser = SmtLib20Parser()
        file_name = "smtlib2_allsat.smt2" # TODO change this with bz2 compression before PR is ready
        script = parser.get_script_fname(path.join(omt_smt2_files_folder, file_name))
        assumptions, parsed_goals = _extract_assumptions_and_objectives(script, file_name)

        expected_goals = (maximize_x, maximize_y)

        assert str(parsed_goals) == str(expected_goals), f"Wrong goals parsed from {file_name}: {parsed_goals}, {(maximize_x, maximize_y)}"

        goals_dict = {}

        # lexicographic
        goal_values = [Int(100), Int(100)]
        goals_dict[(goals, OptimizationTypes.LEXICOGRAPHIC)] = goal_values

        # pareto
        goal_values = [(Int(100), Int(100))]
        goals_dict[(goals, OptimizationTypes.PARETO)] = goal_values

        # boxed
        goal_values = [Int(100), Int(100)]
        goals_dict[(goals, OptimizationTypes.BOXED)] = goal_values

        # basic
        goal_values = [Int(100)]
        goals_dict[((maximize_x, ), OptimizationTypes.BASIC)] = goal_values
        goals_dict[((maximize_y, ), OptimizationTypes.BASIC)] = goal_values

        omt_examples.append(
            OMTTestCase(
                f"QF_LIA - {file_name}",
                assumptions,
                QF_LIA,
                True,
                goals_dict
            )
        )

        # QF_LRA
        parser = SmtLib20Parser()
        file_name = "smtlib2_boxed.smt2" # TODO change this with bz2 compression before PR is ready
        script = parser.get_script_fname(path.join(omt_smt2_files_folder, file_name))
        assumptions, parsed_goals = _extract_assumptions_and_objectives(script, file_name)

        real_x = Symbol("real_x", REAL)
        real_y = Symbol("real_y", REAL)
        real_z = Symbol("real_z", REAL)

        minimize_real_x = MinimizationGoal(real_x)
        maximize_real_y = MaximizationGoal(real_y)
        maximize_real_z = MaximizationGoal(real_z)

        goals = (minimize_real_x, maximize_real_y, maximize_real_z)

        assert str(parsed_goals) == str(goals), f"Wrong goals parsed from {file_name}: {parsed_goals}, {(maximize_x, maximize_y)}"

        goals_dict = {}

        real_42, real_24 = Real(42.0), Real(24.0)

        # # lexicographic
        # goal_values = [real_42, real_42, real_24]
        # goals_dict[(goals, OptimizationTypes.LEXICOGRAPHIC)] = goal_values

        # # pareto
        # goal_values = [(bv_8_8_constant, bv_8_8_constant), (bv_minus_105_8_constant, bv_minus_105_8_constant)]
        # goals_dict[(goals, OptimizationTypes.PARETO)] = goal_values

        # boxed
        goal_values =  [real_42, real_42, real_24]
        goals_dict[(goals, OptimizationTypes.BOXED)] = goal_values

        # basic
        goal_values = [real_42]
        goals_dict[((minimize_real_x, ), OptimizationTypes.BASIC)] = goal_values
        goal_values = [real_42]
        goals_dict[((maximize_real_y, ), OptimizationTypes.BASIC)] = goal_values
        goal_values = [real_24]
        goals_dict[((maximize_real_z, ), OptimizationTypes.BASIC)] = goal_values

        # TODO decomment after understanding how to handle unbound objectives
        # omt_examples.append(
        #     OMTTestCase(
        #         f"QF_LRA - {file_name}",
        #         assumptions,
        #         QF_LRA,
        #         True,
        #         goals_dict
        #     )
        # )

        # QF_BV
        parser = SmtLib20Parser()
        file_name = "smtlib2_bitvector.smt2" # TODO change this with bz2 compression before PR is ready
        script = parser.get_script_fname(path.join(omt_smt2_files_folder, file_name))
        assumptions, parsed_goals = _extract_assumptions_and_objectives(script, file_name)

        bv_8 = Symbol("bv_8", BVType(8))

        minimize_bv_8_unsigned = MinimizationGoal(bv_8)
        minimize_bv_8_signed = MinimizationGoal(bv_8, True)

        goals = (minimize_bv_8_unsigned, minimize_bv_8_signed)

        assert str(parsed_goals) == str(goals), f"Wrong goals parsed from {file_name}: {parsed_goals}, {(maximize_x, maximize_y)}"

        goals_dict = {}

        bv_8_8_constant = BV(8, 8)
        bv_minus_105_8_constant = SBV(-105, 8)

        # lexicographic
        goal_values = [bv_8_8_constant, bv_8_8_constant]
        goals_dict[(goals, OptimizationTypes.LEXICOGRAPHIC)] = goal_values

        # pareto
        goal_values = [(bv_8_8_constant, bv_8_8_constant), (bv_minus_105_8_constant, bv_minus_105_8_constant)]
        goals_dict[(goals, OptimizationTypes.PARETO)] = goal_values

        # boxed
        goal_values = [bv_8_8_constant, bv_minus_105_8_constant]
        goals_dict[(goals, OptimizationTypes.BOXED)] = goal_values

        # basic
        goal_values = [bv_8_8_constant]
        goals_dict[((minimize_bv_8_unsigned, ), OptimizationTypes.BASIC)] = goal_values
        goal_values = [bv_minus_105_8_constant]
        goals_dict[((minimize_bv_8_signed, ), OptimizationTypes.BASIC)] = goal_values

        omt_examples.append(
            OMTTestCase(
                f"QF_BV - {file_name}",
                assumptions,
                QF_BV,
                True,
                goals_dict
            )
        )
        # TODO notice: boxed can also represent basic with different calls
        (QF_LIA, "small_set/QF_LIA/prp-23-47.smt2.bz2", SAT/UNSAT, {BOXED: (7, 8, 4, 5), LEX: "unbound"}),

    return omt_examples

def _extract_assumptions_and_objectives(script, file_name):
    check_sat_found = False
    goals = []
    assumptions = [script.get_last_formula()]
    for command in script.commands:
        if command.name == CHECK_SAT:
            assert not check_sat_found, f"Multiple check-sat commands found in file {file_name}"
            check_sat_found = True
        elif command.name in (MAXIMIZE, MINIMIZE):
            goals.append(_parse_goal(command))
        elif command.name == CHECK_ALLSAT:
            # TODO understand if this is the correct interpretation
            assumptions.extend(command.args)
    if not check_sat_found:
        raise ValueError("No check-sat command found in the script")

    return assumptions, tuple(goals)


def _parse_goal(command):
    assert len(command.args) == 2, f"Command {command.name} must have 2 arguments"
    if command.name == MAXIMIZE:
        goal_type = MaximizationGoal
    elif command.name == MINIMIZE:
        goal_type = MinimizationGoal
    else:
        raise ValueError(f"Unknown goal command {command.name}")

    return goal_type(command.args[0])
