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

import warnings
from collections import defaultdict, namedtuple
from collections.abc import Iterator
from io import StringIO, TextIOWrapper
from typing import Any, Optional, TextIO

import pysmt
import pysmt.smtlib.commands as smtcmd
from pysmt.environment import get_env
from pysmt.exceptions import (
    NoLogicAvailableError,
    PysmtValueError,
    UndefinedLogicError,
    UnknownSmtLibCommandError,
)
from pysmt.fnode import FNode
from pysmt.formula import FormulaManager
from pysmt.logics import SMTLIB2_LOGICS, Logic, get_closer_smtlib_logic
from pysmt.optimization.goal import (
    Goal,
    MaximizationGoal,
    MaxMinGoal,
    MaxSMTGoal,
    MinimizationGoal,
    MinMaxGoal,
)
from pysmt.optimization.optimizer import Optimizer
from pysmt.oracles import get_logic
from pysmt.smtlib.annotations import Annotations
from pysmt.smtlib.printers import SmtDagPrinter, SmtPrinter, quote
from pysmt.solvers.smtlib import SmtLibSolver
from pysmt.solvers.solver import Model
from pysmt.typing import _TypeDecl

PrinterType = SmtPrinter | SmtDagPrinter


def check_sat_filter(
    log: list[tuple[str, Model | bool | Goal | list[tuple[FNode, FNode]] | None]],
) -> bool:
    """
    Returns the result of the check-sat command from a log.

    Raises errors in case a unique check-sat command cannot be located.
    """
    filtered = [(x, y) for x, y in log if x == smtcmd.CHECK_SAT]
    assert len(filtered) == 1
    retval = filtered[0][1]
    assert isinstance(retval, bool)
    return retval


class SmtLibCommand(namedtuple("SmtLibCommand", ["name", "args"])):
    def serialize(
        self,
        outstream: TextIO | None = None,
        printer: PrinterType | None = None,
        daggify: bool = True,
        env=None,
    ):
        """Serializes the SmtLibCommand into outstream using the given printer.

        Exactly one of outstream or printer must be specified. When
        specifying the printer, the associated outstream will be used.
        If printer is not specified, daggify controls the printer to
        be created. If true a daggified formula is produced, otherwise
        a tree printing is done.

        """

        if (outstream is None) and (printer is not None):
            outstream = printer.stream
        elif (outstream is not None) and (printer is None):
            if daggify:
                printer = SmtDagPrinter(outstream, env=env)
            else:
                printer = SmtPrinter(outstream, env=env)
        else:
            assert (outstream is not None and printer is not None) or (
                outstream is None and printer is None
            ), "Exactly one of outstream and printer must be set."
        assert outstream is not None and printer is not None

        if self.name == smtcmd.SET_OPTION:
            outstream.write(f"({self.name} {self.args[0]} {self.args[1]})")

        elif self.name == smtcmd.SET_INFO:
            outstream.write(f"({self.name} {self.args[0]} {quote(self.args[1])})")

        elif self.name == smtcmd.ASSERT:
            outstream.write(f"({self.name} ")
            printer.printer(self.args[0])
            outstream.write(")")

        elif self.name == smtcmd.ASSERT_SOFT:
            outstream.write(f"({self.name} ")
            printer.printer(self.args[0])
            for a in self.args[1]:
                option_name, value = a
                if option_name == ":weight":
                    outstream.write(f" {option_name} ")
                    printer.printer(value)
                else:
                    outstream.write(f" {option_name} {value}")
            outstream.write(")")

        elif self.name == smtcmd.GET_VALUE:
            outstream.write(f"({self.name} (")
            for a in self.args:
                printer.printer(a)
                outstream.write(" ")
            outstream.write("))")

        elif self.name in [smtcmd.MAXIMIZE, smtcmd.MINIMIZE]:
            outstream.write(f"({self.name} ")
            printer.printer(self.args[0])
            for a in self.args[1]:
                option_name, value = a
                if option_name != ":signed":
                    outstream.write(f" {option_name} {value}")
                else:
                    outstream.write(f" {option_name} ")
            outstream.write(")")

        elif self.name in [smtcmd.MINMAX, smtcmd.MAXMIN]:
            outstream.write(f"({self.name}")
            for a in self.args[0]:
                outstream.write(" ")
                printer.printer(a)
            for option_name, value in self.args[1] or []:
                if option_name == ":signed":
                    if value:
                        outstream.write(f" {option_name}")
                else:
                    outstream.write(f" {option_name} {value}")
            outstream.write(")")

        elif self.name == smtcmd.CHECK_ALLSAT:
            outstream.write(f"({self.name} ")
            if self.args:
                outstream.write("(")
                for expr in self.args[:-1]:
                    printer.printer(expr)
                    outstream.write(" ")
                printer.printer(self.args[-1])
                outstream.write(")")
            outstream.write(")")

        elif self.name in [
            smtcmd.CHECK_SAT,
            smtcmd.EXIT,
            smtcmd.RESET_ASSERTIONS,
            smtcmd.GET_UNSAT_CORE,
            smtcmd.GET_ASSIGNMENT,
            smtcmd.GET_MODEL,
            smtcmd.GET_OBJECTIVES,
        ]:
            outstream.write(f"({self.name})")

        elif self.name == smtcmd.SET_LOGIC:
            outstream.write(f"({self.name} {self.args[0]})")

        elif self.name in [smtcmd.DECLARE_FUN, smtcmd.DECLARE_CONST]:
            symbol = self.args[0]
            type_str = symbol.symbol_type().as_smtlib()
            outstream.write(f"({self.name} {quote(symbol.symbol_name())} {type_str})")

        elif self.name == smtcmd.DEFINE_FUN:
            name = self.args[0]
            params_list = self.args[1]
            params = " ".join(
                [
                    f"({v} {v.symbol_type().as_smtlib(funstyle=False)})"
                    for v in params_list
                ]
            )
            rtype = self.args[2]
            expr = self.args[3]
            outstream.write(
                f"({self.name} {name} ({params}) {rtype.as_smtlib(funstyle=False)} "
            )
            printer.printer(expr)
            outstream.write(")")

        elif self.name in [smtcmd.PUSH, smtcmd.POP, smtcmd.LOAD_OBJECTIVE_MODEL]:
            outstream.write(f"({self.name} {self.args[0]})")

        elif self.name == smtcmd.DEFINE_SORT:
            name = self.args[0]
            params_list = self.args[1]
            params = " ".join(x.as_smtlib(funstyle=False) for x in params_list)
            rtype = self.args[2]
            outstream.write(
                f"({self.name} {name} ({params}) {rtype.as_smtlib(funstyle=False)})"
            )
        elif self.name == smtcmd.DECLARE_SORT:
            type_decl = self.args[0]
            outstream.write(f"({self.name} {type_decl.name} {type_decl.arity})")

        elif self.name in smtcmd.ALL_COMMANDS:
            raise NotImplementedError(
                f"'{self.name}' is a valid SMT-LIB command "
                "but it is currently not supported. "
                "Please open a bug-report."
            )
        else:
            raise UnknownSmtLibCommandError(self.name)

    def serialize_to_string(self, daggify: bool = True, env=None) -> str:
        buf = StringIO()
        self.serialize(buf, daggify=daggify, env=env)
        return buf.getvalue()


class SmtLibScript:
    def __init__(self):
        self.annotations: Annotations | None = None
        self.commands: list[SmtLibCommand] = []

    def add(self, name: str, args: list[Logic | _TypeDecl | FNode | str | None]):
        """Adds a new SmtLibCommand with the given name and arguments."""
        self.add_command(SmtLibCommand(name=name, args=args))

    def add_command(self, command: SmtLibCommand):
        self.commands.append(command)

    def evaluate(
        self, solver: SmtLibSolver
    ) -> list[tuple[str, Model | bool | Goal | list[tuple[FNode, FNode]] | None]]:
        log = []
        inter = InterpreterOMT()
        for cmd in self.commands:
            r = inter.evaluate(cmd, solver)
            log.append((cmd.name, r))

        return log

    def contains_command(self, command_name: str) -> bool:
        return any(x.name == command_name for x in self.commands)

    def count_command_occurrences(self, command_name: str) -> int:
        return sum(1 for cmd in self.commands if cmd.name == command_name)

    def filter_by_command_name(self, command_name_set: list[str]) -> Iterator[Any]:
        return (cmd for cmd in self.commands if cmd.name in command_name_set)

    def get_strict_formula(
        self, mgr: Optional["pysmt.formula.FormulaManager"] = None
    ) -> FNode:
        if self.contains_command(smtcmd.PUSH) or self.contains_command(smtcmd.POP):
            raise PysmtValueError("Was not expecting push-pop commands")
        if self.count_command_occurrences(smtcmd.CHECK_SAT) != 1:
            raise PysmtValueError("Was expecting exactly one check-sat command")
        _And = mgr.And if mgr else get_env().formula_manager.And

        assertions = [
            cmd.args[0] for cmd in self.filter_by_command_name([smtcmd.ASSERT])
        ]
        return _And(assertions)

    def get_declared_symbols(self) -> set[FNode]:
        return {
            cmd.args[0]
            for cmd in self.filter_by_command_name(
                [smtcmd.DECLARE_CONST, smtcmd.DECLARE_FUN]
            )
        }

    def get_define_fun_parameter_symbols(self) -> set[FNode]:
        res = set()
        for cmd in self.filter_by_command_name([smtcmd.DEFINE_FUN]):
            for s in cmd.args[1]:
                res.add(s)
        return res

    def get_last_formula(
        self, mgr: FormulaManager | None = None, return_optimizations: bool = False
    ) -> Any:
        """Returns the last formula of the execution of the Script.

        This coincides with the conjunction of the assertions that are
        left on the assertion stack at the end of the SMTLibScript.

        If the parameter `return_optimizations` is set to `True` the method will
        return a couple where the first element is the last formula of the
        script and the second element is the tuple containing the last goals
        defined.
        """
        stack: list[FNode] = []
        backtrack: list[int] = []
        goals: list[Goal] = []
        goals_backtrack: list[int] = []
        max_smt_goals: dict[str | None, tuple[int, MaxSMTGoal]] = {}
        max_smt_goals_backtrack: dict[str | None, list[int]] = defaultdict(list)
        if mgr is None:
            mgr = get_env().formula_manager

        for cmd in self.commands:
            if cmd.name == smtcmd.ASSERT:
                stack.append(cmd.args[0])
            if cmd.name == smtcmd.RESET_ASSERTIONS:
                stack = []
                backtrack = []
                goals = []
                goals_backtrack = []
                max_smt_goals = {}
                max_smt_goals_backtrack = defaultdict(list)
            elif cmd.name == smtcmd.PUSH:
                for _ in range(cmd.args[0]):
                    backtrack.append(len(stack))
                    goals_backtrack.append(len(goals))
                    for k, (_, goal) in max_smt_goals.items():
                        max_smt_goals_backtrack[k].append(len(goal.soft))
            elif cmd.name == smtcmd.POP:
                for _ in range(cmd.args[0]):
                    l = backtrack.pop()
                    stack = stack[:l]
                    l = goals_backtrack.pop()
                    goals = goals[:l]
                    # a max_smt_goal might be removed from the goals completely with the pop
                    # so we remove it from the dict, otherwise we can just remove the
                    # last l elements from the list of formulae
                    goals_to_remove = []
                    for k, (goal_position, goal) in max_smt_goals.items():
                        if goal_position >= len(goals):
                            goals_to_remove.append(k)
                        else:
                            l = max_smt_goals_backtrack[k].pop()
                            goal.soft = goal.soft[:l]
                    for k in goals_to_remove:
                        del max_smt_goals[k]
                        del max_smt_goals_backtrack[k]
            elif cmd.name == smtcmd.MAXIMIZE:
                goals.append(
                    MaximizationGoal(cmd.args[0], _command_is_signed(cmd), env=mgr.env)
                )
            elif cmd.name == smtcmd.MINIMIZE:
                goals.append(
                    MinimizationGoal(cmd.args[0], _command_is_signed(cmd), env=mgr.env)
                )
            elif cmd.name == smtcmd.MINMAX:
                goals.append(
                    MinMaxGoal(cmd.args[0], _command_is_signed(cmd), env=mgr.env)
                )
            elif cmd.name == smtcmd.MAXMIN:
                goals.append(
                    MaxMinGoal(cmd.args[0], _command_is_signed(cmd), env=mgr.env)
                )
            elif cmd.name == smtcmd.ASSERT_SOFT:
                formula = cmd.args[0]
                cmd_annotations = dict(cmd.args[1])
                max_smt_id = cmd_annotations.get(":id", "")
                max_smt_weight = cmd_annotations.get(":weight", mgr.Int(1))
                _, goal = max_smt_goals.setdefault(
                    max_smt_id, (len(goals), MaxSMTGoal(env=mgr.env))
                )
                goal.add_soft_clause(formula, max_smt_weight)
                # if len(goal.soft) > 1 the goal is already in goals
                if len(goal.soft) == 1:
                    goals.append(goal)

        if return_optimizations:
            return mgr.And(stack), tuple(goals)
        return mgr.And(stack)

    def to_file(self, fname, daggify=True, env=None):
        with open(fname, "w") as outstream:
            self.serialize(outstream, daggify=daggify, env=env)

    def serialize(
        self, outstream: TextIOWrapper | StringIO, daggify: bool = True, env=None
    ):
        """Serializes the SmtLibScript expanding commands"""
        if daggify:
            printer: PrinterType = SmtDagPrinter(
                outstream, env=env, annotations=self.annotations
            )
        else:
            printer = SmtPrinter(outstream, env=env, annotations=self.annotations)

        for cmd in self.commands:
            cmd.serialize(printer=printer, env=env)
            outstream.write("\n")

    def __len__(self) -> int:
        return len(self.commands)

    def __iter__(self):
        return iter(self.commands)

    def __str__(self):
        return "\n".join(str(cmd) for cmd in self.commands)


def _command_is_signed(command: SmtLibCommand) -> bool:
    singed = False
    if len(command.args) >= 2:
        options = command.args[1]
        if options is not None:
            for arg in options:
                if arg[0] == ":signed":
                    singed = arg[1]
                    if not isinstance(singed, bool):
                        raise PysmtValueError(
                            f":signed annotation to a command must be a bool, {singed!s} is not"
                        )
                break
    return singed


def smtlibscript_from_formula(
    formula: FNode, logic: str | int | Logic | None = None, env=None
) -> SmtLibScript:
    script = SmtLibScript()
    if env is None:
        env = get_env()

    if logic is None:
        # Get the simplest SmtLib logic that contains the formula
        f_logic = get_logic(formula, env=env)

        smt_logic: Logic | str | None = None
        try:
            smt_logic = get_closer_smtlib_logic(f_logic)
        except NoLogicAvailableError:
            warnings.warn(
                f"The logic {f_logic} is not reducible to any SMTLib2 "
                "standard logic. Proceeding with non-standard "
                f"logic '{f_logic}'",
                stacklevel=3,
            )
            smt_logic = f_logic
    elif not isinstance(logic, (Logic, str)):
        raise UndefinedLogicError(str(logic))
    else:
        if logic not in SMTLIB2_LOGICS:
            warnings.warn(
                f"The logic {logic} is not reducible to any SMTLib2 "
                "standard logic. Proceeding with non-standard "
                f"logic '{logic}'",
                stacklevel=3,
            )
        smt_logic = logic

    script.add(name=smtcmd.SET_LOGIC, args=[smt_logic])

    # Declare all types
    types = env.typeso.get_types(formula, custom_only=True)
    for type_ in types:
        script.add(name=smtcmd.DECLARE_SORT, args=[type_.decl])

    deps = env.fvo.get_free_variables(formula)
    # Declare all variables
    for symbol in deps:
        assert symbol.is_symbol()
        script.add(name=smtcmd.DECLARE_FUN, args=[symbol])

    # Assert formula
    script.add_command(SmtLibCommand(name=smtcmd.ASSERT, args=[formula]))
    # check-sat
    script.add_command(SmtLibCommand(name=smtcmd.CHECK_SAT, args=[]))
    return script


class InterpreterSMT:
    def evaluate(
        self, cmd: SmtLibCommand, solver: SmtLibSolver
    ) -> Model | bool | Goal | list[tuple[FNode, FNode]] | None:
        return self._smt_evaluate(cmd, solver)

    def _smt_evaluate(
        self, cmd: SmtLibCommand, solver: SmtLibSolver
    ) -> Model | bool | Goal | list[tuple[FNode, FNode]] | None:
        if cmd.name == smtcmd.SET_INFO:
            return solver.set_info(cmd.args[0], cmd.args[1])

        if cmd.name == smtcmd.SET_OPTION:
            opt = cmd.args[0]
            if opt[0] == ":":
                opt = opt[1:]
            return solver.set_option(opt, cmd.args[1])

        elif cmd.name == smtcmd.ASSERT:
            return solver.assert_(cmd.args[0])

        elif cmd.name == smtcmd.CHECK_SAT:
            return solver.check_sat()

        elif cmd.name == smtcmd.RESET_ASSERTIONS:
            return solver.reset_assertions()

        elif cmd.name == smtcmd.GET_VALUE:
            return solver.get_values(cmd.args)

        elif cmd.name == smtcmd.PUSH:
            return solver.push(cmd.args[0])

        elif cmd.name == smtcmd.POP:
            return solver.pop(cmd.args[0])

        elif cmd.name == smtcmd.EXIT:
            solver.exit()
            return None

        elif cmd.name == smtcmd.SET_LOGIC:
            name = cmd.args[0]
            return solver.set_logic(name)

        elif cmd.name == smtcmd.DECLARE_FUN:
            return solver.declare_fun(cmd.args[0])

        elif cmd.name == smtcmd.DECLARE_CONST:
            return solver.declare_const(cmd.args[0])

        elif cmd.name == smtcmd.DEFINE_FUN:
            (var, formals, typename, body) = cmd.args
            return solver.define_fun(var, formals, typename, body)

        elif cmd.name == smtcmd.ECHO:
            return cmd.args[0]

        elif cmd.name == smtcmd.CHECK_SAT_ASSUMING:
            return solver.check_sat(cmd.args)

        elif cmd.name == smtcmd.GET_MODEL:
            return solver.get_model()

        elif cmd.name == smtcmd.DECLARE_SORT:
            name = cmd.args[0].name
            arity = cmd.args[0].arity
            return solver.declare_sort(name, arity)

        elif cmd.name == smtcmd.GET_UNSAT_CORE:
            return solver.get_unsat_core()

        elif cmd.name in smtcmd.ALL_COMMANDS:
            raise NotImplementedError(
                f"'{cmd.name}' is a valid SMT-LIB command "
                "but it is currently not supported. "
                "Please open a bug-report."
            )
        else:
            raise UnknownSmtLibCommandError(cmd.name)


class InterpreterOMT(InterpreterSMT):
    def __init__(self):
        self.optimization_goals: tuple[list[Goal], list[tuple[FNode, FNode]]] = ([], [])
        self.opt_priority = "single-obj"

    def evaluate(
        self, cmd: SmtLibCommand, solver: SmtLibSolver
    ) -> Model | bool | Goal | list[tuple[FNode, FNode]] | None:
        return self._omt_evaluate(cmd, solver)

    def _omt_evaluate(
        self, cmd: SmtLibCommand, optimizer: SmtLibSolver
    ) -> Model | bool | Goal | list[tuple[FNode, FNode]] | None:
        if cmd.name == smtcmd.SET_OPTION:
            if cmd.args[0] == ":opt.priority":
                self.opt_priority = cmd.args[1]
            return None

        elif cmd.name == smtcmd.MAXIMIZE:
            g: Goal = MaximizationGoal(cmd.args[0], env=optimizer.environment)
            self.optimization_goals[0].append(g)
            return g

        elif cmd.name == smtcmd.MINIMIZE:
            g = MinimizationGoal(cmd.args[0], env=optimizer.environment)
            self.optimization_goals[0].append(g)
            return g

        elif cmd.name == smtcmd.CHECK_SAT:
            if len(self.optimization_goals[0]) == 0:
                # If there are no optimization objectives, then we default to normal SMT check-sat
                return self._smt_evaluate(cmd, optimizer)

            assert isinstance(optimizer, Optimizer)
            self.optimization_goals[1].clear()
            rt = False
            if self.opt_priority == "single-obj":
                rt = True
                for g in self.optimization_goals[0]:
                    solver_res = optimizer.optimize(g)
                    if solver_res is None:
                        rt = False
                        break
                    self.optimization_goals[1].append((g.term(), solver_res[1]))

            elif self.opt_priority == "pareto":
                assert isinstance(optimizer, Optimizer)
                for _model, values in optimizer.pareto_optimize(
                    self.optimization_goals[0]
                ):
                    rt = True
                    for g, v in zip(self.optimization_goals[0], values, strict=True):
                        self.optimization_goals[1].append((g.term(), v))

            elif self.opt_priority == "box":
                assert isinstance(optimizer, Optimizer)
                boxed_results = optimizer.boxed_optimize(self.optimization_goals[0])
                if boxed_results is not None:
                    rt = True
                    for g in self.optimization_goals[0]:
                        self.optimization_goals[1].append(
                            (g.term(), boxed_results[g][1])
                        )

            elif self.opt_priority == "lex":
                assert isinstance(optimizer, Optimizer)
                lex_results = optimizer.lexicographic_optimize(
                    self.optimization_goals[0]
                )
                if lex_results is not None:
                    _, values = lex_results
                    rt = True
                    for g, v in zip(self.optimization_goals[0], values, strict=True):
                        self.optimization_goals[1].append((g.term(), v))
            return rt

        elif cmd.name == smtcmd.MAXMIN:
            g = MaxMinGoal(cmd.args[0], env=optimizer.environment)
            self.optimization_goals[0].append(g)
            return g

        elif cmd.name == smtcmd.MINMAX:
            g = MinMaxGoal(cmd.args[0], env=optimizer.environment)
            self.optimization_goals[0].append(g)
            return g

        elif cmd.name == smtcmd.GET_OBJECTIVES:
            return self.optimization_goals[1]

        else:
            return self._smt_evaluate(cmd, optimizer)
