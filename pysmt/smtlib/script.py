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
from io import TextIOWrapper, StringIO
from typing import Any, Dict, Iterator, List, Optional, Set, TextIO, Tuple, Union

import pysmt
import pysmt.smtlib.commands as smtcmd
from pysmt.smtlib.annotations import Annotations
from pysmt.exceptions import (UnknownSmtLibCommandError, NoLogicAvailableError,
                              UndefinedLogicError, PysmtValueError)
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter, quote
from pysmt.optimization.optimizer import Optimizer
from pysmt.oracles import get_logic
from pysmt.logics import get_closer_smtlib_logic, Logic, SMTLIB2_LOGICS
from pysmt.environment import get_env
from pysmt.optimization.goal import MaximizationGoal, MinimizationGoal, MinMaxGoal, MaxMinGoal, MaxSMTGoal, Goal
from pysmt.typing import _TypeDecl
from pysmt.fnode import FNode
from pysmt.formula import FormulaManager
from pysmt.solvers.smtlib import SmtLibSolver
from pysmt.solvers.solver import Solver, Model

PrinterType = Union[SmtPrinter, SmtDagPrinter]

def check_sat_filter(log: List[Tuple[str, Optional[Union[Model, bool, Goal, List[Tuple[FNode, FNode]]]]]]) -> bool:
    """
    Returns the result of the check-sat command from a log.

    Raises errors in case a unique check-sat command cannot be located.
    """
    filtered = [(x,y) for x,y in log if x == smtcmd.CHECK_SAT]
    assert len(filtered) == 1
    retval = filtered[0][1]
    assert isinstance(retval, bool)
    return retval


class SmtLibCommand(namedtuple('SmtLibCommand', ['name', 'args'])):
    def serialize(self, outstream: Optional[TextIO]=None, printer: Optional[PrinterType]=None, daggify: bool=True):
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
                printer = SmtDagPrinter(outstream)
            else:
                printer = SmtPrinter(outstream)
        else:
            assert (outstream is not None and printer is not None) or \
                   (outstream is None and printer is None), \
                   "Exactly one of outstream and printer must be set."
        assert outstream is not None and printer is not None

        if self.name == smtcmd.SET_OPTION:
            outstream.write("(%s %s %s)" % (self.name,self.args[0],self.args[1]))

        elif self.name == smtcmd.SET_INFO:
            outstream.write("(%s %s %s)" % (self.name,self.args[0],
                                            quote(self.args[1])))

        elif self.name == smtcmd.ASSERT:
            outstream.write("(%s " % self.name)
            printer.printer(self.args[0])
            outstream.write(")")

        elif self.name == smtcmd.ASSERT_SOFT:
            outstream.write("(%s " % self.name)
            printer.printer(self.args[0])
            for a in self.args[1]:
                option_name, value = a
                if option_name == ":weight":
                    outstream.write(" %s " % option_name)
                    printer.printer(value)
                else:
                    outstream.write(" %s %s" % (option_name, value))
            outstream.write(")")

        elif self.name == smtcmd.GET_VALUE:
            outstream.write("(%s (" % self.name)
            for a in self.args:
                printer.printer(a)
                outstream.write(" ")
            outstream.write("))")

        elif self.name in [smtcmd.MAXIMIZE, smtcmd.MINIMIZE]:
            outstream.write("(%s " % self.name)
            printer.printer(self.args[0])
            for a in self.args[1]:
                option_name, value = a
                if ":signed" != option_name:
                    outstream.write(" %s %s" % (option_name, value))
                else:
                    outstream.write(" %s " % option_name)
            outstream.write(")")

        elif self.name in [smtcmd.MINMAX, smtcmd.MAXMIN]:
            outstream.write("(%s" % self.name)
            for a in self.args:
                outstream.write(" ")
                printer.printer(a)
            outstream.write(")")

        elif self.name == smtcmd.CHECK_ALLSAT:
            outstream.write("(%s " % self.name)
            if self.args:
                outstream.write("(")
                for expr in self.args[:-1]:
                    printer.printer(expr)
                    outstream.write(" ")
                printer.printer(self.args[-1])
                outstream.write(")")
            outstream.write(")")

        elif self.name in [smtcmd.CHECK_SAT, smtcmd.EXIT,
                           smtcmd.RESET_ASSERTIONS, smtcmd.GET_UNSAT_CORE,
                           smtcmd.GET_ASSIGNMENT, smtcmd.GET_MODEL, smtcmd.GET_OBJECTIVES]:
            outstream.write("(%s)" % self.name)

        elif self.name == smtcmd.SET_LOGIC:
            outstream.write("(%s %s)" % (self.name, self.args[0]))

        elif self.name in [smtcmd.DECLARE_FUN, smtcmd.DECLARE_CONST]:
            symbol = self.args[0]
            type_str = symbol.symbol_type().as_smtlib()
            outstream.write("(%s %s %s)" % (self.name,
                                            quote(symbol.symbol_name()),
                                            type_str))

        elif self.name == smtcmd.DEFINE_FUN:
            name = self.args[0]
            params_list = self.args[1]
            params = " ".join(["(%s %s)" % (v, v.symbol_type().as_smtlib(funstyle=False)) for v in params_list])
            rtype = self.args[2]
            expr = self.args[3]
            outstream.write("(%s %s (%s) %s " % (self.name,
                                                name,
                                                params,
                                                rtype.as_smtlib(funstyle=False)))
            printer.printer(expr)
            outstream.write(")")

        elif self.name in [smtcmd.PUSH, smtcmd.POP, smtcmd.LOAD_OBJECTIVE_MODEL]:
            outstream.write("(%s %d)" % (self.name, self.args[0]))

        elif self.name == smtcmd.DEFINE_SORT:
            name = self.args[0]
            params_list = self.args[1]
            params = " ".join(x.as_smtlib(funstyle=False) for x in params_list)
            rtype = self.args[2]
            outstream.write("(%s %s (%s) %s)" % (self.name,
                                                 name,
                                                 params,
                                                 rtype.as_smtlib(funstyle=False)))
        elif self.name == smtcmd.DECLARE_SORT:
            type_decl = self.args[0]
            outstream.write("(%s %s %d)" % (self.name,
                                            type_decl.name,
                                            type_decl.arity))

        elif self.name in smtcmd.ALL_COMMANDS:
            raise NotImplementedError("'%s' is a valid SMT-LIB command "\
                                      "but it is currently not supported. "\
                                      "Please open a bug-report." % self.name)
        else:
            raise UnknownSmtLibCommandError(self.name)

    def serialize_to_string(self, daggify: bool=True) -> str:
        buf = StringIO()
        self.serialize(buf, daggify=daggify)
        return buf.getvalue()



class SmtLibScript(object):

    def __init__(self):
        self.annotations: Optional[Annotations] = None
        self.commands: List[SmtLibCommand] = []

    def add(self, name: str, args: List[Optional[Union[Logic, _TypeDecl, FNode, str]]]):
        """Adds a new SmtLibCommand with the given name and arguments."""
        self.add_command(SmtLibCommand(name=name,
                                       args=args))

    def add_command(self, command: SmtLibCommand):
        self.commands.append(command)

    def evaluate(self, solver: SmtLibSolver) -> List[Tuple[str, Optional[Union[Model, bool, Goal, List[Tuple[FNode, FNode]]]]]]:
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

    def filter_by_command_name(self, command_name_set: List[str]) -> Iterator[Any]:
        return (cmd for cmd in self.commands if cmd.name in command_name_set)

    def get_strict_formula(self, mgr: Optional["pysmt.formula.FormulaManager"]=None) -> FNode:
        if self.contains_command(smtcmd.PUSH) or \
           self.contains_command(smtcmd.POP):
            raise PysmtValueError("Was not expecting push-pop commands")
        if self.count_command_occurrences(smtcmd.CHECK_SAT) != 1:
            raise PysmtValueError("Was expecting exactly one check-sat command")
        _And = mgr.And if mgr else get_env().formula_manager.And

        assertions = [cmd.args[0]
                      for cmd in self.filter_by_command_name([smtcmd.ASSERT])]
        return _And(assertions)

    def get_declared_symbols(self) -> Set[FNode]:
        return {cmd.args[0] for cmd in self.filter_by_command_name([smtcmd.DECLARE_CONST,
                                                                    smtcmd.DECLARE_FUN])}
    def get_define_fun_parameter_symbols(self) -> Set[FNode]:
        res = set()
        for cmd in self.filter_by_command_name([smtcmd.DEFINE_FUN]):
            for s in cmd.args[1]:
                res.add(s)
        return res

    def get_last_formula(self, mgr: Optional[FormulaManager]=None, return_optimizations: bool=False) -> Any:
        """Returns the last formula of the execution of the Script.

        This coincides with the conjunction of the assertions that are
        left on the assertion stack at the end of the SMTLibScript.

        If the parameter `return_optimizations` is set to `True` the method will
        return a couple where the first element is the last formula of the
        script and the second element is the tuple containing the last goals
        defined.
        """
        stack: List[FNode] = []
        backtrack: List[int] = []
        goals: List[Goal] = []
        goals_backtrack: List[int] = []
        max_smt_goals: Dict[Optional[str], Tuple[int, MaxSMTGoal]] = {}
        max_smt_goals_backtrack: Dict[Optional[str], List[int]] = defaultdict(list)
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
                goals.append(MaximizationGoal(cmd.args[0], _command_is_signed(cmd)))
            elif cmd.name == smtcmd.MINIMIZE:
                goals.append(MinimizationGoal(cmd.args[0], _command_is_signed(cmd)))
            elif cmd.name == smtcmd.MINMAX:
                goals.append(MinMaxGoal(cmd.args[0], _command_is_signed(cmd)))
            elif cmd.name == smtcmd.MAXMIN:
                goals.append(MaxMinGoal(cmd.args[0], _command_is_signed(cmd)))
            elif cmd.name == smtcmd.ASSERT_SOFT:
                formula = cmd.args[0]
                cmd_annotations = dict(cmd.args[1])
                max_smt_id = cmd_annotations.get(":id", "")
                max_smt_weight = cmd_annotations.get(":weight", mgr.Int(1))
                _, goal = max_smt_goals.setdefault(max_smt_id, (len(goals), MaxSMTGoal()))
                goal.add_soft_clause(formula, max_smt_weight)
                # if len(goal.soft) > 1 the goal is already in goals
                if len(goal.soft) == 1:
                    goals.append(goal)

        if return_optimizations:
            return mgr.And(stack), tuple(goals)
        return mgr.And(stack)

    def to_file(self, fname, daggify=True):
        with open(fname, "w") as outstream:
            self.serialize(outstream, daggify=daggify)

    def serialize(self, outstream: Union[TextIOWrapper, StringIO], daggify: bool=True):
        """Serializes the SmtLibScript expanding commands"""
        if daggify:
            printer: PrinterType = SmtDagPrinter(outstream, annotations=self.annotations)
        else:
            printer = SmtPrinter(outstream, annotations=self.annotations)

        for cmd in self.commands:
            cmd.serialize(printer=printer)
            outstream.write("\n")

    def __len__(self) -> int:
        return len(self.commands)

    def __iter__(self):
        return iter(self.commands)

    def __str__(self):
        return "\n".join((str(cmd) for cmd in self.commands))


def _command_is_signed(command: SmtLibCommand) -> bool:
    singed = False
    if len(command.args) >= 2:
        options = command.args[1]
        if options is not None:
            for arg in options:
                if arg[0] == ":signed":
                    singed = arg[1]
                    if not isinstance(singed, bool):
                        raise PysmtValueError(":signed annotation to a command must be a bool, %s is not" % str(singed))
                break
    return singed


def smtlibscript_from_formula(formula: FNode, logic: Optional[Union[str, int, Logic]]=None) -> SmtLibScript:
    script = SmtLibScript()

    if logic is None:
        # Get the simplest SmtLib logic that contains the formula
        f_logic = get_logic(formula)

        smt_logic: Optional[Union[Logic, str]] = None
        try:
            smt_logic = get_closer_smtlib_logic(f_logic)
        except NoLogicAvailableError:
            warnings.warn("The logic %s is not reducible to any SMTLib2 " \
                          "standard logic. Proceeding with non-standard " \
                          "logic '%s'" % (f_logic, f_logic),
                          stacklevel=3)
            smt_logic = f_logic
    elif not (isinstance(logic, Logic) or isinstance(logic, str)):
        raise UndefinedLogicError(str(logic))
    else:
        if logic not in SMTLIB2_LOGICS:
            warnings.warn("The logic %s is not reducible to any SMTLib2 " \
                          "standard logic. Proceeding with non-standard " \
                          "logic '%s'" % (logic, logic),
                          stacklevel=3)
        smt_logic = logic

    script.add(name=smtcmd.SET_LOGIC,
               args=[smt_logic])

    # Declare all types
    types = get_env().typeso.get_types(formula, custom_only=True)
    for type_ in types:
        script.add(name=smtcmd.DECLARE_SORT, args=[type_.decl])

    deps = formula.get_free_variables()
    # Declare all variables
    for symbol in deps:
        assert symbol.is_symbol()
        script.add(name=smtcmd.DECLARE_FUN, args=[symbol])

    # Assert formula
    script.add_command(SmtLibCommand(name=smtcmd.ASSERT,
                                     args=[formula]))
    # check-sat
    script.add_command(SmtLibCommand(name=smtcmd.CHECK_SAT,
                                     args=[]))
    return script


class InterpreterSMT(object):
    def evaluate(self, cmd: SmtLibCommand, solver: SmtLibSolver) -> Optional[Union[Model, bool, Goal, List[Tuple[FNode, FNode]]]]:
        return self._smt_evaluate(cmd, solver)

    def _smt_evaluate(self, cmd: SmtLibCommand, solver: SmtLibSolver) -> Optional[Union[Model, bool, Goal, List[Tuple[FNode, FNode]]]]:
        if cmd.name == smtcmd.SET_INFO:
            return solver.set_info(cmd.args[0], cmd.args[1])

        if cmd.name == smtcmd.SET_OPTION:
            opt = cmd.args[0]
            if opt[0] == ':':
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
            raise NotImplementedError("'%s' is a valid SMT-LIB command "\
                                      "but it is currently not supported. "\
                                      "Please open a bug-report." % cmd.name)
        else:
            raise UnknownSmtLibCommandError(cmd.name)


class InterpreterOMT(InterpreterSMT):

    def __init__(self):
        self.optimization_goals: Tuple[List[Goal], List[Tuple[FNode, FNode]]] = ([], [])
        self.opt_priority = "single-obj"

    def evaluate(self, cmd: SmtLibCommand, solver: SmtLibSolver) -> Optional[Union[Model, bool, Goal, List[Tuple[FNode, FNode]]]]:
        return self._omt_evaluate(cmd, solver)

    def _omt_evaluate(self, cmd: SmtLibCommand, optimizer: SmtLibSolver) -> Optional[Union[Model, bool, Goal, List[Tuple[FNode, FNode]]]]:
        if cmd.name == smtcmd.SET_OPTION:
            if cmd.args[0] == ":opt.priority":
                self.opt_priority = cmd.args[1]
            return None

        elif cmd.name == smtcmd.MAXIMIZE:
            g: Goal = MaximizationGoal(cmd.args[0])
            self.optimization_goals[0].append(g)
            return g

        elif cmd.name == smtcmd.MINIMIZE:
            g = MinimizationGoal(cmd.args[0])
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
                for model, values in optimizer.pareto_optimize(self.optimization_goals[0]):
                    rt = True
                    for (g, v) in zip(self.optimization_goals[0], values):
                        self.optimization_goals[1].append((g.term(), v))

            elif self.opt_priority == "box":
                assert isinstance(optimizer, Optimizer)
                boxed_results = optimizer.boxed_optimize(self.optimization_goals[0])
                if boxed_results is not None:
                    rt = True
                    for g in self.optimization_goals[0]:
                        self.optimization_goals[1].append((g.term(), boxed_results[g][1]))

            elif self.opt_priority == "lex":
                assert isinstance(optimizer, Optimizer)
                lex_results = optimizer.lexicographic_optimize(self.optimization_goals[0])
                if lex_results is not None:
                    _, values = lex_results
                    rt = True
                    for (g, v) in zip(self.optimization_goals[0], values):
                        self.optimization_goals[1].append((g.term(), v))
            return rt

        elif cmd.name == smtcmd.MAXMIN:
            g = MaxMinGoal(cmd.args[0])
            self.optimization_goals[0].append(g)
            return g

        elif cmd.name == smtcmd.MINMAX:
            g = MinMaxGoal(cmd.args[0])
            self.optimization_goals[0].append(g)
            return g

        elif cmd.name == smtcmd.GET_OBJECTIVES:
            return self.optimization_goals[1]

        else:
            return self._smt_evaluate(cmd, optimizer)
