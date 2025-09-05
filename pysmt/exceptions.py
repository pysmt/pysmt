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
"""This module contains all custom exceptions of pySMT."""

import pysmt.operators as op
from typing import Optional, Tuple


class PysmtException(Exception):
    """Base class for all custom exceptions of pySMT"""
    pass

class UnknownSmtLibCommandError(PysmtException):
    """Raised when the parser finds an unknown command."""
    pass

class SolverReturnedUnknownResultError(PysmtException):
    """This exception is raised if a solver returns 'unknown' as a result"""
    pass

class UnknownSolverAnswerError(PysmtException):
    """Raised when the a solver returns an invalid response."""
    pass

class NoSolverAvailableError(PysmtException):
    """No solver is available for the selected Logic."""
    pass

class NonLinearError(PysmtException):
    """The provided expression is not linear."""
    pass

class UndefinedLogicError(PysmtException):
    """This exception is raised if an undefined Logic is attempted to be used."""
    pass

class InternalSolverError(PysmtException):
    """Generic exception to capture errors provided by a solver."""
    pass

class NoLogicAvailableError(PysmtException):
    """Generic exception to capture errors caused by missing support for logics."""
    pass

class SolverRedefinitionError(PysmtException):
    """Exception representing errors caused by multiple definition of solvers
       having the same name."""
    pass

class SolverNotConfiguredForUnsatCoresError(PysmtException):
    """
    Exception raised if a solver not configured for generating unsat
    cores is required to produce a core.
    """
    pass

class SolverStatusError(PysmtException):
    """
    Exception raised if a method requiring a specific solver status is
    incorrectly called in the wrong status.
    """
    pass

class ConvertExpressionError(PysmtException):
    """Exception raised if the converter cannot convert an expression."""

    def __init__(self, message=None, expression=None):
        PysmtException.__init__(self)
        self.message = message
        self.expression=expression

    def __str__(self):
        return self.message

class UnsupportedOperatorError(PysmtException):
    """The expression contains an operator that is not supported.

    The argument node_type contains the unsupported operator id.
    """

    def __init__(self, message=None, node_type=None, expression=None):
        if message is None:
            message = "Unsupported operator '%s' (node_type: %d)" % (op.op_to_str(node_type), node_type)
        PysmtException.__init__(self)
        self.message = message
        self.expression = expression
        self.node_type = node_type

    def __str__(self):
        return self.message


class SolverAPINotFound(PysmtException):
    """The Python API of the selected solver cannot be found."""
    pass


class UndefinedSymbolError(PysmtException):
    """The given Symbol is not in the FormulaManager."""

    def __init__(self, name):
        PysmtException.__init__(self)
        self.name = name

    def __str__(self):
        return "'%s' is not defined!" % self.name

class PysmtModeError(PysmtException):
    """The current mode is not supported for this operation"""
    pass


class PysmtImportError(PysmtException, ImportError):
    pass

class PysmtValueError(PysmtException, ValueError):
    pass

class PysmtTypeError(PysmtException, TypeError):
    pass

class PysmtSyntaxError(PysmtException, SyntaxError):
    def __init__(self, message: str, pos_info: Optional[Tuple[int, int]]=None):
        super(PysmtSyntaxError, self).__init__(message)
        self.pos_info = pos_info
        self.message = message

    def __str__(self):
        if self.pos_info:
            return "Line %d, Col %d: " % self.pos_info + self.message
        else:
            return self.message


class PysmtIOError(PysmtException, IOError):
    pass

class PysmtInfinityError(PysmtException):
    """Infinite value in expressions."""
    pass

class PysmtInfinitesimalError(PysmtException):
    """Infinite value in expressions."""
    pass

class PysmtUnboundedOptimizationError(PysmtException):
    """Infinite optimal value in optimization."""
    pass

class GoalNotSupportedError(PysmtException):
    """
    Goal not supported by the solver.

    The possible modes are the optimization modes, in case a specific goal is
    not supported by a specific mode.
    The possible modes are:
    - basic
    - boxed
    - lexicographic
    - pareto
    """
    def __init__(self, solver, goal, mode=None):
        self._solver = solver
        self._goal = goal
        self._mode = mode

    @property
    def solver(self):
        return self._solver

    @property
    def goal(self):
        return self._goal

    @property
    def mode(self):
        return self._mode

    def __str__(self):
        mode_str = (" in mode '%s'" % self.mode) if self.mode else ""
        return "Optimizer '%s' does not support goal '%s'%s" % tuple(map(str, (type(self.solver).__name__, self.goal, mode_str)))
