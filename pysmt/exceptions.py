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

class UnknownSmtLibCommandError(Exception):
    """Raised when the parser finds an unknown command."""
    pass

class SolverReturnedUnknownResultError(Exception):
    """This exception is raised if a solver returns 'unknown' as a result"""
    pass

class UnknownSolverAnswerError(Exception):
    """Raised when the a solver returns an invalid response."""
    pass

class NoSolverAvailableError(Exception):
    """No solver is available for the selected Logic."""
    pass

class NonLinearError(Exception):
    """The provided expression is not linear."""
    pass

class UndefinedLogicError(Exception):
    """This exception is raised if an undefined Logic is attempted to be used."""
    pass

class InternalSolverError(Exception):
    """Generic exception to capture errors provided by a solver."""
    pass

class NoLogicAvailableError(Exception):
    """Generic exception to capture errors caused by missing support for logics."""
    pass

class SolverRedefinitionError(Exception):
    """Exception representing errors caused by multiple defintion of solvers
       having the same name."""
    pass

class SolverNotConfiguredForUnsatCoresError(Exception):
    """
    Exception raised if a solver not configured for generating unsat
    cores is required to produce a core.
    """
    pass

class SolverStatusError(Exception):
    """
    Exception raised if a method requiring a specific solver status is
    incorrectly called in the wrong status.
    """
    pass

class ConvertExpressionError(Exception):
    """Exception raised if the converter cannot convert an expression."""

    def __init__(self, message=None, expression=None):
        Exception.__init__(self)
        self.message = message
        self.expression=expression

    def __str__(self):
        return self.message

class UnsupportedOperatorError(Exception):
    """The expression contains an operator that is not supported.

    The argument node_type contains the unsupported operator id.
    """

    def __init__(self, message=None, node_type=None, expression=None):
        if message is None:
            message = "Unsupported operator '%s' (node_type: %d)" % (op.op_to_str(node_type), node_type)
        Exception.__init__(self)
        self.message = message
        self.expression = expression
        self.node_type = node_type

    def __str__(self):
        return self.message


class SolverAPINotFound(Exception):
    """The Python API of the selected solver cannot be found."""
    pass


class UndefinedSymbolError(Exception):
    """The given Symbol is not in the FormulaManager."""

    def __init__(self, name):
        Exception.__init__(self)
        self.name = name

    def __str__(self):
        return "'%s' is not defined!" % self.name
