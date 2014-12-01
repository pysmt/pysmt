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
