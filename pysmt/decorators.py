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
from functools import wraps
import warnings

import pysmt.exceptions

class deprecated(object):
    """This is a decorator which can be used to mark functions
    as deprecated. It will result in a warning being emmitted
    when the function is used."""

    def __init__(self, alternative=None):
        self.alternative = alternative

    def __call__(self, func):
        def newFunc(*args, **kwargs):
            alt = ""
            if self.alternative is not None:
                alt = " You should call %s() instead!" % self.alternative
            warnings.warn("Call to deprecated function %s().%s" % \
                          (func.__name__, alt),
                          category=DeprecationWarning,
                          stacklevel=2)
            return func(*args, **kwargs)
        newFunc.__name__ = func.__name__
        newFunc.__doc__ = func.__doc__
        newFunc.__dict__.update(func.__dict__)
        return newFunc


def clear_pending_pop(f):
    """Pop the solver stack (if necessary) before calling the function.

    Some functions (e.g., get_value) required the state of the solver
    to stay unchanged after a call to solve. Therefore, we can leave
    th solver in an intermediate state in which there is a formula
    asserted in the stack that is not needed (e.g., when solving under
    assumptions). In order to guarantee that methods operate on the
    correct set of formulae, all methods of the solver that rely on
    the assertion stack, need to be marked with this decorator.
    """

    @wraps(f)
    def clear_pending_pop_wrap(self, *args, **kwargs):
        if self.pending_pop:
            self.pending_pop = False
            self.pop()
        return f(self, *args, **kwargs)
    return clear_pending_pop_wrap


def typecheck_result(f):
    """Performs type checking on the return value using the global environment"""

    @wraps(f)
    def typecheck_result_wrap(*args, **kwargs):
        res = f(*args, **kwargs)
        res.get_type() # This raises an exception if an invalid type is found
    return typecheck_result_wrap


def catch_conversion_error(f):
    """Catch unknown operators errors and converts them into conversion error."""

    @wraps(f)
    def catch_conversion_error_wrap(*args, **kwargs):
        try:
            res = f(*args, **kwargs)
        except pysmt.exceptions.UnsupportedOperatorError as ex:
            raise pysmt.exceptions.ConvertExpressionError(message=
                "Could not convert the input expression. " +
                "The formula contains unsupported operators. " +
                "The error was: %s" % ex.message,
            expression=ex.expression)
        return res
    return catch_conversion_error_wrap


def assert_infix_enabled(f):
    """Raise an exception if infix notation is not enabled."""
    from functools import wraps
    from pysmt.exceptions import PysmtModeError
    INFIX_ERROR_MSG = """Infix notation is not enabled for the current environment.
Enable it by setting enable_infix_notation to True."""

    @wraps(f)
    def assert_infix_enabled_wrap(*args, **kwargs):
        from pysmt.environment import get_env
        if not get_env().enable_infix_notation:
            raise PysmtModeError(INFIX_ERROR_MSG)
        return f(*args, **kwargs)
    return assert_infix_enabled_wrap
