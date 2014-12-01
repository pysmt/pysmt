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
"""This module defines the types of the formulae handled by pySMT.

In the current version these are:
 * Bool
 * Int
 * Real
 * FunctionType

Types are represented by singletons. Basic types (Bool, Int and Real)
are constructed here by default, while FunctionType relies on a
factory service, and existing FunctionTypes are stored in a global
map.
"""

# Global dictionary of types
__CUSTOM_TYPES__ = {}


class PySMTType(object):

    def is_bool_type(self):
        return False

    def is_int_type(self):
        return False

    def is_real_type(self):
        return False

    def is_function_type(self):
        return False


class BooleanType(PySMTType):
    def is_bool_type(self):
        return True

    def as_smtlib(self, funstyle=True):
        if funstyle:
            return "() Bool"
        else:
            return "Bool"

    def __str__(self):
        return "Bool"


class RealType(PySMTType):

    def is_real_type(self):
        return True

    def as_smtlib(self, funstyle=True):
        if funstyle:
            return "() Real"
        else:
            return "Real"

    def __str__(self):
        return "Real"


class IntType(PySMTType):
    def is_int_type(self):
        return True

    def as_smtlib(self, funstyle=True):
        if funstyle:
            return "() Int"
        else:
            return "Int"

    def __str__(self):
        return "Int"


# FunctionType is a Factory that returns a _FunctionType
def FunctionType(return_type, param_types):
    param_types = tuple(param_types)
    key = (return_type, param_types)
    if key in __CUSTOM_TYPES__:
        return  __CUSTOM_TYPES__[key]

    res = _FunctionType(return_type=return_type,
                        param_types=param_types)
    __CUSTOM_TYPES__[key] = res
    return res


class _FunctionType(PySMTType):

    def __init__(self, return_type, param_types):
        PySMTType.__init__(self)
        self.return_type = return_type
        self.param_types = param_types
        return

    def as_smtlib(self, funstyle=True):
        args = [p.as_smtlib(False)
                for p in self.param_types]
        rtype = self.return_type.as_smtlib(False)

        if funstyle:
            res = "(%s) %s" % (" ".join(args), rtype)
        else:
            res = " -> ".join(args+[rtype])
        return res

    def __str__(self):
        return " -> ".join([str(p) for p in self.param_types] +
                           [str(self.return_type)])

    def is_function_type(self):
        return True


BOOL = BooleanType()

REAL = RealType()

INT = IntType()

PYSMT_TYPES = frozenset([BOOL, REAL, INT])
