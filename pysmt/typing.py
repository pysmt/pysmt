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
__BV_TYPES__ = {}

class PySMTType(object):
    def __init__(self, type_id=-1):
        self.type_id = type_id

    def is_bool_type(self):
        return False

    def is_int_type(self):
        return False

    def is_real_type(self):
        return False

    def is_bv_type(self):
        return False

    def is_function_type(self):
        return False

    def __hash__(self):
        return self.type_id

    def __eq__(self, other):
        if other is None:
            return False
        return self.type_id == other.type_id

    def __ne__(self, other):
        return not (self == other)

class BooleanType(PySMTType):
    def __init__(self):
        PySMTType.__init__(self, type_id = 0)

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
    def __init__(self):
        PySMTType.__init__(self, type_id = 1)

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
    def __init__(self):
        PySMTType.__init__(self, type_id = 2)

    def is_int_type(self):
        return True

    def as_smtlib(self, funstyle=True):
        if funstyle:
            return "() Int"
        else:
            return "Int"

    def __str__(self):
        return "Int"

# BV is a Factory for _BVType
def BVType(width=32):
    key = width
    if key in __BV_TYPES__:
        return  __BV_TYPES__[key]

    res = _BVType(width=width)
    __BV_TYPES__[key] = res
    return res


class _BVType(PySMTType):
    def __init__(self, width=32):
        PySMTType.__init__(self, type_id = 3)
        self.width = width

    def is_bv_type(self, width=None):
        if width:
            return self.width == width
        return True

    def as_smtlib(self, funstyle=True):
        if funstyle:
            return "() (_ BitVec %d)" % self.width
        else:
            return "(_ BitVec %d)" % self.width

    def __str__(self):
        return "BV%d" % self.width

    def __eq__(self, other):
        if other is None:
            return False
        if self.type_id != other.type_id:
            return False
        if self.width != other.width:
            return False
        return True

    def __hash__(self):
        return hash(self.type_id + self.width)

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
        PySMTType.__init__(self, type_id = 4)
        self.return_type = return_type
        self.param_types = param_types
        self._hash = hash(str(self))
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

    def __eq__(self, other):
        if other is None:
            return False
        if self.type_id != other.type_id:
            return False
        if id(self) == id(other):
            return True
        return str(self) == str(other)

    def __hash__(self):
        return self._hash

BOOL = BooleanType()

REAL = RealType()

INT = IntType()

PYSMT_TYPES = frozenset([BOOL, REAL, INT])

BV1, BV8, BV16, BV32, BV64, BV128 = [BVType(i) for i in [1, 8, 16, 32, 64, 128]]
