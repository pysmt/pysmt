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
 * BVType
 * FunctionType

Types are represented by singletons. Basic types (Bool, Int and Real)
are constructed here by default, while BVType and FunctionType relies
on a factory service. Each BitVector width is represented by a
different instance of BVType.

"""

# Global dictionary of types, used to store the singletons
__CUSTOM_TYPES__ = {}
__BV_TYPES__ = {}

class PySMTType(object):
    """Abstract class for representing a type within pySMT."""

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
    
    def is_array_type(self):
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
        if other is None:
            return True
        return self.type_id != other.type_id


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
    
class ArrayType(PySMTType):
    def __init__(self, arraytype):
        PySMTType.__init__(self, type_id = 5)
        if arraytype == INT:
            self.type = IntType()
        elif arraytype == REAL:
            self.type = RealType()
        elif arraytype == BOOL:
            self.type = BooleanType()
        else:
            raise Exception("Unsupported array type %s" %(type))

    def is_array_type(self):
        return True
    
    def is_array_int_type(self):
        return self.type == IntType()
    
    def is_array_real_type(self):
        return self.type == RealType()
    
    def is_array_bool_type(self):
        return self.type == BooleanType()

    def as_smtlib(self, funstyle=True):
        if funstyle:
            return "() (_ Array Int %s)" %self.type.__str__() 
        else:
            return "(_ Array Int %s)" %self.type.__str__()

    def __str__(self):
        return "Array Int %s" %self.type.__str__()


def BVType(width=32):
    """Returns the singleton associated to the BV type for the given width.

    This function takes care of building and registering the type
    whenever needed. To see the functions provided by the type look at
    _BVType.
    """
    key = width
    if key in __BV_TYPES__:
        return  __BV_TYPES__[key]

    res = _BVType(width=width)
    __BV_TYPES__[key] = res
    return res


class _BVType(PySMTType):
    """Internal class to represent a BitVector type.

    This class should not be instantiated directly, but the factory
    method BVType should be used instead.
    """
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

    def __ne__(self, other):
        if other is None:
            return True
        if self.type_id != other.type_id:
            return True
        if self.width != other.width:
            return True
        return False

        return True
    def __hash__(self):
        return hash(self.type_id + self.width)


# FunctionType is a Factory that returns a _FunctionType
def FunctionType(return_type, param_types):
    """Returns the singleton of the Function type with the given arguments.

    This function takes care of building and registering the type
    whenever needed. To see the functions provided by the type look at
    _FunctionType

    Note: If the list of parameters is empty, the function is
    equivalent to the return type.
    """
    param_types = tuple(param_types)
    key = (return_type, param_types)
    # 0-arity functions types are equivalent to the return type
    if len(param_types) == 0:
        return return_type
    if key in __CUSTOM_TYPES__:
        return  __CUSTOM_TYPES__[key]

    res = _FunctionType(return_type=return_type,
                        param_types=param_types)
    __CUSTOM_TYPES__[key] = res
    return res


class _FunctionType(PySMTType):
    """Internal class used to represent a Function type.

    This class should not be instantiated directly, but the factory
    method FunctionType should be used instead.
    """
    def __init__(self, return_type, param_types):
        PySMTType.__init__(self, type_id = 4)
        self._return_type = return_type
        self._param_types = param_types
        self._hash = hash(str(self))
        return

    @property
    def param_types(self):
        """Returns the arguments of the Function Type.

        E.g.,  F: (Bool -> Bool) -> Real
        Returns [BoolType, BoolType].
        """
        return self._param_types

    @property
    def return_type(self):
        """Returns the return type of  the Function Type.

        E.g.,  F: (Bool -> Bool) -> Real
        Returns RealType.
        """
        return self._return_type

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

    def __ne__(self, other):
        if other is None:
            return True
        if self.type_id != other.type_id:
            return True
        if id(self) == id(other):
            return False
        return str(self) != str(other)

    def __hash__(self):
        return self._hash


# Singletons for the basic types
BOOL = BooleanType()
REAL = RealType()
INT = IntType()
ARRAY_INT = ArrayType(INT)
ARRAY_REAL = ArrayType(REAL)
ARRAY_BOOL = ArrayType(BOOL)

# Helper Constants
PYSMT_TYPES = frozenset([BOOL, REAL, INT])
BV1, BV8, BV16, BV32, BV64, BV128 = [BVType(i) for i in [1, 8, 16, 32, 64, 128]]
