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
 * ArrayType

Types are represented by singletons. Basic types (Bool, Int and Real)
are constructed here by default, while BVType and FunctionType relies
on a factory service. Each BitVector width is represented by a
different instance of BVType.

"""
from pysmt.exceptions import PysmtValueError


class PySMTType(object):
    """Class for representing a type within pySMT.

    Instances of this class are used to represent sorts.
    The subclass FunctionType is used to represent function declarations.
    """

    __MAX_ID = -1

    def __init__(self, type_id=None, name=None, args=None):
        assert type_id is None or isinstance(type_id, int)
        if type_id is None:
            type_id = PySMTType.__MAX_ID + 1
            PySMTType.__MAX_ID = type_id
        else:
            assert type_id > PySMTType.__MAX_ID
            PySMTType.__MAX_ID = type_id
        self.type_id = type_id
        self.name = name
        self.args = args
        self.arity = len(args) if args else 0

    def is_bool_type(self):
        return self.type_id == 0

    def is_real_type(self):
        return self.type_id == 1

    def is_int_type(self):
        return self.type_id == 2

    def is_bv_type(self, width=None):
        #pylint: disable=unused-argument
        return False

    def is_function_type(self):
        return False

    def is_array_type(self):
        return False

    def __hash__(self):
        return self.type_id

    def __eq__(self, other):
        if other is None:
            return False
        return self.type_id == other.type_id

    def __ne__(self, other):
        return not self.__eq__(other)

    def __repr__(self):
        if self.name is None:
            return self.__class__.__name__
        return self.name

    def as_smtlib(self, funstyle=True):
        name = self.name
        if self.args:
            args = " ".join([arg.as_smtlib(funstyle=False) \
                             for arg in self.args])
            name = "(" + self.name + " " + args + ")"
        if funstyle:
            return "() %s" % name
        else:
            return name

    def __str__(self):
        if self.args:
            args = "(%s)" % ", ".join(str(a) for a in self.args)
        else:
            args = ""
        return self.name + args


def BVType(width=32):
    """Returns the singleton associated to the BV type for the given width.

    This function takes care of building and registering the type
    whenever needed. To see the functions provided by the type look at
    _BVType.
    """
    try:
        ty = _BVType._instances[width]
    except KeyError:
        ty = _BVType(width=width)
        _BVType._instances[width] = ty
    return ty


class _BVType(PySMTType):
    """Internal class to represent a BitVector type.

    This class should not be instantiated directly, but the factory
    method BVType should be used instead.
    """

    _instances = {}

    def __init__(self, width=32):
        PySMTType.__init__(self)
        self._width = width

    @property
    def width(self):
        return self._width

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
        return "BV{%d}" % self.width

    def __eq__(self, other):
        if other is None:
            return False
        if self.type_id != other.type_id:
            return False
        if self.width != other.width:
            return False
        return True

    def __ne__(self, other):
        return not self.__eq__(other)

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
    try:
        ty = _FunctionType._instances[key]
    except KeyError:
        ty = _FunctionType(return_type=return_type,
                           param_types=param_types)
        _FunctionType._instances[key] = ty
    return ty


class _FunctionType(PySMTType):
    """Internal class used to represent a Function type.

    This class should not be instantiated directly, but the factory
    method FunctionType should be used instead.
    """

    _instances = {}

    def __init__(self, return_type, param_types):
        PySMTType.__init__(self)
        self._return_type = return_type
        self._param_types = param_types
        self._hash = hash(return_type) + sum(hash(p) for p in param_types)
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
        if self.return_type != other.return_type:
            return False
        return self.param_types == other.param_types

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._hash


# ArrayType is a Factory that returns a _ArrayType
def ArrayType(index_type, elem_type):
    """Returns the singleton of the Array type with the given arguments.

    This function takes care of building and registering the type
    whenever needed. To see the functions provided by the type look at
    _ArrayType
    """
    key = (index_type, elem_type)
    try:
        ty = _ArrayType._instances[key]
    except KeyError:
        ty = _ArrayType(index_type, elem_type)
        _ArrayType._instances[key] = ty
    return ty


class _ArrayType(PySMTType):
    """Internal class used to represent an Array type.

    This class should not be instantiated directly, but the factory
    method ArrayType should be used instead.
    """

    _instances = {}

    def __init__(self, index_type, elem_type):
        PySMTType.__init__(self)
        self._index_type = index_type
        self._elem_type = elem_type
        self._hash = hash(index_type) + hash(elem_type)
        return

    @property
    def elem_type(self):
        """Returns the element type.

        E.g.,  A: (Array Int Real)
        Returns RealType.
        """
        return self._elem_type

    @property
    def index_type(self):
        """Returns the index type.

        E.g.,  A: (Array Int Real)
        Returns IntType.
        """
        return self._index_type

    def as_smtlib(self, funstyle=True):
        itype = self.index_type.as_smtlib(False)
        etype = self.elem_type.as_smtlib(False)

        if funstyle:
            return "() (Array %s %s)" % (itype, etype)
        else:
            return "(Array %s %s)" % (itype, etype)

    def __str__(self):
        return "Array{%s, %s}" % (self.index_type, self.elem_type)

    def is_array_type(self):
        return True

    def __eq__(self, other):
        if other is None:
            return False
        if self.type_id != other.type_id:
            return False
        if id(self) == id(other):
            return True
        if self.index_type != other.index_type:
            return False
        return self.elem_type == other.elem_type

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return self._hash

# Custom Type (sorts declaration)
def Type(name, arity=0):
    """Creates a new Type Declaration (sort declaration).

    This is equivalent to the SMT-LIB command "declare-sort".  For
    sorts of arity 0, we return a PySMTType, all other sorts need to
    be instantiated.

    See class _Type.
    """

    if arity == 0:
        # Automatically instantiate 0-arity types
        return _TypeDecl(name, arity)()
    return _TypeDecl(name, arity)


class _TypeDecl(object):
    """Create a new Type Declaration (sort).

    This is equivalent to the SMT-LIB command "declare-sort".
    NOTE: This object is **not** a Type, but a Type Declaration.
    """

    # Maintain a unique instance of _Type and _PySMTType for each
    # type declaration and type instance.
    _names = {}
    _instances = {}

    def __new__(cls, name, arity):
        try:
            ty = _TypeDecl._names[name]
            if ty.arity != arity:
                raise PysmtValueError("Type %s previously declared with arity "\
                                      " %d." % (name, ty.arity))
        except KeyError:
            ty = object.__new__(cls)
            _TypeDecl._names[name] = ty
        return ty

    def __init__(self, name, arity):
        self.name = name
        self.arity = arity

    def __call__(self, *args):
        if self.arity == 0:
            subkey = None
        else:
            assert len(args) == self.arity
            assert all(isinstance(t, PySMTType) for t in args)
            subkey = tuple(args)
        try:
            ty = _TypeDecl._instances[self.name][subkey]
        except KeyError:
            ty = PySMTType(name=self.name, args=args)
            if self.name not in _TypeDecl._instances:
                _TypeDecl._instances[self.name] = dict()
            _TypeDecl._instances[self.name][subkey] = ty
        return ty


class PartialType(object):
    """PartialType allows to delay the definition of a Type.

    A partial type is equivalent to SMT-LIB "define-sort" command.
    """
    def __init__(self, name, definition):
        self.name = name
        self.definition = definition

    def __str__(self):
        return "PartialType(%s)" % (self.name)

    def __call__(self, *args):
        return self.definition(*args)


# Singletons for the basic types
BOOL = PySMTType(type_id=0, name="Bool")
REAL = PySMTType(type_id=1, name="Real")
INT = PySMTType(type_id=2, name="Int")

# Helper Constants
PYSMT_TYPES = frozenset([BOOL, REAL, INT])
BV1, BV8, BV16, BV32, BV64, BV128 = [BVType(i) for i in [1, 8, 16, 32, 64, 128]]
ARRAY_INT_INT = ArrayType(INT,INT)
