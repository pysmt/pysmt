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
import pysmt

from pysmt.exceptions import PysmtValueError, PysmtModeError


class PySMTType(object):
    """Class for representing a type within pySMT.

    Instances of this class are used to represent sorts.
    The subclass FunctionType is used to represent function declarations.

    """

    def __init__(self, decl=None, basename=None, args=None):
        if decl:
            self.decl = decl
            self.basename = decl.name
            self.arity = decl.arity
            if (args and self.arity != len(args)) or \
               (not args and self.arity != 0):
                raise PysmtValueError("Invalid number of arguments. " +
                                      "Expected %d, got %d." % (self.arity,
                                                                len(args)))
            self.custom_type = decl.custom_type
        else:
            self.basename = basename
            self.arity = len(args) if args else 0
            self.custom_type = False

        self.args = args
        if self.args:
            args_str = "{%s}" % ", ".join(str(a) for a in self.args)
        else:
            args_str = ""
        if self.basename:
            self.name = self.basename + args_str
        else:
            self.name = None

    def is_bool_type(self):
        return False

    def is_real_type(self):
        return False

    def is_int_type(self):
        return False

    def is_bv_type(self, width=None):
        #pylint: disable=unused-argument
        return False

    def is_array_type(self):
        return False

    def is_string_type(self):
        return False

    def is_function_type(self):
        return False

    def is_custom_type(self):
        return self.custom_type

    def __hash__(self):
        return hash(self.name)

    def __eq__(self, other):
        if other is None:
            return False
        if self is other:
            return True
        if self.basename == other.basename:
            return self.args == other.args
        return False

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
            name = "(" + self.basename + " " + args + ")"
        if funstyle:
            return "() %s" % name
        else:
            return name

    def __str__(self):
        return self.name

# EOC PySMTType

# Basic Types Declarations
class _BoolType(PySMTType):
    def __init__(self):
        decl = _TypeDecl("Bool", 0)
        PySMTType.__init__(self, decl=decl, args=None)

    def is_bool_type(self):
        return True

class _IntType(PySMTType):
    def __init__(self):
        decl = _TypeDecl("Int", 0)
        PySMTType.__init__(self, decl=decl, args=None)

    def is_int_type(self):
        return True

class _RealType(PySMTType):
    def __init__(self):
        decl = _TypeDecl("Real", 0)
        PySMTType.__init__(self, decl=decl, args=None)

    def is_real_type(self):
        return True

class _StringType(PySMTType):
    def __init__(self):
        decl = _TypeDecl("String", 0)
        PySMTType.__init__(self, decl=decl, args=None)

    def is_string_type(self):
        return True

# End Basic Types Declarations


class _ArrayType(PySMTType):
    """Internal class used to represent an Array type.

    This class should not be instantiated directly, but the factory
    method ArrayType should be used instead.
    """

    _instances = {}

    def __init__(self, index_type, elem_type):
        decl = _TypeDecl("Array", 2)
        PySMTType.__init__(self, decl=decl, args=(index_type, elem_type))

    @property
    def elem_type(self):
        """Returns the element type.

        E.g.,  A: (Array Int Real)
        Returns RealType.
        """
        return self.args[1]

    @property
    def index_type(self):
        """Returns the index type.

        E.g.,  A: (Array Int Real)
        Returns IntType.
        """
        return self.args[0]

    def is_array_type(self):
        return True

# EOC _ArrayType


class _BVType(PySMTType):
    """Internal class to represent a BitVector type.

    This class should not be instantiated directly, but the factory
    method BVType should be used instead.
    """

    _instances = {}

    def __init__(self, width=32):
        decl = _TypeDecl("BV{%d}" % width, 0)
        PySMTType.__init__(self, decl=decl, args=None)
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

    def __eq__(self, other):
        if PySMTType.__eq__(self, other):
            return True
        if other is not None and other.is_bv_type():
            return self.width == other.width
        return False

    def __hash__(self):
        return hash(self.width)

# EOC _BVType


class _FunctionType(PySMTType):
    """Internal class used to represent a Function type.

    This class should not be instantiated directly, but the factory
    method FunctionType should be used instead.
    """

    _instances = {}

    def __init__(self, return_type, param_types):
        PySMTType.__init__(self)
        self._return_type = return_type
        self._param_types = tuple(param_types)
        self._hash = hash(return_type) + sum(hash(p) for p in param_types)
        # Note:

        # An underlying assumption of this module is that
        # PySMTType.args can be used as key to identify a given type
        # instance. This means that all subtypes are accessible
        # through args (similarly as how we do FNode.args).
        #
        # This means that
        #  - Hashing can use args as a key
        #  - Navigating the type tree (e.g., during normalization)
        #    only works on args.
        #
        # In order to make this possible, we need to combine the
        # return typ and param_types for FunctionType.
        self.args = (self._return_type,) + self.param_types
        self.arity = len(self.args)
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
        if self is other:
            return True
        if other.is_function_type():
            if self.return_type == other.return_type and\
               self.param_types == other.param_types:
                return True
        return False

    def __hash__(self):
        return self._hash


class _TypeDecl(object):
    """Create a new Type Declaration (sort).

    This is equivalent to the SMT-LIB command "declare-sort".
    NOTE: This object is **not** a Type, but a Type Declaration.
    """

    def __init__(self, name, arity):
        self.name = name
        self.arity = arity
        self.custom_type = False

    def __call__(self, *args):
        env = pysmt.environment.get_env()
        # Note: This uses the global type manager
        if not env.enable_infix_notation:
            raise PysmtModeError("Infix notation disabled. "
                                 "Use type_manager.get_type_instance instead.")
        return env.type_manager.get_type_instance(self, *args)

    def __str__(self):
        return "%s/%s" % (self.name, self.arity)

    def set_custom_type_flag(self):
        assert self.custom_type == False
        self.custom_type = True

# EOC _TypeDecl


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


#
# Singletons for the basic types
#
BOOL = _BoolType()
REAL = _RealType()
INT =  _IntType()
STRING = _StringType()
PYSMT_TYPES = frozenset([BOOL, REAL, INT])

# Helper Constants
BV1, BV8, BV16, BV32, BV64, BV128 = [_BVType(i) for i in [1, 8, 16, 32, 64, 128]]
ARRAY_INT_INT = _ArrayType(INT,INT)


class TypeManager(object):

    def __init__(self, environment):
        self._bv_types = {}
        self._function_types = {}
        self._array_types = {}
        self._custom_types = {}
        self._custom_types_decl = {}
        self._bool = None
        self._real = None
        self._int = None
        self._string = None
        #
        self.load_global_types()
        self.environment = environment

    def load_global_types(self):
        """Register basic global types within the TypeManager."""
        for bvtype in (BV1, BV8, BV16, BV32, BV64, BV128):
            self._bv_types[bvtype.width] = bvtype
        self._array_types[(INT, INT)] = ARRAY_INT_INT
        self._bool = BOOL
        self._real = REAL
        self._int = INT
        self._string = STRING

    def BOOL(self):
        return self._bool

    def REAL(self):
        return self._real

    def INT(self):
        return self._int

    def STRING(self):
        return self._string

    def BVType(self, width=32):
        """Returns the singleton associated to the BV type for the given width.

        This function takes care of building and registering the type
        whenever needed. To see the functions provided by the type look at
        _BVType.
        """
        try:
            ty = self._bv_types[width]
        except KeyError:
            ty = _BVType(width=width)
            self._bv_types[width] = ty
        return ty

    def FunctionType(self, return_type, param_types):
        """Returns the singleton of the Function type with the given arguments.

        This function takes care of building and registering the type
        whenever needed. To see the functions provided by the type look at
        _FunctionType

        Note: If the list of parameters is empty, the function is
        equivalent to the return type.
        """
        param_types = tuple(param_types)
        key = (return_type, param_types)
        # 0-arity function types are equivalent to the return type
        if len(param_types) == 0:
            return return_type
        try:
            ty = self._function_types[key]
        except KeyError:
            assert_is_type(return_type, __name__)
            assert_are_types(param_types, __name__)
            ty = _FunctionType(return_type=return_type,
                               param_types=param_types)
            self._function_types[key] = ty
        return ty

    def ArrayType(self, index_type, elem_type):
        """Returns the singleton of the Array type with the given arguments.

        This function takes care of building and registering the type
        whenever needed. To see the functions provided by the type look at
        _ArrayType
        """
        key = (index_type, elem_type)
        try:
            ty = self._array_types[key]
        except KeyError:
            assert_are_types((index_type, elem_type), __name__)
            ty = _ArrayType(index_type, elem_type)
            self._array_types[key] = ty
        return ty

    def Type(self, name, arity=0):
        """Creates a new Type Declaration (sort declaration).

        This is equivalent to the SMT-LIB command "declare-sort".  For
        sorts of arity 0, we return a PySMTType, all other sorts need to
        be instantiated.

        See class _Type.
        """

        try:
            td = self._custom_types_decl[name]
            if td.arity != arity:
                raise PysmtValueError("Type %s previously declared with arity "\
                                      " %d." % (name, td.arity))
        except KeyError:
            td = _TypeDecl(name, arity)
            td.set_custom_type_flag()
            self._custom_types_decl[name] = td

        if td.arity == 0:
            # Automatically instantiate 0-arity types
            return self.get_type_instance(td)
        return td

    def get_type_instance(self, type_decl, *args):
        """Creates an instance of the TypeDecl with the given arguments."""
        assert_are_types(args, __name__)
        key = (type_decl, tuple(args)) if args is not None else type_decl
        try:
            ty = self._custom_types[key]
        except KeyError:
            ty = PySMTType(decl=type_decl, args=args)
            self._custom_types[key] = ty
        return ty

    def normalize(self, type_):
        """Recursively recreate the given type within the manager.

        This proceeds iteratively on the structure of the type tree.
        """
        stack = [type_]
        typemap = {}
        while stack:
            ty = stack.pop()
            if ty.arity == 0:
                if (ty.is_bool_type() or ty.is_int_type() or
                    ty.is_real_type() or ty.is_string_type()):
                    myty = ty
                elif ty.is_bv_type():
                    myty = self.BVType(ty.width)
                else:
                    myty = self.Type(ty.basename, arity=0)
                typemap[ty] = myty
            else:
                missing = [subtype for subtype in ty.args\
                           if subtype not in typemap]
                if missing:
                    # At least one type still needs to be converted
                    stack.append(ty)
                    stack += missing
                else:
                    if ty.is_array_type():
                        index_type = typemap[ty.index_type]
                        elem_type = typemap[ty.elem_type]
                        myty = self.ArrayType(index_type, elem_type)
                    elif ty.is_function_type():
                        param_types = (typemap[a] for a in ty.param_types)
                        return_type = typemap[ty.return_type]
                        myty = self.FunctionType(return_type, param_types)
                    else:
                        # Custom Type
                        typedecl = self.Type(type_.basename, type_.arity)
                        new_args = tuple(typemap[a] for a in type_.args)
                        myty = self.get_type_instance(typedecl, *new_args)
                    typemap[ty] = myty
        return typemap[type_]

# EOC TypeManager


# Util
def assert_is_type(target, func_name):
    if not isinstance(target, PySMTType):
        raise PysmtValueError("Invalid type '%s' in %s." % (target, func_name))

def assert_are_types(targets, func_name):
    for target in targets:
        assert_is_type(target, func_name)



def BVType(width=32):
    """Returns the BV type for the given width."""
    mgr = pysmt.environment.get_env().type_manager
    return mgr.BVType(width=width)

def FunctionType(return_type, param_types):
    """Returns Function Type with the given arguments."""
    mgr = pysmt.environment.get_env().type_manager
    return mgr.FunctionType(return_type=return_type, param_types=param_types)

def ArrayType(index_type, elem_type):
    """Returns the Array type with the given arguments."""
    mgr = pysmt.environment.get_env().type_manager
    return mgr.ArrayType(index_type=index_type, elem_type=elem_type)

def Type(name, arity=0):
    """Returns the Type Declaration with the given name (sort declaration)."""
    mgr = pysmt.environment.get_env().type_manager
    return mgr.Type(name=name, arity=arity)
