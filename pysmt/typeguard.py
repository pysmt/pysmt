from typing import Optional
from typing_extensions import TypeGuard
from pysmt.typing import (
    PySMTType,
    _BoolType,
    _RealType,
    _IntType,
    _BVType,
    _ArrayType,
    _StringType,
    _FunctionType,
    _AlgebraicDataType,
    _TypeDecl,
)


def is_bool_type(type: "PySMTType") -> TypeGuard["_BoolType"]:
    return type.is_bool_type()


def is_real_type(type: "PySMTType") -> TypeGuard["_RealType"]:
    return type.is_real_type()


def is_int_type(type: "PySMTType") -> TypeGuard["_IntType"]:
    return type.is_int_type()


def is_bv_type(type: "PySMTType", width: Optional[int] = None) -> TypeGuard["_BVType"]:
    return type.is_bv_type(width)


def is_array_type(type: "PySMTType") -> TypeGuard["_ArrayType"]:
    return type.is_array_type()


def is_string_type(type: "PySMTType") -> TypeGuard["_StringType"]:
    return type.is_string_type()


def is_function_type(type: "PySMTType") -> TypeGuard["_FunctionType"]:
    return type.is_function_type()


def is_algebraic_data_type(type: "PySMTType") -> TypeGuard["_AlgebraicDataType"]:
    return type.is_algebraic_data_type()


def is_adt_constructor(
    type: "PySMTType",
) -> TypeGuard["_AlgebraicDataType._Constructor"]:
    return isinstance(type, _AlgebraicDataType._Constructor)


def is_adt_selector(type: "PySMTType") -> TypeGuard["_AlgebraicDataType._Selector"]:
    return isinstance(type, _AlgebraicDataType._Selector)


def is_adt_discriminator(
    type: "PySMTType",
) -> TypeGuard["_AlgebraicDataType._Discriminator"]:
    return isinstance(type, _AlgebraicDataType._Discriminator)


def is_custom_type(type: "PySMTType") -> TypeGuard["_TypeDecl"]:
    return type.custom_type
