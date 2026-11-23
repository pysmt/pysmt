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
"""This module provides basic services to perform type checking and
reasoning about the type of formulae.

 * SimpleTypeChecker provides the pysmt.typing type of a formula
 * The functions assert_*_args are useful for testing the type of
   arguments of a given function.
"""

from typing import Any, Iterable, List, Optional, Sequence, Set, Tuple, cast

import pysmt
import pysmt.operators as op
import pysmt.typing as types
import pysmt.walkers as walkers
from pysmt.exceptions import PysmtTypeError
from pysmt.fnode import FNode
from pysmt.typing import BOOL, INT, REAL, STRING, PySMTType


class SimpleTypeChecker(walkers.DagWalker):
    def __init__(self, env: Optional["pysmt.environment.Environment"] = None):
        walkers.DagWalker.__init__(self, env=env)
        # If `be_nice` is true, the `get_type` method will return None if
        # the type cannot be computed instead of than raising an exception.
        self.be_nice: bool = False

    def _get_key(self, formula: FNode, **kwargs) -> FNode:
        return formula

    def get_type(self, formula: FNode) -> PySMTType:
        """Returns the pysmt.types type of the formula.

        If `self.be_nice` is `True` this method can return `None` instead of
        raising an exception, but internally a lot of calls rely on formulae
        being correctly typed.
        """
        res = self.walk(formula)
        if not self.be_nice and res is None:
            raise PysmtTypeError("The formula '%s' is not well-formed" % str(formula))
        return cast(PySMTType, res)

    def walk_type_to_type(
        self,
        formula: FNode,
        args: List[PySMTType],
        type_in: PySMTType,
        type_out: PySMTType,
    ) -> Optional[PySMTType]:
        assert formula is not None
        for x in args:
            if x is None or x != type_in:
                return None
        return type_out

    @walkers.handles(op.AND, op.OR, op.NOT, op.IMPLIES, op.IFF)
    def walk_bool_to_bool(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, BOOL, BOOL)

    def walk_real_to_bool(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, REAL, BOOL)

    @walkers.handles(op.TOREAL)
    def walk_int_to_real(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, INT, REAL)

    @walkers.handles(op.TOINT)
    def walk_real_to_int(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, REAL, INT)

    def walk_real_to_real(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, REAL, REAL)

    @walkers.handles(op.PLUS, op.MINUS, op.TIMES, op.DIV)
    def walk_realint_to_realint(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        rval = self.walk_type_to_type(formula, args, REAL, REAL)
        if rval is None:
            rval = self.walk_type_to_type(formula, args, INT, INT)
        return rval

    @walkers.handles(op.BV_ADD, op.BV_SUB, op.BV_NOT, op.BV_AND, op.BV_OR)
    @walkers.handles(op.BV_XOR, op.BV_NEG, op.BV_MUL)
    @walkers.handles(op.BV_UDIV, op.BV_UREM, op.BV_LSHL, op.BV_LSHR)
    @walkers.handles(op.BV_SDIV, op.BV_SREM, op.BV_ASHR)
    def walk_bv_to_bv(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        # We check that all children are BV and the same size
        target_bv_type = self.env.type_manager.BVType(formula.bv_width())
        for a in args:
            if not a == target_bv_type:
                return None
        return target_bv_type

    @walkers.handles(op.STR_CONCAT, op.STR_REPLACE)
    def walk_str_to_str(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, STRING, STRING)

    @walkers.handles(op.STR_LENGTH, op.STR_TO_INT)
    def walk_str_to_int(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, STRING, INT)

    @walkers.handles(op.STR_CONTAINS, op.STR_PREFIXOF, op.STR_SUFFIXOF)
    def walk_str_to_bool(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, STRING, BOOL)

    @walkers.handles(op.INT_TO_STR)
    def walk_int_to_str(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        return self.walk_type_to_type(formula, args, INT, STRING)

    def walk_bv_comp(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # We check that all children are BV and the same size
        a, b = args
        if a != b or (not a.is_bv_type()):
            return None
        return self.env.type_manager.BVType(1)

    @walkers.handles(op.BV_ULT, op.BV_ULE, op.BV_SLT, op.BV_SLE)
    def walk_bv_to_bool(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        width = cast(types._BVType, args[0]).width
        for a in args[1:]:
            if (not a.is_bv_type()) or width != cast(types._BVType, a).width:
                return None
        return BOOL

    def walk_bv_tonatural(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        if args[0].is_bv_type():
            return INT
        return None

    def walk_bv_concat(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # Width of BV operators are computed at construction time.
        # The type-checker only verifies that they are indeed
        # correct.
        try:
            l_width = cast(types._BVType, args[0]).width
            r_width = cast(types._BVType, args[1]).width
            target_width = formula.bv_width()
        except AttributeError:
            return None
        if not l_width + r_width == target_width:
            return None
        return self.env.type_manager.BVType(target_width)

    def walk_bv_extract(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        arg = args[0]
        if not arg.is_bv_type():
            return None
        base_width = cast(types._BVType, arg).width
        target_width = formula.bv_width()
        start = formula.bv_extract_start()
        end = formula.bv_extract_end()
        if start >= base_width or end >= base_width:
            return None
        if base_width < target_width:
            return None
        if target_width != (end - start + 1):
            return None
        return self.env.type_manager.BVType(target_width)

    @walkers.handles(op.BV_ROL, op.BV_ROR)
    def walk_bv_rotate(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        target_width = formula.bv_width()
        if target_width < formula.bv_rotation_step() or target_width < 0:
            return None
        if target_width != cast(types._BVType, args[0]).width:
            return None
        return self.env.type_manager.BVType(target_width)

    @walkers.handles(op.BV_ZEXT, op.BV_SEXT)
    def walk_bv_extend(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        target_width = formula.bv_width()
        if target_width < cast(types._BVType, args[0]).width or target_width < 0:
            return None
        return self.env.type_manager.BVType(target_width)

    def walk_equals(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        if args[0].is_bool_type():
            raise PysmtTypeError(
                "The formula '%s' is not well-formed."
                "Equality operator is not supported for Boolean"
                " terms. Use Iff instead." % str(formula)
            )
        elif args[0].is_bv_type():
            return self.walk_bv_to_bool(formula, args)
        return self.walk_type_to_type(formula, args, args[0], BOOL)

    @walkers.handles(op.LE, op.LT)
    def walk_math_relation(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        if args[0].is_real_type():
            return self.walk_type_to_type(formula, args, REAL, BOOL)
        return self.walk_type_to_type(formula, args, INT, BOOL)

    def walk_ite(self, formula: FNode, args: List[PySMTType], **kwargs) -> Any:
        assert formula is not None
        if None in args:
            return None
        if args[0] == BOOL and args[1] == args[2]:
            return args[1]
        return None

    @walkers.handles(op.BOOL_CONSTANT)
    def walk_identity_bool(
        self, formula: FNode, args: List[Any], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return BOOL

    @walkers.handles(op.REAL_CONSTANT, op.ALGEBRAIC_CONSTANT)
    def walk_identity_real(
        self, formula: FNode, args: List[Any], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return REAL

    @walkers.handles(op.INT_CONSTANT)
    def walk_identity_int(
        self, formula: FNode, args: List[Any], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return INT

    @walkers.handles(op.STR_CONSTANT)
    def walk_identity_string(
        self, formula: FNode, args: List[Any], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return STRING

    @walkers.handles(op.BV_CONSTANT)
    def walk_identity_bv(
        self, formula: FNode, args: List[Any], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 0
        return self.env.type_manager.BVType(formula.bv_width())

    @walkers.handles(op.FP_RM_CONSTANTS)
    def walk_fp_rounding_mode(
        self, formula: FNode, args: List[Any], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 0:
            return None
        return self.env.type_manager.RMType()

    def walk_fp_from_components(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        """Type the SMT-LIB ``fp`` constructor.

        The three arguments encode the sign, biased exponent, and trailing
        significand. SMT-LIB's significand-size includes the implicit
        leading bit, so the third bit-vector has width ``sb - 1``.
        """
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 3 or any(a is None or not a.is_bv_type() for a in args):
            return None

        sign_type = cast(types._BVType, args[0])
        exponent_type = cast(types._BVType, args[1])
        significand_type = cast(types._BVType, args[2])
        if sign_type.width != 1:
            return None
        if exponent_type.width <= 1 or significand_type.width < 1:
            return None

        return self.env.type_manager.FPType(
            exponent_type.width, significand_type.width + 1
        )

    @staticmethod
    def _same_fp_type(args: Sequence[PySMTType]) -> Optional[PySMTType]:
        """Return the common FP type of ``args``, or ``None``."""
        if not args or args[0] is None or not args[0].is_fp_type():
            return None
        target_type = args[0]
        if any(a is None or a != target_type for a in args[1:]):
            return None
        return target_type

    @walkers.handles(op.FP_ABS, op.FP_NEG)
    def walk_fp_unary(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 1:
            return None
        return self._same_fp_type(args)

    @walkers.handles(op.FP_SQRT, op.FP_ROUND_TO_INTEGRAL)
    def walk_fp_rounded_unary(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 2 or args[0] is None or not args[0].is_rm_type():
            return None
        return self._same_fp_type(args[1:])

    @walkers.handles(op.FP_ADD, op.FP_SUB, op.FP_MUL, op.FP_DIV)
    def walk_fp_rounded_binary(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 3 or args[0] is None or not args[0].is_rm_type():
            return None
        return self._same_fp_type(args[1:])

    def walk_fp_fma(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 4 or args[0] is None or not args[0].is_rm_type():
            return None
        return self._same_fp_type(args[1:])

    @walkers.handles(op.FP_REM, op.FP_MIN, op.FP_MAX)
    def walk_fp_binary(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 2:
            return None
        return self._same_fp_type(args)

    @walkers.handles(op.FP_LEQ, op.FP_LT, op.FP_EQ)
    def walk_fp_relation(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 2 or self._same_fp_type(args) is None:
            return None
        return BOOL

    @walkers.handles(
        op.FP_IS_NORMAL,
        op.FP_IS_SUBNORMAL,
        op.FP_IS_ZERO,
        op.FP_IS_INFINITE,
        op.FP_IS_NAN,
        op.FP_IS_NEGATIVE,
        op.FP_IS_POSITIVE,
    )
    def walk_fp_predicate(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 1 or self._same_fp_type(args) is None:
            return None
        return BOOL

    @staticmethod
    def _valid_fp_format(formula: FNode) -> Optional[Tuple[int, int]]:
        try:
            exponent_size, significand_size = formula.fp_conversion_format()
        except (AssertionError, TypeError, ValueError, PysmtTypeError):
            return None
        if (
            not isinstance(exponent_size, int)
            or isinstance(exponent_size, bool)
            or exponent_size <= 1
            or not isinstance(significand_size, int)
            or isinstance(significand_size, bool)
            or significand_size <= 1
        ):
            return None
        return exponent_size, significand_size

    def walk_fp_from_ieee_bv(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        fp_format = self._valid_fp_format(formula)
        if (
            len(args) != 1
            or fp_format is None
            or args[0] is None
            or not args[0].is_bv_type()
        ):
            return None
        exponent_size, significand_size = fp_format
        if cast(types._BVType, args[0]).width != (exponent_size + significand_size):
            return None
        return self.env.type_manager.FPType(exponent_size, significand_size)

    def walk_fp_to_fp(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        fp_format = self._valid_fp_format(formula)
        if (
            len(args) != 2
            or fp_format is None
            or args[0] is None
            or not args[0].is_rm_type()
            or args[1] is None
        ):
            return None
        source_type = args[1]
        if not (
            source_type.is_fp_type()
            or source_type.is_real_type()
            or source_type.is_bv_type()
        ):
            return None
        return self.env.type_manager.FPType(*fp_format)

    def walk_fp_to_fp_unsigned(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        fp_format = self._valid_fp_format(formula)
        if (
            len(args) != 2
            or fp_format is None
            or args[0] is None
            or not args[0].is_rm_type()
            or args[1] is None
            or not args[1].is_bv_type()
        ):
            return None
        return self.env.type_manager.FPType(*fp_format)

    @walkers.handles(op.FP_TO_UBV, op.FP_TO_SBV)
    def walk_fp_to_bv(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if (
            len(args) != 2
            or args[0] is None
            or not args[0].is_rm_type()
            or self._same_fp_type(args[1:]) is None
        ):
            return None
        try:
            width = formula.fp_conversion_width()
        except (AssertionError, TypeError, ValueError, PysmtTypeError):
            return None
        if not isinstance(width, int) or isinstance(width, bool) or width <= 0:
            return None
        return self.env.type_manager.BVType(width)

    def walk_fp_to_real(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        if len(args) != 1 or self._same_fp_type(args) is None:
            return None
        return REAL

    def walk_symbol(
        self, formula: FNode, args: List[Any], **kwargs
    ) -> Optional[PySMTType]:
        assert formula is not None
        assert len(args) == 0
        return formula.symbol_type()

    @walkers.handles(op.FORALL, op.EXISTS)
    def walk_quantifier(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        # pylint: disable=unused-argument
        assert formula is not None
        assert len(args) == 1
        if args[0] == BOOL:
            return BOOL
        return None

    def walk_function(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        name = formula.function_name()
        assert name.is_symbol()
        tp = name.symbol_type()
        assert tp.is_function_type()

        if len(args) != len(cast(types._FunctionType, tp).param_types):
            return None

        for arg, p_type in zip(args, cast(types._FunctionType, tp).param_types):
            if arg != p_type:
                return None

        return cast(types._FunctionType, tp).return_type

    def walk_str_charat(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        assert formula is not None
        if len(args) == 2 and args[0].is_string_type() and args[1].is_int_type():
            return STRING
        return None

    def walk_str_indexof(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        assert formula is not None
        if (
            len(args) == 3
            and args[0].is_string_type()
            and args[1].is_string_type()
            and args[2].is_int_type()
        ):
            return INT
        return None

    def walk_str_substr(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        assert formula is not None
        if (
            len(args) == 3
            and args[0].is_string_type()
            and args[1].is_int_type()
            and args[2].is_int_type()
        ):
            return STRING
        return None

    def walk_array_select(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        assert formula is not None
        if None in args:
            return None
        if (
            args[0].is_array_type()
            and cast(types._ArrayType, args[0]).index_type == args[1]
        ):
            return cast(types._ArrayType, args[0]).elem_type
        return None

    def walk_array_store(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        assert formula is not None
        if None in args:
            return None
        if (
            args[0].is_array_type()
            and cast(types._ArrayType, args[0]).index_type == args[1]
            and cast(types._ArrayType, args[0]).elem_type == args[2]
        ):
            return args[0]
        return None

    def walk_array_value(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        assert formula is not None
        if None in args:
            return None

        default_type = args[0]
        idx_type = formula.array_value_index_type()
        for i, c in enumerate(args[1:]):
            if i % 2 == 0 and c != idx_type:
                return None  # Wrong index type
            elif i % 2 == 1 and c != default_type:
                return None
        return self.env.type_manager.ArrayType(idx_type, default_type)

    def walk_pow(
        self, formula: FNode, args: List[PySMTType], **kwargs
    ) -> Optional[PySMTType]:
        if args[0] != args[1]:
            return None
        return REAL


# EOC SimpleTypeChecker


def assert_no_boolean_in_args(args: Iterable[FNode]):
    """Enforces that the elements in args are not of BOOL type."""
    for arg in args:
        if arg.get_type() == BOOL:
            raise PysmtTypeError("Boolean Expressions are not allowed in arguments")


def assert_boolean_args(args: Iterable[FNode]):
    """Enforces that the elements in args are of BOOL type."""
    for arg in args:
        t = arg.get_type()
        if t != BOOL:
            raise PysmtTypeError("%s is not allowed in arguments" % t)


def assert_same_type_args(args: Sequence[FNode]):
    """Enforces that all elements in args have the same type."""
    ref_t = args[0].get_type()
    for arg in args[1:]:
        t = arg.get_type()
        if t != ref_t:
            raise PysmtTypeError(
                "Arguments should be of the same type!\n"
                + str([str((a, a.get_type())) for a in args])
            )


def assert_args_type_in(args: Iterable[FNode], allowed_types: Set[PySMTType]):
    """Enforces that the type of the arguments is an allowed type"""
    for arg in args:
        t = arg.get_type()
        if t not in allowed_types:
            raise PysmtTypeError(
                "Argument is of type %s, but one of %s was expected!\n"
                % (t, str(allowed_types))
            )
