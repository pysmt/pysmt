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
"""Exact semantics of the SMT-LIB FloatingPoint theory on constant values.

The simplifier uses this module to evaluate the floating-point operations
whose arguments are all constants. Every operation is computed on exact
rational values and rounded once, as the SMT-LIB FloatingPoint theory
(following IEEE 754-2008) specifies.

Results that the theory leaves unspecified are returned as None: fp.min and
fp.max of the two zeros, fp.to_ubv and fp.to_sbv of NaN, of an infinity or
of a value out of range, and fp.to_real of NaN or of an infinity.
"""

import math
from fractions import Fraction
from math import isqrt
from typing import Optional, Tuple, Union

# Rounding modes, named as by FNode.rounding_mode()
RNE = "RNE"
RNA = "RNA"
RTP = "RTP"
RTN = "RTN"
RTZ = "RTZ"


def _pow2(exponent: int) -> Fraction:
    if exponent >= 0:
        return Fraction(1 << exponent)
    return Fraction(1, 1 << -exponent)


class FPValue(object):
    """A value of sort (_ FloatingPoint eb sb), stored as its IEEE encoding.

    The theory has a single NaN value, so every NaN is stored with the
    canonical encoding (sign 0, significand 1).
    """

    __slots__ = ("eb", "sb", "sign", "exponent", "significand")

    def __init__(self, eb: int, sb: int, sign: int, exponent: int, significand: int):
        if exponent == (1 << eb) - 1 and significand != 0:
            sign, significand = 0, 1
        self.eb = eb
        self.sb = sb
        self.sign = sign
        self.exponent = exponent
        self.significand = significand

    @classmethod
    def nan(cls, eb: int, sb: int) -> "FPValue":
        return cls(eb, sb, 0, (1 << eb) - 1, 1)

    @classmethod
    def infinity(cls, eb: int, sb: int, negative: bool) -> "FPValue":
        return cls(eb, sb, int(negative), (1 << eb) - 1, 0)

    @classmethod
    def zero(cls, eb: int, sb: int, negative: bool) -> "FPValue":
        return cls(eb, sb, int(negative), 0, 0)

    @classmethod
    def largest(cls, eb: int, sb: int, negative: bool) -> "FPValue":
        """The finite value of largest magnitude."""
        return cls(eb, sb, int(negative), (1 << eb) - 2, (1 << (sb - 1)) - 1)

    @classmethod
    def from_ieee_bits(cls, eb: int, sb: int, bits: int) -> "FPValue":
        """The value of an IEEE interchange encoding of eb + sb bits."""
        return cls(
            eb,
            sb,
            bits >> (eb + sb - 1),
            (bits >> (sb - 1)) & ((1 << eb) - 1),
            bits & ((1 << (sb - 1)) - 1),
        )

    def triple(self) -> Tuple[int, int, int]:
        """The (sign, exponent, significand) arguments of the fp constructor."""
        return (self.sign, self.exponent, self.significand)

    @property
    def negative(self) -> bool:
        return self.sign == 1

    def is_nan(self) -> bool:
        return self.exponent == (1 << self.eb) - 1 and self.significand != 0

    def is_infinite(self) -> bool:
        return self.exponent == (1 << self.eb) - 1 and self.significand == 0

    def is_finite(self) -> bool:
        """True for the zeros, the subnormal and the normal values."""
        return self.exponent != (1 << self.eb) - 1

    def is_zero(self) -> bool:
        return self.exponent == 0 and self.significand == 0

    def is_subnormal(self) -> bool:
        return self.exponent == 0 and self.significand != 0

    def is_normal(self) -> bool:
        return 0 < self.exponent < (1 << self.eb) - 1

    def magnitude(self) -> Fraction:
        """The exact absolute value of a finite value."""
        assert self.is_finite()
        bias = (1 << (self.eb - 1)) - 1
        if self.exponent == 0:
            return self.significand * _pow2(1 - bias - (self.sb - 1))
        significand = (1 << (self.sb - 1)) | self.significand
        return significand * _pow2(self.exponent - bias - (self.sb - 1))

    def value(self) -> Fraction:
        """The exact value of a finite value (0 for both zeros)."""
        magnitude = self.magnitude()
        return -magnitude if self.negative else magnitude

    def __eq__(self, other: object) -> bool:
        return isinstance(other, FPValue) and (
            self.eb,
            self.sb,
            self.sign,
            self.exponent,
            self.significand,
        ) == (other.eb, other.sb, other.sign, other.exponent, other.significand)

    def __hash__(self) -> int:
        return hash((self.eb, self.sb, self.sign, self.exponent, self.significand))

    def __repr__(self) -> str:
        return "FPValue(%d, %d, %d, %d, %d)" % (
            self.eb,
            self.sb,
            self.sign,
            self.exponent,
            self.significand,
        )


def _round_integer(numerator: int, denominator: int, rm: str, negative: bool) -> int:
    """Rounds the non-negative rational numerator/denominator to an integer.

    `negative` is the sign of the value being rounded, which decides the
    direction of RTP and RTN.
    """
    quotient, remainder = divmod(numerator, denominator)
    if remainder == 0:
        return quotient
    if rm == RNE:
        twice = 2 * remainder
        if twice > denominator or (twice == denominator and quotient & 1):
            return quotient + 1
        return quotient
    if rm == RNA:
        return quotient + 1 if 2 * remainder >= denominator else quotient
    if rm == RTP:
        return quotient if negative else quotient + 1
    if rm == RTN:
        return quotient + 1 if negative else quotient
    assert rm == RTZ, rm
    return quotient


def round_rational(eb: int, sb: int, rm: str, value: Fraction) -> FPValue:
    """Rounds a non-zero rational to the format (eb, sb)."""
    assert value != 0
    negative = value < 0
    numerator, denominator = abs(value.numerator), value.denominator
    bias = (1 << (eb - 1)) - 1
    emin = 1 - bias

    # e = floor(log2(|value|))
    e = numerator.bit_length() - denominator.bit_length()
    if e >= 0:
        below = numerator < (denominator << e)
    else:
        below = (numerator << -e) < denominator
    if below:
        e -= 1

    # Exponent of the last bit of the significand: the subnormal values all
    # share the one of the smallest normal exponent.
    ulp = max(e, emin) - (sb - 1)
    if ulp >= 0:
        significand = _round_integer(numerator, denominator << ulp, rm, negative)
    else:
        significand = _round_integer(numerator << -ulp, denominator, rm, negative)
    if significand == 1 << sb:
        # Rounding carried into the next binade
        significand >>= 1
        ulp += 1

    if significand == 0:
        return FPValue.zero(eb, sb, negative)
    if significand < (1 << (sb - 1)):
        return FPValue(eb, sb, int(negative), 0, significand)
    exponent = ulp + (sb - 1) + bias
    if exponent >= (1 << eb) - 1:
        # Overflow
        if rm in (RNE, RNA) or (rm == RTP and not negative) or (rm == RTN and negative):
            return FPValue.infinity(eb, sb, negative)
        return FPValue.largest(eb, sb, negative)
    return FPValue(eb, sb, int(negative), exponent, significand - (1 << (sb - 1)))


def _exact_zero(x: FPValue, y_negative: bool, rm: str, y_zero: bool) -> FPValue:
    """The zero resulting from an exact sum x + y equal to zero.

    The sum of two zeros of the same sign keeps that sign, any other exact
    zero sum is +0, or -0 when rounding toward negative.
    """
    if x.is_zero() and y_zero and x.negative == y_negative:
        return FPValue.zero(x.eb, x.sb, x.negative)
    return FPValue.zero(x.eb, x.sb, rm == RTN)


def fp_abs(x: FPValue) -> FPValue:
    if x.is_nan():
        return x
    return FPValue(x.eb, x.sb, 0, x.exponent, x.significand)


def fp_neg(x: FPValue) -> FPValue:
    if x.is_nan():
        return x
    return FPValue(x.eb, x.sb, 1 - x.sign, x.exponent, x.significand)


def fp_add(rm: str, x: FPValue, y: FPValue) -> FPValue:
    eb, sb = x.eb, x.sb
    if x.is_nan() or y.is_nan():
        return FPValue.nan(eb, sb)
    if x.is_infinite():
        if y.is_infinite() and x.sign != y.sign:
            return FPValue.nan(eb, sb)
        return x
    if y.is_infinite():
        return y
    exact = x.value() + y.value()
    if exact == 0:
        return _exact_zero(x, y.negative, rm, y.is_zero())
    return round_rational(eb, sb, rm, exact)


def fp_sub(rm: str, x: FPValue, y: FPValue) -> FPValue:
    return fp_add(rm, x, fp_neg(y))


def fp_mul(rm: str, x: FPValue, y: FPValue) -> FPValue:
    eb, sb = x.eb, x.sb
    if x.is_nan() or y.is_nan():
        return FPValue.nan(eb, sb)
    negative = x.negative != y.negative
    if x.is_infinite() or y.is_infinite():
        if x.is_zero() or y.is_zero():
            return FPValue.nan(eb, sb)
        return FPValue.infinity(eb, sb, negative)
    if x.is_zero() or y.is_zero():
        return FPValue.zero(eb, sb, negative)
    return round_rational(eb, sb, rm, x.value() * y.value())


def fp_div(rm: str, x: FPValue, y: FPValue) -> FPValue:
    eb, sb = x.eb, x.sb
    if x.is_nan() or y.is_nan():
        return FPValue.nan(eb, sb)
    negative = x.negative != y.negative
    if x.is_infinite():
        if y.is_infinite():
            return FPValue.nan(eb, sb)
        return FPValue.infinity(eb, sb, negative)
    if y.is_infinite():
        return FPValue.zero(eb, sb, negative)
    if y.is_zero():
        if x.is_zero():
            return FPValue.nan(eb, sb)
        return FPValue.infinity(eb, sb, negative)
    if x.is_zero():
        return FPValue.zero(eb, sb, negative)
    return round_rational(eb, sb, rm, x.value() / y.value())


def fp_fma(rm: str, x: FPValue, y: FPValue, z: FPValue) -> FPValue:
    """(x * y) + z, rounded once."""
    eb, sb = x.eb, x.sb
    if x.is_nan() or y.is_nan() or z.is_nan():
        return FPValue.nan(eb, sb)
    product_negative = x.negative != y.negative
    if x.is_infinite() or y.is_infinite():
        if x.is_zero() or y.is_zero():
            return FPValue.nan(eb, sb)
        if z.is_infinite() and z.negative != product_negative:
            return FPValue.nan(eb, sb)
        return FPValue.infinity(eb, sb, product_negative)
    if z.is_infinite():
        return z
    exact = x.value() * y.value() + z.value()
    if exact == 0:
        product_zero = x.is_zero() or y.is_zero()
        if product_zero and z.is_zero() and product_negative == z.negative:
            return FPValue.zero(eb, sb, z.negative)
        return FPValue.zero(eb, sb, rm == RTN)
    return round_rational(eb, sb, rm, exact)


def fp_sqrt(rm: str, x: FPValue) -> FPValue:
    eb, sb = x.eb, x.sb
    if x.is_nan():
        return x
    if x.is_zero():
        return x
    if x.negative:
        return FPValue.nan(eb, sb)
    if x.is_infinite():
        return x
    value = x.value()
    numerator, denominator = value.numerator, value.denominator
    # Compute root = floor(sqrt(value) * 2**k) with at least sb + 2 bits:
    # rounding (2 * root + inexact) / 2**(k + 1) then gives the same result
    # as rounding sqrt(value), since no rounding boundary lies between them.
    e = numerator.bit_length() - denominator.bit_length()
    k = sb + 2 - (e - 1) // 2
    if k >= 0:
        scaled_num, scaled_den = numerator << (2 * k), denominator
    else:
        scaled_num, scaled_den = numerator, denominator << (-2 * k)
    integer_part, remainder = divmod(scaled_num, scaled_den)
    root = isqrt(integer_part)
    inexact = remainder != 0 or root * root != integer_part
    approximation = (2 * root + int(inexact)) * _pow2(-(k + 1))
    return round_rational(eb, sb, rm, approximation)


def fp_rem(x: FPValue, y: FPValue) -> FPValue:
    """The IEEE remainder x - y * n, with n the integer nearest to x / y."""
    eb, sb = x.eb, x.sb
    if x.is_nan() or y.is_nan() or x.is_infinite() or y.is_zero():
        return FPValue.nan(eb, sb)
    if y.is_infinite() or x.is_zero():
        return x
    n = round(x.value() / y.value())  # ties to even
    remainder = x.value() - y.value() * n
    if remainder == 0:
        return FPValue.zero(eb, sb, x.negative)
    # The remainder is exactly representable
    return round_rational(eb, sb, RNE, remainder)


def fp_round_to_integral(rm: str, x: FPValue) -> FPValue:
    if not x.is_finite() or x.is_zero():
        return x
    magnitude = x.magnitude()
    n = _round_integer(magnitude.numerator, magnitude.denominator, rm, x.negative)
    if n == 0:
        return FPValue.zero(x.eb, x.sb, x.negative)
    # An integer in the binade of x (or next to it) is exactly representable
    return round_rational(x.eb, x.sb, RNE, Fraction(-n if x.negative else n))


def _order_key(x: FPValue) -> Tuple[int, Fraction]:
    if x.is_infinite():
        return (-1 if x.negative else 1, Fraction(0))
    return (0, x.value())


def fp_lt(x: FPValue, y: FPValue) -> bool:
    if x.is_nan() or y.is_nan():
        return False
    return _order_key(x) < _order_key(y)


def fp_leq(x: FPValue, y: FPValue) -> bool:
    if x.is_nan() or y.is_nan():
        return False
    return _order_key(x) <= _order_key(y)


def fp_eq(x: FPValue, y: FPValue) -> bool:
    """IEEE equality: false on NaN, true on the two zeros."""
    if x.is_nan() or y.is_nan():
        return False
    return _order_key(x) == _order_key(y)


def fp_min(x: FPValue, y: FPValue) -> Optional[FPValue]:
    if x.is_nan():
        return y
    if y.is_nan():
        return x
    if x.is_zero() and y.is_zero() and x.sign != y.sign:
        return None  # Unspecified
    return x if fp_leq(x, y) else y


def fp_max(x: FPValue, y: FPValue) -> Optional[FPValue]:
    if x.is_nan():
        return y
    if y.is_nan():
        return x
    if x.is_zero() and y.is_zero() and x.sign != y.sign:
        return None  # Unspecified
    return x if fp_leq(y, x) else y


def fp_is_negative(x: FPValue) -> bool:
    return not x.is_nan() and x.negative


def fp_is_positive(x: FPValue) -> bool:
    return not x.is_nan() and not x.negative


def fp_to_fp(rm: str, x: FPValue, eb: int, sb: int) -> FPValue:
    """Converts x to the format (eb, sb)."""
    if x.is_nan():
        return FPValue.nan(eb, sb)
    if x.is_infinite():
        return FPValue.infinity(eb, sb, x.negative)
    if x.is_zero():
        return FPValue.zero(eb, sb, x.negative)
    return round_rational(eb, sb, rm, x.value())


def real_to_fp(rm: str, value: Fraction, eb: int, sb: int) -> FPValue:
    """Converts a real (or an integer) to the format (eb, sb)."""
    if value == 0:
        return FPValue.zero(eb, sb, False)
    return round_rational(eb, sb, rm, value)


def sbv_to_fp(rm: str, bits: int, width: int, eb: int, sb: int) -> FPValue:
    """Converts a two's complement bit-vector to the format (eb, sb)."""
    value = bits - (1 << width) if bits >> (width - 1) else bits
    return real_to_fp(rm, Fraction(value), eb, sb)


def ubv_to_fp(rm: str, bits: int, eb: int, sb: int) -> FPValue:
    """Converts an unsigned bit-vector to the format (eb, sb)."""
    return real_to_fp(rm, Fraction(bits), eb, sb)


def _to_integer(rm: str, x: FPValue) -> Optional[int]:
    if not x.is_finite():
        return None
    magnitude = x.magnitude()
    n = _round_integer(magnitude.numerator, magnitude.denominator, rm, x.negative)
    return -n if x.negative else n


def fp_to_ubv(rm: str, x: FPValue, width: int) -> Optional[int]:
    """The unsigned bit-vector value of x rounded to an integer, if in range."""
    n = _to_integer(rm, x)
    if n is None or not 0 <= n < (1 << width):
        return None  # Unspecified
    return n


def fp_to_sbv(rm: str, x: FPValue, width: int) -> Optional[int]:
    """The two's complement value of x rounded to an integer, if in range."""
    n = _to_integer(rm, x)
    if n is None or not -(1 << (width - 1)) <= n < (1 << (width - 1)):
        return None  # Unspecified
    return n % (1 << width)


def fp_to_real(x: FPValue) -> Optional[Fraction]:
    if not x.is_finite():
        return None  # Unspecified
    return x.value()


def from_number(
    value: Union[int, float, Fraction, str], eb: int, sb: int, rm: str
) -> FPValue:
    """The value of the format (eb, sb) nearest to a Python number.

    A float keeps its NaN, infinities and the sign of its zeros; any other
    number (or string accepted by fractions.Fraction) is rounded with rm.
    """
    if isinstance(value, float):
        if math.isnan(value):
            return FPValue.nan(eb, sb)
        if math.isinf(value):
            return FPValue.infinity(eb, sb, value < 0)
        if value == 0:
            return FPValue.zero(eb, sb, math.copysign(1.0, value) < 0)
    return real_to_fp(rm, Fraction(value), eb, sb)
