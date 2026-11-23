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
"""Tests of the evaluation of constant FP operations (pysmt.floating_point)."""

import bisect
import itertools
from fractions import Fraction

import pysmt.floating_point as F
from pysmt.logics import QF_BVFPLRA
from pysmt.shortcuts import (
    BV,
    FP,
    FPFMA,
    RNA,
    RNE,
    RTN,
    RTP,
    RTZ,
    And,
    Equals,
    FPAdd,
    FPDiv,
    FPEq,
    FPIsNormal,
    FPIsSubnormal,
    FPLEq,
    FPLt,
    FPMax,
    FPMin,
    FPMul,
    FPRem,
    FPRoundToIntegral,
    FPSqrt,
    FPSub,
    FPToFP,
    FPToReal,
    FPToSBV,
    FPToUBV,
    Iff,
    Not,
    Solver,
)
from tests import TestCase, main, skipIfSolverNotAvailable

ROUNDING_MODES = [F.RNE, F.RNA, F.RTP, F.RTN, F.RTZ]


class ReferenceFormat(object):
    """Rounds exact values by looking up the representable values of a
    (small) format, independently of pysmt.floating_point.round_rational."""

    def __init__(self, eb, sb):
        self.eb, self.sb = eb, sb
        self.values = [
            F.FPValue(eb, sb, s, e, m)
            for s in (0, 1)
            for e in range(1 << eb)
            for m in range(1 << (sb - 1))
        ]
        self.finite = [v for v in self.values if v.is_finite()]
        self.positive = {
            v.magnitude(): v for v in self.finite if not v.is_zero() and not v.negative
        }
        bias = (1 << (eb - 1)) - 1
        self.beyond = Fraction(2) ** (bias + 1)  # the first value past the format
        self.candidates = [Fraction(0)] + sorted(self.positive) + [self.beyond]

    def encode(self, magnitude, negative):
        if magnitude == self.beyond:
            return F.FPValue.infinity(self.eb, self.sb, negative)
        if magnitude == 0:
            return F.FPValue.zero(self.eb, self.sb, negative)
        return (
            F.fp_neg(self.positive[magnitude]) if negative else self.positive[magnitude]
        )

    def round(self, rm, value):
        negative = value < 0
        magnitude = abs(value)
        if magnitude >= self.beyond:
            if rm in (F.RNE, F.RNA) or rm == (F.RTN if negative else F.RTP):
                return F.FPValue.infinity(self.eb, self.sb, negative)
            return F.FPValue.largest(self.eb, self.sb, negative)
        i = bisect.bisect_left(self.candidates, magnitude)
        if self.candidates[i] == magnitude:
            return self.encode(magnitude, negative)
        lo, hi = self.candidates[i - 1], self.candidates[i]
        if rm == F.RTZ or rm == (F.RTP if negative else F.RTN):
            pick = lo
        elif rm in (F.RTP, F.RTN):
            pick = hi
        elif magnitude - lo != hi - magnitude:
            pick = lo if magnitude - lo < hi - magnitude else hi
        elif rm == F.RNA:
            pick = hi
        else:
            even = lo == 0 or self.positive[lo].significand % 2 == 0
            pick = lo if even else hi
        return self.encode(pick, negative)

    def round_to_integer(self, rm, value):
        floor = value.numerator // value.denominator
        if value == floor:
            return floor
        if rm == F.RTZ:
            return floor if value > 0 else floor + 1
        if rm in (F.RTP, F.RTN):
            return floor + 1 if rm == F.RTP else floor
        if value - floor != Fraction(1, 2):
            return floor if value - floor < Fraction(1, 2) else floor + 1
        if rm == F.RNA:
            return floor + 1 if value > 0 else floor
        return floor if floor % 2 == 0 else floor + 1


class TestFPEvaluation(TestCase):
    def check_against_reference(self, eb, sb, ternary):
        ref = ReferenceFormat(eb, sb)
        for rm in ROUNDING_MODES:
            for x, y in itertools.product(ref.finite, ref.finite):
                exact = x.value() + y.value()
                if exact != 0:
                    self.assertEqual(F.fp_add(rm, x, y), ref.round(rm, exact))
                if not x.is_zero() and not y.is_zero():
                    exact = x.value() * y.value()
                    self.assertEqual(F.fp_mul(rm, x, y), ref.round(rm, exact))
                    exact = x.value() / y.value()
                    self.assertEqual(F.fp_div(rm, x, y), ref.round(rm, exact))
            if ternary:
                for x, y, z in itertools.product(ref.finite, ref.finite, ref.finite):
                    exact = x.value() * y.value() + z.value()
                    if exact != 0:
                        self.assertEqual(F.fp_fma(rm, x, y, z), ref.round(rm, exact))
            for x in ref.finite:
                if x.is_zero():
                    continue
                n = ref.round_to_integer(rm, x.value())
                expected = (
                    F.FPValue.zero(eb, sb, x.negative)
                    if n == 0
                    else ref.round(F.RNE, Fraction(n))
                )
                self.assertEqual(F.fp_round_to_integral(rm, x), expected)
                if not x.negative:
                    squares = [c * c for c in ref.candidates]
                    i = bisect.bisect_left(squares, x.value())
                    if squares[i] == x.value():
                        root = ref.candidates[i]
                    elif rm in (F.RTZ, F.RTN):
                        root = ref.candidates[i - 1]
                    elif rm == F.RTP:
                        root = ref.candidates[i]
                    else:
                        lo, hi = ref.candidates[i - 1], ref.candidates[i]
                        root = lo if x.value() < ((lo + hi) / 2) ** 2 else hi
                    self.assertEqual(F.fp_sqrt(rm, x), ref.encode(root, False))

    def test_tiny_formats_exhaustively(self):
        # Formats with eb = 2 are where z3 and cvc5 disagree with the theory
        self.check_against_reference(2, 3, ternary=True)
        self.check_against_reference(3, 3, ternary=False)

    def test_special_values(self):
        one = F.FPValue(5, 11, 0, 15, 0)
        zero, minus_zero = F.FPValue.zero(5, 11, False), F.FPValue.zero(5, 11, True)
        inf, nan = F.FPValue.infinity(5, 11, False), F.FPValue.nan(5, 11)
        self.assertEqual(F.fp_add(F.RNE, inf, F.fp_neg(inf)), nan)
        self.assertEqual(F.fp_mul(F.RNE, inf, zero), nan)
        self.assertEqual(F.fp_div(F.RNE, one, minus_zero), F.fp_neg(inf))
        self.assertEqual(F.fp_add(F.RNE, zero, minus_zero), zero)
        self.assertEqual(F.fp_add(F.RTN, zero, minus_zero), minus_zero)
        self.assertEqual(F.fp_sqrt(F.RNE, minus_zero), minus_zero)
        self.assertEqual(F.fp_sqrt(F.RNE, F.fp_neg(one)), nan)
        self.assertEqual(F.fp_rem(one, zero), nan)
        self.assertEqual(F.fp_rem(one, inf), one)
        self.assertEqual(F.fp_fma(F.RNE, inf, zero, one), nan)
        self.assertIsNone(F.fp_min(zero, minus_zero))
        self.assertEqual(F.fp_min(nan, one), one)
        self.assertFalse(F.fp_eq(nan, nan))
        self.assertTrue(F.fp_eq(zero, minus_zero))
        self.assertFalse(F.fp_is_negative(nan) or F.fp_is_positive(nan))
        self.assertIsNone(F.fp_to_real(inf))
        self.assertIsNone(F.fp_to_ubv(F.RNE, F.fp_neg(one), 8))
        self.assertEqual(F.fp_to_ubv(F.RTZ, F.FPValue(5, 11, 1, 14, 0), 8), 0)
        # Every NaN has the canonical encoding
        self.assertEqual(F.FPValue(5, 11, 1, 31, 5), nan)

    @skipIfSolverNotAvailable("z3")
    def test_agreement_with_z3(self):
        values = [
            FP(BV(s, 1), BV(e, 5), BV(m, 10))
            for s, e, m in [
                (0, 0, 0), (1, 0, 0), (0, 31, 0), (1, 31, 0), (0, 31, 1),
                (0, 0, 1), (1, 0, 1023), (0, 1, 0), (0, 30, 1023), (1, 30, 1023),
                (0, 15, 0), (1, 15, 512), (0, 16, 1), (0, 10, 333), (1, 25, 77),
            ]
        ]  # fmt: skip
        pairs = list(itertools.product(values, values))
        terms = []
        for rm in (RNE(), RNA(), RTP(), RTN(), RTZ()):
            for op in (FPAdd, FPSub, FPMul, FPDiv):
                terms.extend(op(rm, x, y) for x, y in pairs)
            terms.extend(FPFMA(rm, x, y, x) for x, y in pairs)
            terms.extend(FPSqrt(rm, x) for x in values)
            terms.extend(FPRoundToIntegral(rm, x) for x in values)
            terms.extend(FPToFP(rm, x, 3, 4) for x in values)
            terms.extend(FPToFP(rm, x, 8, 24) for x in values)
            terms.extend(FPToUBV(rm, x, 8) for x in values)
            terms.extend(FPToSBV(rm, x, 8) for x in values)
        for op in (FPRem, FPMin, FPMax, FPLt, FPLEq, FPEq):
            terms.extend(op(x, y) for x, y in pairs)
        terms.extend(FPToReal(x) for x in values)
        terms.extend(FPIsNormal(x) for x in values)
        terms.extend(FPIsSubnormal(x) for x in values)

        checks = []
        for term in terms:
            value = term.simplify()
            if not value.is_constant():
                continue  # Unspecified
            if term.get_type().is_bool_type():
                checks.append(Iff(term, value))
            else:
                checks.append(Equals(term, value))
        self.assertGreater(len(checks), 7000)
        with Solver(name="z3", logic=QF_BVFPLRA) as solver:
            solver.add_assertion(Not(And(checks)))
            self.assertFalse(solver.solve())


if __name__ == "__main__":
    main()
