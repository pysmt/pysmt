#
# This file is part of pySMT.
#
#   Copyright 2015 Andrea Micheli and Marco Gario
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

from io import StringIO
from itertools import combinations

from pysmt.environment import Environment
from pysmt.exceptions import PysmtSyntaxError, PysmtTypeError, PysmtValueError
from pysmt.logics import (
    QF_ABVFP,
    QF_ABVFPLRA,
    QF_AUFBVFP,
    QF_AUFBVLIRA,
    QF_BVFP,
    QF_BVFPLRA,
    QF_FP,
    QF_FPLRA,
)
from pysmt.oracles import get_logic
from pysmt.rewritings import propagate_toplevel
from pysmt.shortcuts import (
    BV,
    BVULT,
    FP,
    FPFMA,
    LT,
    RNA,
    RNE,
    RTN,
    RTP,
    RTZ,
    And,
    Array,
    BVAdd,
    BVExtract,
    Equals,
    FPAbs,
    FPAdd,
    FPDiv,
    FPEq,
    FPFromIEEEBV,
    FPGEq,
    FPGt,
    FPIsInfinite,
    FPIsNaN,
    FPIsNegative,
    FPIsNormal,
    FPIsPositive,
    FPIsSubnormal,
    FPIsZero,
    FPLEq,
    FPLt,
    FPMax,
    FPMin,
    FPMinusInfinity,
    FPMinusZero,
    FPMul,
    FPNaN,
    FPNeg,
    FPPlusInfinity,
    FPPlusZero,
    FPRem,
    FPRoundToIntegral,
    FPSqrt,
    FPSub,
    FPToFP,
    FPToFPUnsigned,
    FPToReal,
    FPToSBV,
    FPToUBV,
    FPVal,
    Function,
    Iff,
    Int,
    Ite,
    Not,
    Plus,
    Real,
    Select,
    Solver,
    String,
    Symbol,
    Times,
    Type,
)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.printers import to_smtlib
from pysmt.smtlib.script import smtlibscript_from_formula
from pysmt.smtlib.utils import SmtLibModelValidationSimplifier
from pysmt.solvers.eager import EagerModel
from pysmt.typing import (
    BOOL,
    FLOAT16,
    FLOAT32,
    FLOAT64,
    FLOAT128,
    INT,
    REAL,
    ArrayType,
    BVType,
    FPType,
    FunctionType,
    RMType,
)
from tests import TestCase, main, skipIfSolverNotAvailable


class TestFP(TestCase):
    def setUp(self):
        super(TestFP, self).setUp()

        # Binary16 encodings used throughout the tests.
        self.one = FP(BV(0, 1), BV(15, 5), BV(0, 10))
        self.two = FP(BV(0, 1), BV(16, 5), BV(0, 10))
        self.minus_one = FP(BV(1, 1), BV(15, 5), BV(0, 10))

    def _all_operators_formula(self):
        """Build one well-typed formula containing every public FP operator."""
        x = Symbol("fp_x", FLOAT16)
        y = Symbol("fp_y", FLOAT16)
        rne = RNE()

        fp_terms = [
            FPAbs(x),
            FPNeg(x),
            FPSqrt(rne, x),
            FPRoundToIntegral(rne, x),
            FPAdd(rne, x, y),
            FPSub(rne, x, y),
            FPMul(rne, x, y),
            FPDiv(rne, x, y),
            FPFMA(rne, x, y, self.one),
            FPRem(x, y),
            FPMin(x, y),
            FPMax(x, y),
            FPFromIEEEBV(BV(0x3C00, 16), 5, 11),
            FPToFP(rne, x, 8, 24),
            FPToFP(rne, Real(1), 5, 11),
            FPToFP(rne, BV(1, 8), 5, 11),
            FPToFPUnsigned(rne, BV(1, 8), 5, 11),
        ]
        other_terms = [
            FPToUBV(rne, x, 8),
            FPToSBV(rne, x, 8),
            FPToReal(x),
        ]
        predicates = [
            FPLEq(x, y),
            FPLt(x, y),
            FPEq(x, y),
            FPIsNormal(x),
            FPIsSubnormal(x),
            FPIsZero(x),
            FPIsInfinite(x),
            FPIsNaN(x),
            FPIsNegative(x),
            FPIsPositive(x),
        ]

        checks = [Equals(term, term) for term in fp_terms + other_terms]
        checks.extend(Iff(predicate, predicate) for predicate in predicates)
        checks.extend(
            Equals(mode, mode) for mode in (RNE(), RNA(), RTP(), RTN(), RTZ())
        )
        return And(checks)

    def test_fp_types(self):
        aliases = [
            (FLOAT16, 5, 11),
            (FLOAT32, 8, 24),
            (FLOAT64, 11, 53),
            (FLOAT128, 15, 113),
        ]
        for alias, eb, sb in aliases:
            with self.subTest(alias=alias):
                self.assertIs(FPType(eb, sb), alias)
                self.assertTrue(alias.is_fp_type())
                self.assertTrue(alias.is_fp_type(eb, sb))
                self.assertEqual(alias.exponent_size, eb)
                self.assertEqual(alias.significand_size, sb)
                self.assertEqual(
                    alias.as_smtlib(False), "(_ FloatingPoint %d %d)" % (eb, sb)
                )

        rm_type = RMType()
        self.assertTrue(rm_type.is_rm_type())
        self.assertFalse(rm_type.is_fp_type())
        self.assertEqual(rm_type.as_smtlib(False), "RoundingMode")
        self.assertFalse(BOOL.is_fp_type())
        self.assertFalse(BOOL.is_rm_type())

        with self.assertRaises(PysmtValueError):
            FPType(1, 11)
        with self.assertRaises(PysmtValueError):
            FPType(5, 1)

    def test_type_and_formula_normalization(self):
        src_env = Environment()
        dst_env = Environment()

        with src_env:
            src_type = FPType(6, 13)
            src_x = Symbol("nonstandard_fp", src_type)
            src_formula = FPLEq(FPAdd(RNE(), src_x, src_x), src_x)
            src_to_fp = FPToFP(RNE(), src_x, 8, 24)
            src_to_bv = FPToUBV(RTZ(), src_x, 17)

        with dst_env:
            dst_type = FPType(6, 13)
            normalized = dst_env.formula_manager.normalize(src_formula)
            normalized_to_fp = dst_env.formula_manager.normalize(src_to_fp)
            normalized_to_bv = dst_env.formula_manager.normalize(src_to_bv)

        self.assertEqual(normalized.get_type(), BOOL)
        normalized_x = next(iter(normalized.get_free_variables()))
        self.assertIs(normalized_x.symbol_type(), dst_type)
        self.assertIsNot(src_type, dst_type)
        self.assertNotEqual(normalized, src_formula)
        self.assertEqual(normalized_to_fp.fp_conversion_format(), (8, 24))
        self.assertEqual(normalized_to_fp.get_type(), FLOAT32)
        self.assertEqual(normalized_to_bv.fp_conversion_width(), 17)
        self.assertEqual(normalized_to_bv.get_type(), BVType(17))

    def test_fp_literals_and_special_values(self):
        self.assertIsNotNone(self.one)
        self.assertEqual(self.one.get_type(), FLOAT16)
        self.assertTrue(self.one.is_constant())
        self.assertEqual(self.one.constant_type(), FLOAT16)
        self.assertEqual(self.one.get_free_variables(), frozenset())

        specials = [
            FPPlusZero(5, 11),
            FPMinusZero(5, 11),
            FPPlusInfinity(5, 11),
            FPMinusInfinity(5, 11),
            FPNaN(5, 11),
        ]
        for value in specials:
            with self.subTest(value=value):
                self.assertEqual(value.get_type(), FLOAT16)
                self.assertTrue(value.is_constant())
                self.assertEqual(value.constant_type(), FLOAT16)

        with self.assertRaises(PysmtTypeError):
            FP(BV(0, 2), BV(15, 5), BV(0, 10))

    def test_symbolic_fp_components_keep_free_variables(self):
        sign = Symbol("fp_sign", BVType(1))
        exponent = Symbol("fp_exponent", BVType(5))
        significand = Symbol("fp_significand", BVType(10))

        assembled = FP(sign, exponent, significand)
        self.assertEqual(assembled.get_type(), FLOAT16)
        self.assertFalse(assembled.is_constant())
        self.assertEqual(
            assembled.get_free_variables(), frozenset((sign, exponent, significand))
        )

        rebuilt = assembled.substitute(
            {
                sign: BV(0, 1),
                exponent: BV(15, 5),
                significand: BV(0, 10),
            }
        )
        self.assertEqual(rebuilt, self.one)

    def test_rounding_modes(self):
        modes = (RNE(), RNA(), RTP(), RTN(), RTZ())
        for mode in modes:
            with self.subTest(mode=mode):
                self.assertEqual(mode.get_type(), RMType())
                self.assertTrue(mode.is_constant())
                self.assertEqual(mode.constant_type(), RMType())
        self.assertEqual(len(set(modes)), 5)

    def test_operator_types(self):
        x = Symbol("x", FLOAT16)
        y = Symbol("y", FLOAT16)
        rm = RNE()

        fp_terms = [
            FPAbs(x),
            FPNeg(x),
            FPSqrt(rm, x),
            FPRoundToIntegral(rm, x),
            FPAdd(rm, x, y),
            FPSub(rm, x, y),
            FPMul(rm, x, y),
            FPDiv(rm, x, y),
            FPFMA(rm, x, y, self.one),
            FPRem(x, y),
            FPMin(x, y),
            FPMax(x, y),
        ]
        for term in fp_terms:
            with self.subTest(term=term):
                self.assertEqual(term.get_type(), FLOAT16)

        predicates = [
            FPLEq(x, y),
            FPLt(x, y),
            FPEq(x, y),
            FPIsNormal(x),
            FPIsSubnormal(x),
            FPIsZero(x),
            FPIsInfinite(x),
            FPIsNaN(x),
            FPIsNegative(x),
            FPIsPositive(x),
        ]
        for predicate in predicates:
            with self.subTest(predicate=predicate):
                self.assertEqual(predicate.get_type(), BOOL)
                self.assertTrue(predicate.is_theory_relation())

    def test_conversion_types(self):
        rm = RNE()

        self.assertEqual(FPFromIEEEBV(BV(0x3C00, 16), 5, 11).get_type(), FLOAT16)
        self.assertEqual(FPToFP(rm, self.one, 8, 24).get_type(), FLOAT32)
        self.assertEqual(FPToFP(rm, Real(1), 8, 24).get_type(), FLOAT32)
        self.assertEqual(FPToFP(rm, BV(1, 8), 8, 24).get_type(), FLOAT32)
        self.assertEqual(FPToFPUnsigned(rm, BV(1, 8), 8, 24).get_type(), FLOAT32)
        self.assertEqual(FPToUBV(rm, self.one, 8).get_type(), BVType(8))
        self.assertEqual(FPToSBV(rm, self.one, 8).get_type(), BVType(8))
        self.assertEqual(FPToReal(self.one).get_type(), REAL)

        with self.assertRaises(PysmtTypeError):
            FPFromIEEEBV(BV(0, 15), 5, 11)
        with self.assertRaises(PysmtTypeError):
            FPToFP(Int(0), self.one, 8, 24)
        with self.assertRaises(PysmtTypeError):
            FPToFP(rm, Symbol("bad_fp_source", BOOL), 8, 24)

    def test_rejects_ill_typed_operations(self):
        x16 = Symbol("x16", FLOAT16)
        x32 = Symbol("x32", FLOAT32)

        with self.assertRaises(PysmtTypeError):
            FPAdd(RNE(), x16, x32)
        with self.assertRaises(PysmtTypeError):
            FPAdd(Int(0), x16, x16)
        with self.assertRaises(PysmtTypeError):
            FPRem(x16, x32)
        with self.assertRaises(PysmtTypeError):
            FPIsNaN(Int(0))

    def test_eager_model_completion(self):
        fp_symbol = Symbol("eager_fp", FLOAT16)
        rm_symbol = Symbol("eager_rm", RMType())
        model = EagerModel({})

        self.assertEqual(model.get_value(fp_symbol), FPPlusZero(5, 11))
        self.assertEqual(model.get_value(rm_symbol), RNE())

    def test_oracles_simplification_and_substitution(self):
        x = Symbol("oracle_fp_x", FLOAT16)
        predicate = FPIsNaN(FPAdd(RNE(), x, self.one))

        self.assertEqual(get_logic(predicate), QF_FP)
        self.assertEqual(self.env.ao.get_atoms(predicate), frozenset((predicate,)))
        self.assertIn(FLOAT16, self.env.typeso.get_types(predicate))
        self.assertIn(RMType(), self.env.typeso.get_types(predicate))
        self.assertEqual(predicate.get_free_variables(), frozenset((x,)))
        self.assertEqual(predicate.simplify(), predicate)

        substituted = predicate.substitute({x: self.two})
        self.assertEqual(substituted, FPIsNaN(FPAdd(RNE(), self.two, self.one)))

    def test_oracle_preserves_theories_nested_in_fp(self):
        x = Symbol("nested_fp_x", FLOAT16)
        uf = Symbol("nested_fp_uf", FunctionType(FLOAT16, [FLOAT16]))
        uf_formula = FPIsNaN(FPAdd(RNE(), Function(uf, [x]), x))
        uf_theory = self.env.theoryo.get_theory(uf_formula)
        self.assertTrue(uf_theory.floating_point)
        self.assertTrue(uf_theory.uninterpreted)

        array = Symbol("nested_fp_array", ArrayType(INT, FLOAT16))
        array_formula = FPIsNaN(Select(array, Int(0)))
        array_theory = self.env.theoryo.get_theory(array_formula)
        self.assertTrue(array_theory.floating_point)
        self.assertTrue(array_theory.arrays)
        self.assertTrue(array_theory.integer_arithmetic)

        ieee_theory = self.env.theoryo.get_theory(FPFromIEEEBV(BV(0x3C00, 16), 5, 11))
        real_theory = self.env.theoryo.get_theory(FPToFP(RNE(), Real(1), 5, 11))
        self.assertFalse(ieee_theory.bit_vectors)
        self.assertFalse(real_theory.real_arithmetic)

        computed_ieee_theory = self.env.theoryo.get_theory(
            FPFromIEEEBV(BVAdd(BV(0x3BFF, 16), BV(1, 16)), 5, 11)
        )
        self.assertTrue(computed_ieee_theory.bit_vectors)

        real_symbol = Symbol("nested_fp_real", REAL)
        nonlinear_conversion = FPIsNaN(
            FPToFP(RNE(), Times(real_symbol, real_symbol), 5, 11)
        )
        nonlinear_theory = self.env.theoryo.get_theory(nonlinear_conversion)
        self.assertTrue(nonlinear_theory.real_arithmetic)
        self.assertFalse(nonlinear_theory.linear)

    def _mixed_logic_cases(self):
        """Formulas that combine FP with other theories, and their logic."""
        x = Symbol("mixed_fp_x", FLOAT16)
        bv = Symbol("mixed_fp_bv", BVType(8))
        real = Symbol("mixed_fp_real", REAL)
        array = Symbol("mixed_fp_array", ArrayType(BVType(8), FLOAT16))
        uf = Symbol("mixed_fp_uf", FunctionType(FLOAT16, [FLOAT16]))

        to_ubv = Equals(FPToUBV(RNE(), x, 8), BVAdd(bv, BV(1, 8)))
        to_real = Equals(FPToReal(x), real)
        select = FPIsNaN(Select(array, bv))
        return [
            (to_ubv, QF_BVFP),
            (Equals(FPToSBV(RNE(), x, 8), BV(3, 8)), QF_BVFP),
            (to_real, QF_FPLRA),
            (And(to_ubv, to_real), QF_BVFPLRA),
            (select, QF_ABVFP),
            (And(select, to_real), QF_ABVFPLRA),
            (FPIsNaN(Function(uf, [x])), QF_AUFBVFP),
        ]

    def test_mixed_fp_logics(self):
        for formula, logic in self._mixed_logic_cases():
            with self.subTest(logic=logic.name):
                self.assertEqual(get_logic(formula), logic)

    @skipIfSolverNotAvailable("z3")
    def test_z3_solves_mixed_fp_logics(self):
        # No logic is given, so the solver is picked from the detected logic.
        for formula, logic in self._mixed_logic_cases():
            with self.subTest(logic=logic.name):
                self.assertSat(formula)

    def test_smtlib_mixed_fp_logic(self):
        source = """
        (set-logic QF_BVFP)
        (declare-fun x () Float32)
        (declare-fun y () (_ BitVec 8))
        (assert (= ((_ fp.to_ubv 8) RNE x) (bvadd y #x01)))
        (check-sat)
        """
        script = SmtLibParser().get_script(StringIO(source))
        self.assertEqual(get_logic(script.get_last_formula()), QF_BVFP)

        stream = StringIO()
        script.serialize(stream)
        self.assertIn("(set-logic QF_BVFP)", stream.getvalue())

    def test_smtlib_tree_and_dag_round_trip(self):
        formula = self._all_operators_formula()

        for daggify in (False, True):
            with self.subTest(daggify=daggify):
                stream = StringIO()
                script = smtlibscript_from_formula(formula, logic=QF_FP)
                script.serialize(stream, daggify=daggify)
                serialized = stream.getvalue()

                parsed = SmtLibParser().get_script(StringIO(serialized))
                parsed_formula = parsed.get_last_formula()
                self.assertEqual(parsed_formula, formula)
                self.assertIn("(set-logic QF_FP)", serialized)
                self.assertIn("(_ FloatingPoint 5 11)", serialized)

    def test_smtlib_standard_aliases_and_special_values(self):
        source = """
        (set-logic QF_FP)
        (declare-fun x () Float16)
        (assert
          (and
            (fp.eq
              (fp.add roundNearestTiesToEven x (_ +zero 5 11))
              (fp.add RNE x (fp #b0 #b00000 #b0000000000)))
            (fp.isZero (_ -zero 5 11))
            (fp.isInfinite (_ +oo 5 11))
            (fp.isInfinite (_ -oo 5 11))
            (fp.isNaN (_ NaN 5 11))))
        (check-sat)
        """
        script = SmtLibParser().get_script(StringIO(source))
        formula = script.get_last_formula()

        self.assertEqual(formula.get_type(), BOOL)
        x = next(iter(formula.get_free_variables()))
        self.assertEqual(x.symbol_type(), FLOAT16)

        stream = StringIO()
        script.serialize(stream)
        reparsed = SmtLibParser().get_script(StringIO(stream.getvalue()))
        self.assertEqual(reparsed.get_last_formula(), formula)

    def test_smtlib_chainable_fp_relations(self):
        source = """
        (set-logic QF_FP)
        (declare-fun x () Float16)
        (declare-fun y () Float16)
        (declare-fun z () Float16)
        (assert
          (and
            (fp.lt x y z)
            (fp.leq x y z)
            (fp.gt x y z)
            (fp.geq x y z)
            (fp.eq x y z)))
        (check-sat)
        """
        formula = SmtLibParser().get_script(StringIO(source)).get_last_formula()
        x = Symbol("x", FLOAT16)
        y = Symbol("y", FLOAT16)
        z = Symbol("z", FLOAT16)
        expected = And(
            And(FPLt(x, y), FPLt(y, z)),
            And(FPLEq(x, y), FPLEq(y, z)),
            And(FPGt(x, y), FPGt(y, z)),
            And(FPGEq(x, y), FPGEq(y, z)),
            And(FPEq(x, y), FPEq(y, z)),
        )
        self.assertEqual(formula, expected)

    def test_hr_printer_honors_threshold_for_fp(self):
        formula = FPNeg(FPNeg(FPNeg(self.one)))
        full = formula.serialize()

        self.assertEqual(formula.serialize(threshold=1), "fp.neg(...)")
        self.assertEqual(formula.serialize(threshold=2), "fp.neg(fp.neg(...))")
        self.assertNotEqual(formula.serialize(threshold=1), full)

    def test_smt_equality_identifies_nan_encodings(self):
        # The theory has a single NaN: every encoding builds the same node
        first_nan = FP(BV(0, 1), BV(31, 5), BV(1, 10))
        second_nan = FP(BV(1, 1), BV(31, 5), BV(2, 10))

        self.assertIs(first_nan, second_nan)
        self.assertIs(first_nan, FPNaN(5, 11))
        self.assertEqual(first_nan.constant_value(), (0, 31, 1))
        self.assertTrue(Equals(first_nan, second_nan).simplify().is_true())
        self.assertTrue(FPEq(first_nan, second_nan).simplify().is_false())

    def test_smtlib_literal_spelling(self):
        self.assertEqual(
            self.one.to_smtlib(daggify=False), "(fp #b0 #b01111 #b0000000000)"
        )
        self.assertEqual(RNE().to_smtlib(daggify=False), "RNE")

    @skipIfSolverNotAvailable("z3")
    def test_z3_converts_every_fp_operator(self):
        self.assertValid(self._all_operators_formula(), solver_name="z3", logic=QF_FP)

    @skipIfSolverNotAvailable("z3")
    def test_z3_rounding_modes_are_distinct(self):
        modes = (RNE(), RNA(), RTP(), RTN(), RTZ())
        pairwise_distinct = And(
            Not(Equals(left, right)) for left, right in combinations(modes, 2)
        )
        self.assertValid(pairwise_distinct, solver_name="z3", logic=QF_FP)

    @skipIfSolverNotAvailable("z3")
    def test_z3_special_value_semantics(self):
        plus_zero = FPPlusZero(5, 11)
        minus_zero = FPMinusZero(5, 11)
        plus_inf = FPPlusInfinity(5, 11)
        minus_inf = FPMinusInfinity(5, 11)
        nan = FPNaN(5, 11)

        expected = And(
            FPIsZero(plus_zero),
            FPIsZero(minus_zero),
            FPEq(plus_zero, minus_zero),
            Not(Equals(plus_zero, minus_zero)),
            FPIsInfinite(plus_inf),
            FPIsInfinite(minus_inf),
            FPIsPositive(plus_zero),
            FPIsNegative(minus_zero),
            FPIsNaN(nan),
            Not(FPEq(nan, nan)),
        )
        self.assertValid(expected, solver_name="z3", logic=QF_FP)

    @skipIfSolverNotAvailable("z3")
    def test_z3_exact_binary16_arithmetic(self):
        expected = And(
            Equals(FPAbs(self.minus_one), self.one),
            Equals(FPNeg(self.minus_one), self.one),
            Equals(FPAdd(RNE(), self.one, self.one), self.two),
            Equals(FPSub(RNE(), self.two, self.one), self.one),
            Equals(FPMul(RNE(), self.one, self.two), self.two),
            Equals(FPDiv(RNE(), self.two, self.two), self.one),
            Equals(FPFMA(RNE(), self.one, self.one, self.one), self.two),
            Equals(FPSqrt(RNE(), self.one), self.one),
            Equals(FPRoundToIntegral(RNE(), self.one), self.one),
            Equals(FPMin(self.one, self.two), self.one),
            Equals(FPMax(self.one, self.two), self.two),
            FPLt(self.one, self.two),
            FPLEq(self.one, self.two),
        )
        self.assertValid(expected, solver_name="z3", logic=QF_FP)

    @skipIfSolverNotAvailable("z3")
    def test_z3_conversions(self):
        float32_one = FP(BV(0, 1), BV(127, 8), BV(0, 23))
        expected = And(
            Equals(FPFromIEEEBV(BV(0x3C00, 16), 5, 11), self.one),
            Equals(FPToFP(RNE(), self.one, 8, 24), float32_one),
            Equals(FPToFP(RNE(), Real(1), 5, 11), self.one),
            Equals(FPToFP(RNE(), BV(1, 8), 5, 11), self.one),
            Equals(FPToFPUnsigned(RNE(), BV(1, 8), 5, 11), self.one),
            Equals(FPToUBV(RTZ(), self.one, 8), BV(1, 8)),
            Equals(FPToSBV(RTZ(), self.one, 8), BV(1, 8)),
            Equals(FPToReal(self.one), Real(1)),
        )
        self.assertValid(expected, solver_name="z3", logic=QF_FP)

    @skipIfSolverNotAvailable("z3")
    def test_z3_model_back_conversion(self):
        x = Symbol("model_fp_x", FLOAT16)
        with Solver(name="z3", logic=QF_FP) as solver:
            solver.add_assertion(Equals(x, self.one))
            self.assertTrue(solver.solve())
            value = solver.get_model()[x]

        self.assertEqual(value.get_type(), FLOAT16)
        self.assertTrue(value.is_constant())
        self.assertValid(Equals(value, self.one), solver_name="z3", logic=QF_FP)

    # Regressions

    def _parse(self, source):
        return SmtLibParser().get_script(StringIO(source)).get_last_formula()

    def test_logic_of_formulas_without_fp(self):
        # An FP logic is never chosen for a formula without FP, although
        # e.g. QF_ABVFPLRA would win the tie with QF_AUFBVLIRA by name
        a = Symbol("a", ArrayType(BVType(8), REAL))
        formula = LT(Select(a, Symbol("i", BVType(8))), Real(1))
        self.assertEqual(get_logic(formula), QF_AUFBVLIRA)
        stream = StringIO()
        smtlibscript_from_formula(formula).serialize(stream)
        self.assertNotIn("FP", stream.getvalue())

    def test_bv_operators_over_fp_conversions(self):
        x = Symbol("x", FLOAT16)
        ubv = FPToUBV(RNE(), x, 8)
        self.assertEqual(ubv.bv_width(), 8)
        self.assertEqual(BVAdd(ubv, BV(1, 8)).get_type(), BVType(8))
        self.assertEqual(BVExtract(FPToSBV(RNE(), x, 8), 0, 3).get_type(), BVType(4))
        self.assertEqual(Ite(Symbol("c"), ubv, BV(0, 8)).bv_width(), 8)
        formula = self._parse(
            """
            (declare-fun x () Float16)
            (assert (= (bvadd ((_ fp.to_ubv 8) RNE x) #x01)
                       ((_ extract 7 0) ((_ fp.to_sbv 8) RNE x))))
            """
        )
        self.assertEqual(get_logic(formula), QF_BVFP)

    def test_nan_encodings_are_one_value(self):
        x = Symbol("x", FLOAT16)
        nan1 = FP(BV(0, 1), BV(31, 5), BV(1, 10))
        nan2 = FP(BV(1, 1), BV(31, 5), BV(512, 10))
        # Satisfiable: both encodings denote the single NaN
        self.assertFalse(
            propagate_toplevel(And(Equals(x, nan1), Equals(x, nan2))).is_false()
        )
        self.assertTrue(
            SmtLibModelValidationSimplifier().simplify(Equals(nan1, nan2)).is_true()
        )
        array = Array(FLOAT16, Int(0), {nan1: Int(7)})
        self.assertEqual(Select(array, nan2).simplify(), Int(7))

    def test_propagate_toplevel_with_fp_constants(self):
        one = FPVal(1, 5, 11)
        two = FPVal(2, 5, 11)
        self.assertTrue(propagate_toplevel(Equals(one, two)).is_false())
        self.assertTrue(propagate_toplevel(Equals(RNE(), RTZ())).is_false())
        self.assertTrue(propagate_toplevel(Equals(String("a"), String("b"))).is_false())

    def test_logic_of_operations_over_fp_conversions(self):
        x, y, z = (Symbol(n, FLOAT16) for n in "xyz")
        bvult = BVULT(FPToUBV(RNE(), x, 8), FPToUBV(RNE(), y, 8))
        self.assertEqual(get_logic(bvult), QF_BVFP)
        lt = LT(Plus(FPToReal(x), FPToReal(y)), FPToReal(z))
        self.assertEqual(get_logic(lt), QF_FPLRA)

    def test_logic_of_fp_operands(self):
        x = Symbol("x", FLOAT16)
        # Literal operands are part of the FP signature
        self.assertEqual(get_logic(FPEq(x, FPToFP(RNE(), Real(0.5), 5, 11))), QF_FP)
        self.assertEqual(get_logic(FPEq(x, FPFromIEEEBV(BV(0x3C00, 16), 5, 11))), QF_FP)
        components = FP(Ite(Symbol("c"), BV(0, 1), BV(1, 1)), BV(15, 5), BV(0, 10))
        self.assertEqual(get_logic(FPEq(x, components)), QF_FP)
        # Variables of BV or Real sort are not
        r = Symbol("r", REAL)
        bv = Symbol("bv", BVType(16))
        self.assertEqual(get_logic(FPIsNaN(FPToFP(RNE(), r, 5, 11))), QF_FPLRA)
        self.assertEqual(get_logic(FPIsNaN(FPFromIEEEBV(bv, 5, 11))), QF_BVFP)
        self.assertEqual(
            get_logic(FPIsNaN(FPToFPUnsigned(RNE(), BVExtract(bv, 0, 7), 5, 11))),
            QF_BVFP,
        )

    def test_smtlib_declarations_shadow_interpreted_symbols(self):
        formula = self._parse(
            "(set-logic QF_UFLIA)(declare-fun fp (Int) Int)(assert (= (fp 1) 2))"
        )
        fp = Symbol("fp", FunctionType(INT, [INT]))
        self.assertEqual(formula, Equals(Function(fp, [Int(1)]), Int(2)))

        formula = self._parse(
            "(set-logic QF_UFLIA)(declare-fun bvadd (Int) Int)(assert (= (bvadd 1) 2))"
        )
        bvadd = Symbol("bvadd", FunctionType(INT, [INT]))
        self.assertEqual(formula, Equals(Function(bvadd, [Int(1)]), Int(2)))

        formula = self._parse(
            "(set-logic QF_LIA)(define-fun fp ((a Int)) Int (+ a 1))"
            "(assert (= (fp 1) 2))"
        )
        self.assertEqual(formula, Equals(Plus(Int(1), Int(1)), Int(2)))

    def test_smtlib_fp_syntax_errors(self):
        for source in [
            "(declare-fun x () (_ FloatingPoint 1 5))",
            "(declare-fun x () (_ FloatingPoint 8 x))",
            "(assert (fp.isZero (_ +zero 8 1)))",
            "(declare-fun b () (_ BitVec 8))"
            "(assert (fp.isNaN ((_ to_fp_unsigned 5 11) b)))",
            "(declare-fun x () Float16)(assert (= ((_ fp.to_ubv 0) RNE x) #b0))",
            "(declare-fun x () Float16)(assert (= ((_ fp.to_sbv 4) x) #x0))",
        ]:
            with self.subTest(source=source):
                with self.assertRaises(PysmtSyntaxError):
                    self._parse(source)

    def test_smtlib_special_values(self):
        x = Symbol("x", FLOAT16)
        formula = And(
            FPEq(x, FPPlusInfinity(5, 11)),
            FPEq(x, FPMinusInfinity(5, 11)),
            Equals(x, FPNaN(5, 11)),
            FPEq(x, FPMinusZero(5, 11)),
        )
        for daggify in (False, True):
            with self.subTest(daggify=daggify):
                printed = to_smtlib(formula, daggify=daggify)
                for value in ("(_ +oo 5 11)", "(_ -oo 5 11)", "(_ NaN 5 11)"):
                    self.assertIn(value, printed)
                self.assertIn("(fp #b1 #b00000 #b0000000000)", printed)
                source = "(declare-fun x () Float16)(assert %s)" % printed
                self.assertEqual(self._parse(source), formula)

    def test_fp_val(self):
        # The Float32 value nearest to 0.1 is 0x3DCCCCCD
        self.assertEqual(
            FPVal(0.1, 8, 24), FPFromIEEEBV(BV(0x3DCCCCCD, 32), 8, 24).simplify()
        )
        self.assertEqual(FPVal("0.1", 8, 24), FPVal(0.1, 8, 24))
        self.assertEqual(FPVal(1, 5, 11), self.one)
        self.assertEqual(FPVal(-1.0, 5, 11), self.minus_one)
        self.assertEqual(FPVal(float("nan"), 5, 11), FPNaN(5, 11))
        self.assertEqual(FPVal(float("-inf"), 5, 11), FPMinusInfinity(5, 11))
        self.assertEqual(FPVal(-0.0, 5, 11), FPMinusZero(5, 11))
        self.assertEqual(FPVal(0, 5, 11), FPPlusZero(5, 11))
        # 1/3 rounded down and up
        third_down = FPVal("1/3", 5, 11, RTZ())
        third_up = FPVal("1/3", 5, 11, RTP())
        self.assertEqual(
            FPAdd(RNE(), third_down, FPVal(2**-12, 5, 11)).simplify(), third_up
        )
        self.assertEqual(FPVal(70000, 5, 11), FPPlusInfinity(5, 11))
        self.assertEqual(FPVal(70000, 5, 11, RTZ()), FPVal(65504, 5, 11))
        with self.assertRaises(PysmtValueError):
            FPVal(1, 5, 11, Symbol("rm", RMType()))

    def test_evaluation_of_constant_operations(self):
        one, two = FPVal(1, 5, 11), FPVal(2, 5, 11)
        zero, minus_zero = FPPlusZero(5, 11), FPMinusZero(5, 11)
        self.assertEqual(FPAdd(RNE(), one, one).simplify(), two)
        self.assertEqual(FPSqrt(RNE(), FPVal(4, 5, 11)).simplify(), two)
        self.assertEqual(
            FPMul(RNE(), FPVal(65504, 5, 11), two).simplify(), FPPlusInfinity(5, 11)
        )
        # An exact zero sum is +0, or -0 when rounding toward negative
        self.assertEqual(FPSub(RNE(), one, one).simplify(), zero)
        self.assertEqual(FPSub(RTN(), one, one).simplify(), minus_zero)
        self.assertTrue(FPIsNaN(FPDiv(RNE(), zero, zero)).simplify().is_true())
        self.assertTrue(FPEq(zero, minus_zero).simplify().is_true())
        self.assertTrue(Equals(zero, minus_zero).simplify().is_false())
        self.assertEqual(FPToReal(FPVal(0.5, 5, 11)).simplify(), Real(0.5))
        self.assertEqual(FPToSBV(RTZ(), FPVal(-2.5, 5, 11), 8).simplify(), BV(254, 8))
        self.assertEqual(FPToFP(RNE(), BV(255, 8), 5, 11).simplify(), self.minus_one)
        # Unspecified results are kept
        for term in [
            FPToReal(FPPlusInfinity(5, 11)),
            FPToUBV(RNE(), FPVal(-1, 5, 11), 8),
            FPToSBV(RNE(), FPNaN(5, 11), 8),
            FPMin(zero, minus_zero),
        ]:
            with self.subTest(term=term):
                self.assertEqual(term.simplify(), term)

    def test_eager_model_evaluates_fp(self):
        x = Symbol("x", FLOAT16)
        model = EagerModel({x: FPNaN(5, 11)})
        self.assertTrue(model.get_value(FPIsNaN(x)).is_true())
        self.assertTrue(model.satisfies(Not(FPEq(x, x))))

    def test_smtlib_model_validation(self):
        parser = SmtLibParser()
        formula = parser.get_script(
            StringIO(
                "(declare-fun x () Float16)(declare-fun y () Float16)"
                "(assert (and (fp.lt x y) (= (fp.add RNE x x) y) (not (= x (_ NaN 5 11)))))"
            )
        ).get_last_formula()

        def validate(model_source):
            model, interpretations = parser.parse_model(StringIO(model_source))
            return SmtLibModelValidationSimplifier().simplify(
                formula.substitute(model, interpretations)
            )

        # x = 1.0, y = 2.0
        good = validate(
            "(model (define-fun x () Float16 (fp #b0 #b01111 #b0000000000))"
            " (define-fun y () Float16 (fp #b0 #b10000 #b0000000000)))"
        )
        self.assertTrue(good.is_true())
        # x is a NaN, with an encoding other than the one of (_ NaN 5 11)
        bad = validate(
            "(model (define-fun x () Float16 (fp #b1 #b11111 #b0000000011))"
            " (define-fun y () Float16 (fp #b0 #b10000 #b0000000000)))"
        )
        self.assertTrue(bad.is_false())

    @skipIfSolverNotAvailable("z3")
    def test_z3_models_satisfy_fp_formulas(self):
        x, y = Symbol("x", FLOAT16), Symbol("y", FLOAT16)
        r = Symbol("r", REAL)
        formulas = [
            And(FPLt(x, y), FPEq(FPAdd(RNE(), x, self.one), y)),
            FPIsNaN(FPMul(RTZ(), x, y)),
            And(FPIsSubnormal(x), FPIsNegative(FPFMA(RTP(), x, y, x))),
            # Unspecified values, which the model decides
            And(FPIsInfinite(x), Equals(FPToReal(x), r)),
            And(
                Equals(x, FPPlusZero(5, 11)),
                Equals(y, FPMinusZero(5, 11)),
                Equals(FPMin(x, y), FPMinusZero(5, 11)),
            ),
        ]
        for formula in formulas:
            with self.subTest(formula=formula):
                with Solver(name="z3", logic=QF_FPLRA) as solver:
                    solver.add_assertion(formula)
                    self.assertTrue(solver.solve())
                    model = solver.get_model()
                    self.assertTrue(model.satisfies(formula, solver))

    @skipIfSolverNotAvailable("z3")
    def test_z3_converts_selects_over_custom_sorts(self):
        sort = Type("S")
        select = Select(Symbol("a", ArrayType(INT, sort)), Int(0))
        with Solver(name="z3") as solver:
            self.assertEqual(str(solver.converter.convert(select)), "a[0]")

    @skipIfSolverNotAvailable("cvc5")
    def test_cvc5_models_with_fp_symbols_in_the_environment(self):
        Symbol("x", FLOAT16)
        p = Symbol("p", INT)
        with Solver(name="cvc5") as solver:
            solver.add_assertion(Equals(p, Int(3)))
            self.assertTrue(solver.solve())
            self.assertEqual(solver.get_model().get_value(p), Int(3))


if __name__ == "__main__":
    main()
