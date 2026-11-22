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
from pysmt.exceptions import PysmtTypeError, PysmtValueError
from pysmt.logics import (
    QF_ABVFP,
    QF_ABVFPLRA,
    QF_AUFBVFP,
    QF_BVFP,
    QF_BVFPLRA,
    QF_FP,
    QF_FPLRA,
)
from pysmt.oracles import get_logic
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
    BVAdd,
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
    Function,
    Iff,
    Int,
    Not,
    Real,
    Select,
    Solver,
    Symbol,
    Times,
)
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import smtlibscript_from_formula
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
        first_nan = FP(BV(0, 1), BV(31, 5), BV(1, 10))
        second_nan = FP(BV(1, 1), BV(31, 5), BV(2, 10))

        self.assertNotEqual(first_nan.constant_value(), second_nan.constant_value())
        self.assertTrue(Equals(first_nan, second_nan).simplify().is_true())

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


if __name__ == "__main__":
    main()
