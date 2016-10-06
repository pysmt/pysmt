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
from collections import namedtuple

import pysmt.logics
from pysmt.environment import get_env
from pysmt.shortcuts import (Symbol, Function,
                             Int, Real, FALSE, TRUE,
                             And, Iff, Or, Not, Implies, Ite,
                             LT, LE, GT, GE,
                             Times, Pow, Equals, Plus, Minus, Div, ToReal,
                             ForAll, Exists,
                             BV, SBV, BVOne, BVZero,
                             BVNot, BVAnd, BVOr, BVXor,
                             BVConcat, BVExtract,
                             BVULT, BVUGT, BVULE, BVUGE, BVSGE,
                             BVNeg, BVAdd, BVMul, BVUDiv, BVURem, BVSub,
                             BVLShl, BVLShr,BVRol, BVRor,
                             BVZExt, BVSExt, BVSub, BVComp, BVAShr, BVSLE,
                             BVSLT, BVSGT, BVSGE, BVSDiv, BVSRem,
                             Store, Select, Array)
from pysmt.constants import Fraction

from pysmt.typing import REAL, BOOL, INT, BV8, BV16, ARRAY_INT_INT
from pysmt.typing import FunctionType, ArrayType


Example = namedtuple('Example',
                     ['hr', 'expr', 'is_valid', 'is_sat', 'logic'])

SExample = namedtuple('SimpleExample',
                      ['expr', 'is_valid', 'is_sat', 'logic'])


def get_full_example_formulae(environment=None):
    """Return a list of Examples using the given environment."""

    if environment is None:
        environment = get_env()

    with environment:
        x = Symbol("x", BOOL)
        y = Symbol("y", BOOL)
        p = Symbol("p", INT)
        q = Symbol("q", INT)
        r = Symbol("r", REAL)
        s = Symbol("s", REAL)
        aii = Symbol("aii", ARRAY_INT_INT)
        ari = Symbol("ari", ArrayType(REAL, INT))
        arb = Symbol("arb", ArrayType(REAL, BV8))
        abb = Symbol("abb", ArrayType(BV8, BV8))
        nested_a = Symbol("a_arb_aii", ArrayType(ArrayType(REAL, BV8),
                                                 ARRAY_INT_INT))

        rf = Symbol("rf", FunctionType(REAL, [REAL, REAL]))
        rg = Symbol("rg", FunctionType(REAL, [REAL]))

        ih = Symbol("ih", FunctionType(INT, [REAL, INT]))
        ig = Symbol("ig", FunctionType(INT, [INT]))

        bf = Symbol("bf", FunctionType(BOOL, [BOOL]))
        bg = Symbol("bg", FunctionType(BOOL, [BOOL]))

        bv8 = Symbol("bv1", BV8)
        bv16 = Symbol("bv2", BV16)

        result = [
            # Formula, is_valid, is_sat, is_qf
            Example(hr="(x & y)",
                    expr=And(x, y),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL
                ),

            Example(hr="(x <-> y)",
                    expr=Iff(x, y),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL
                ),

            Example(hr="((x | y) & (! (x | y)))",
                    expr=And(Or(x, y), Not(Or(x, y))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BOOL
                ),

            Example(hr="(x & (! y))",
                    expr=And(x, Not(y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL
                ),

            Example(hr="(False -> True)",
                    expr=Implies(FALSE(),TRUE()),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL
                ),

            #
            #  LIA
            #
            Example(hr="((q < p) & (x -> y))",
                    expr=And(GT(p, q), Implies(x, y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_IDL
                ),

            Example(hr="(((p + q) = 5) & (q < p))",
                    expr=And(Equals(Plus(p,q),Int(5)) , GT(p, q)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),

            Example(hr="((q <= p) | (p <= q))",
                    expr=Or(GE(p, q), LE(p, q)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_IDL
                ),

            Example(hr="(! (p < (q * 2)))",
                    expr=Not(LT(p, Times(q, Int(2)))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),

            Example(hr="(p < (p - (5 - 2)))",
                    expr=GT(Minus(p, Minus(Int(5), Int(2))), p),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_IDL
                ),

            Example(hr="((x ? 7 : ((p + -1) * 3)) = q)",
                    expr=Equals(Ite(x,
                                    Int(7),
                                    Times(Plus(p, Int(-1)), Int(3))), q),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),

            Example(hr="(p < (q + 1))",
                    expr=LT(p, Plus(q, Int(1))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),

            #
            # LRA
            #
            Example(hr="((s < r) & (x -> y))",
                    expr=And(GT(r, s), Implies(x, y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_RDL
                ),

            Example(hr="(((r + s) = 28/5) & (s < r))",
                    expr=And(Equals(Plus(r,s), Real(Fraction("5.6"))) , GT(r, s)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LRA
                ),

            Example(hr="((s <= r) | (r <= s))",
                    expr=Or(GE(r, s), LE(r, s)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_RDL
                ),

            Example(hr="(! ((r * 2.0) < (s * 2.0)))",
                    expr=Not(LT(Div(r, Real((1,2))), Times(s, Real(2)))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LRA
                ),

            Example(hr="(! (r < (r - (5.0 - 2.0))))",
                    expr=Not(GT(Minus(r, Minus(Real(5), Real(2))), r)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_RDL
                ),

            Example(hr="((x ? 7.0 : ((s + -1.0) * 3.0)) = r)",
                    expr=Equals( Ite(x, Real(7), Times(Plus(s, Real(-1)), Real(3))), r),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LRA
                ),

            #
            # EUF
            #
            Example(hr="(bf(x) <-> bg(x))",
                    expr=Iff(Function(bf, (x,)), Function(bg, (x,))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_UF
                ),

            Example(hr="(rf(5.0, rg(r)) = 0.0)",
                    expr=Equals(Function(rf, (Real(5), Function(rg, (r,)))), Real(0)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLRA
                ),

            Example(hr="((rg(r) = (5.0 + 2.0)) <-> (rg(r) = 7.0))",
                    expr=Iff(Equals(Function(rg, [r]), Plus(Real(5), Real(2))),
                             Equals(Function(rg, [r]), Real(7))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLRA
                ),

            Example(hr="((r = (s + 1.0)) & (rg(s) = 5.0) & (rg((r - 1.0)) = 7.0))",
                    expr=And([Equals(r, Plus(s, Real(1))),
                              Equals(Function(rg, [s]), Real(5)),
                              Equals(
                                  Function(rg, [Minus(r, Real(1))]), Real(7))]),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_UFLRA
                ),

            #
            # BV
            #
            Example(hr="((1_32 & 0_32) = 0_32)",
                    expr=Equals(BVAnd(BVOne(32), BVZero(32)),
                                BVZero(32)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((! 2_3) = 5_3)",
                    expr=Equals(BVNot(BV("010")),
                                BV("101")),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((7_3 xor 0_3) = 0_3)",
                    expr=Equals(BVXor(BV("111"), BV("000")),
                                BV("000")),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv1::bv1) u< 0_16)",
                    expr=BVULT(BVConcat(bv8, bv8),
                               BVZero(16)),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="(1_32[0:7] = 1_8)",
                    expr=Equals(BVExtract(BVOne(32), end=7),
                                BVOne(8)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="(0_8 u< (((bv1 + 1_8) * 5_8) u/ 5_8))",
                    expr=BVUGT(BVUDiv(BVMul(BVAdd(bv8, BVOne(8)), BV(5, width=8)),
                                      BV(5, width=8)),
                               BVZero(8)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="(0_16 u<= bv2)",
                    expr=BVUGE(bv16, BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="(0_16 s<= bv2)",
                    expr=BVSGE(bv16, BVZero(16)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((0_32 u< (5_32 u% 2_32)) & ((5_32 u% 2_32) u<= 1_32))",
                    expr=And(BVUGT(BVURem(BV(5, width=32), BV(2, width=32)), BVZero(32)),
                             BVULE(BVURem(BV(5, width=32), BV(2, width=32)), BVOne(32))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((((1_32 + (- 1_32)) << 1_32) >> 1_32) = 1_32)",
                    expr=Equals(BVLShr(BVLShl(BVAdd(BVOne(32),
                                                    BVNeg(BVOne(32))),
                                              1), 1),
                                BVOne(32)),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((1_32 - 1_32) = 0_32)",
                    expr=Equals(BVSub(BVOne(32), BVOne(32)), BVZero(32)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            # Rotations
            Example(hr="(((1_32 ROL 1) ROR 1) = 1_32)",
                    expr=Equals(BVRor(BVRol(BVOne(32), 1),1), BVOne(32)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            # Extensions
            Example(hr="((0_5 ZEXT 11) = (0_1 SEXT 15))",
                    expr=Equals(BVZExt(BVZero(5), 11),
                                BVSExt(BVZero(1), 15)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2 - bv2) = 0_16)",
                    expr=Equals(BVSub(bv16, bv16), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2 - bv2)[0:7] = bv1)",
                    expr=Equals(BVExtract(BVSub(bv16, bv16), 0, 7), bv8),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2[0:7] bvcomp bv1) = 1_1)",
                    expr=Equals(BVComp(BVExtract(bv16, 0, 7), bv8), BVOne(1)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2 bvcomp bv2) = 0_1)",
                    expr=Equals(BVComp(bv16, bv16), BVZero(1)),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="(bv2 s< bv2)",
                    expr=BVSLT(bv16, bv16),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="(bv2 s< 0_16)",
                    expr=BVSLT(bv16, BVZero(16)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2 s< 0_16) | (0_16 s<= bv2))",
                    expr=Or(BVSGT(BVZero(16), bv16), BVSGE(bv16, BVZero(16))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="(bv2 u< bv2)",
                    expr=BVULT(bv16, bv16),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="(bv2 u< 0_16)",
                    expr=BVULT(bv16, BVZero(16)),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2 | 0_16) = bv2)",
                    expr=Equals(BVOr(bv16, BVZero(16)), bv16),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2 & 0_16) = 0_16)",
                    expr=Equals(BVAnd(bv16, BVZero(16)), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((0_16 s< bv2) & ((bv2 s/ 65535_16) s< 0_16))",
                    expr=And(BVSLT(BVZero(16), bv16),
                             BVSLT(BVSDiv(bv16, SBV(-1, 16)), BVZero(16))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((0_16 s< bv2) & ((bv2 s% 1_16) s< 0_16))",
                    expr=And(BVSLT(BVZero(16), bv16),
                             BVSLT(BVSRem(bv16, BVOne(16)), BVZero(16))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV
                ),
            Example(hr="((bv2 u% 1_16) = 0_16)",
                    expr=Equals(BVURem(bv16, BVOne(16)), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2 s% 1_16) = 0_16)",
                    expr=Equals(BVSRem(bv16, BVOne(16)), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2 s% (- 1_16)) = 0_16)",
                    expr=Equals(BVSRem(bv16, BVNeg(BVOne(16))), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((bv2 a>> 0_16) = bv2)",
                    expr=Equals(BVAShr(bv16, BVZero(16)), bv16),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),

            Example(hr="((0_16 s<= bv2) & ((bv2 a>> 1_16) = (bv2 >> 1_16)))",
                    expr=And(BVSLE(BVZero(16), bv16),
                             Equals(BVAShr(bv16, BVOne(16)),
                                    BVLShr(bv16, BVOne(16)))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV
                ),
            #
            # Quantification
            #
            Example(hr="(forall y . (x -> y))",
                    expr=ForAll([y], Implies(x,y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.BOOL
                ),

            Example(hr="(forall p, q . ((p + q) = 0))",
                    expr=ForAll([p,q], Equals(Plus(p,q), Int(0))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.LIA
                ),

            Example(hr="(forall r, s . (((0.0 < r) & (0.0 < s)) -> ((r - s) < r)))",
                    expr=ForAll([r,s],
                                Implies(And(GT(r, Real(0)), GT(s, Real(0))),
                                        (LT(Minus(r,s), r)))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.LRA
                ),

            Example(hr="(exists x, y . (x -> y))",
                    expr=Exists([x,y], Implies(x,y)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.BOOL
                ),

            Example(hr="(exists p, q . ((p + q) = 0))",
                    expr=Exists([p,q], Equals(Plus(p,q), Int(0))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.LIA
                ),

            Example(hr="(exists r . (forall s . (r < (r - s))))",
                    expr=Exists([r], ForAll([s], GT(Minus(r,s), r))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.LRA
                ),

            Example(hr="(forall r . (exists s . (r < (r - s))))",
                    expr=ForAll([r], Exists([s], GT(Minus(r,s), r))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.LRA
                ),

            Example(hr="(x & (forall r . ((r + s) = 5.0)))",
                    expr=And(x, ForAll([r], Equals(Plus(r,s), Real(5)))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.LRA
                ),

            Example(hr="(exists x . ((x <-> (5.0 < s)) & (s < 3.0)))",
                    expr=Exists([x], (And(Iff(x, GT(s, Real(5))),
                                          LT(s, Real(3))))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.LRA
                ),

            #
            # UFLIRA
            #
            Example(hr="((p < ih(r, q)) & (x -> y))",
                    expr=And(GT(Function(ih, (r, q)), p), Implies(x, y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLIRA
                ),

            Example(hr="(((p - 3) = q) -> ((p < ih(r, (q + 3))) | (ih(r, p) <= p)))",
                    expr=Implies(Equals(Minus(p, Int(3)), q),
                                 Or(GT(Function(ih, (r, Plus(q, Int(3)))), p),
                                    LE(Function(ih, (r, p)), p))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLIRA
                ),

            Example(hr="(((ToReal((p - 3)) = r) & (ToReal(q) = r)) -> ((p < ih(ToReal((p - 3)), (q + 3))) | (ih(r, p) <= p)))",
                    expr=Implies(And(Equals(ToReal(Minus(p, Int(3))), r),
                                     Equals(ToReal(q), r)),
                                 Or(GT(Function(ih, (ToReal(Minus(p, Int(3))),
                                                     Plus(q, Int(3)))), p),
                                    LE(Function(ih, (r, p)), p))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLIRA
                ),

            Example(hr="(! (((ToReal((p - 3)) = r) & (ToReal(q) = r)) -> ((p < ih(ToReal((p - 3)), (q + 3))) | (ih(r, p) <= p))))",
                    expr=Not(Implies(And(Equals(ToReal(Minus(p, Int(3))), r),
                                         Equals(ToReal(q), r)),
                                     Or(GT(Function(ih, (ToReal(Minus(p, Int(3))),
                                                         Plus(q, Int(3)))), p),
                                        LE(Function(ih, (r, p)), p)))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_UFLIRA
                ),

            Example(hr="""("Did you know that any string works? #yolo" & "10" & "|#somesolverskeepthe||" & " ")""",
                    expr=And(Symbol("Did you know that any string works? #yolo"),
                             Symbol("10"),
                             Symbol("|#somesolverskeepthe||"),
                             Symbol(" ")),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL
                ),

            #
            # Arrays
            #
            Example(hr="((q = 0) -> (aii[0 := 0] = aii[0 := q]))",
                    expr=Implies(Equals(q, Int(0)),
                                 Equals(Store(aii, Int(0), Int(0)),
                                        Store(aii, Int(0), q))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_ALIA
                ),

            Example(hr="(aii[0 := 0][0] = 0)",
                    expr=Equals(Select(Store(aii, Int(0), Int(0)), Int(0)),
                                Int(0)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_ALIA
                ),

            Example(hr="((Array{Int, Int}(0)[1 := 1] = aii) & (aii[1] = 0))",
                    expr=And(Equals(Array(INT, Int(0), {Int(1) : Int(1)}), aii), Equals(Select(aii, Int(1)), Int(0))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.get_logic_by_name("QF_ALIA*")
                ),

            Example(hr="((Array{Int, Int}(0)[1 := 3] = aii) & (aii[1] = 3))",
                    expr=And(Equals(Array(INT, Int(0), {Int(1) : Int(3)}), aii), Equals(Select(aii, Int(1)), Int(3))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.get_logic_by_name("QF_ALIA*")
                ),

            Example(hr="((Array{Real, Int}(10) = ari) & (ari[6/5] = 0))",
                    expr=And(Equals(Array(REAL, Int(10)), ari), Equals(Select(ari, Real((6, 5))), Int(0))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.get_logic_by_name("QF_AUFBVLIRA*")
                ),

            Example(hr="((Array{Real, Int}(0)[1.0 := 10][2.0 := 20][3.0 := 30][4.0 := 40] = ari) & (! ((ari[0.0] = 0) & (ari[1.0] = 10) & (ari[2.0] = 20) & (ari[3.0] = 30) & (ari[4.0] = 40))))",
                    expr=And(Equals(Array(REAL, Int(0), {Real(1) : Int(10), Real(2) : Int(20), Real(3) : Int(30), Real(4) : Int(40)}), ari),
                             Not(And(Equals(Select(ari, Real(0)), Int(0)),
                                     Equals(Select(ari, Real(1)), Int(10)),
                                     Equals(Select(ari, Real(2)), Int(20)),
                                     Equals(Select(ari, Real(3)), Int(30)),
                                     Equals(Select(ari, Real(4)), Int(40))))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.get_logic_by_name("QF_AUFBVLIRA*")
                ),

            Example(hr="((Array{Real, Int}(0)[1.0 := 10][2.0 := 20][3.0 := 30][4.0 := 40][5.0 := 50] = ari) & (! ((ari[0.0] = 0) & (ari[1.0] = 10) & (ari[2.0] = 20) & (ari[3.0] = 30) & (ari[4.0] = 40) & (ari[5.0] = 50))))",
                    expr=And(Equals(Array(REAL, Int(0), {Real(1) : Int(10), Real(2) : Int(20), Real(3) : Int(30), Real(4) : Int(40), Real(5) : Int(50)}), ari),
                             Not(And(Equals(Select(ari, Real(0)), Int(0)),
                                     Equals(Select(ari, Real(1)), Int(10)),
                                     Equals(Select(ari, Real(2)), Int(20)),
                                     Equals(Select(ari, Real(3)), Int(30)),
                                     Equals(Select(ari, Real(4)), Int(40)),
                                     Equals(Select(ari, Real(5)), Int(50))))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.get_logic_by_name("QF_AUFBVLIRA*")
                ),


            Example(hr="((a_arb_aii = Array{Array{Real, BV{8}}, Array{Int, Int}}(Array{Int, Int}(7))) -> (a_arb_aii[arb][42] = 7))",
                    expr=Implies(Equals(nested_a, Array(ArrayType(REAL, BV8),
                                                        Array(INT, Int(7)))),
                                 Equals(Select(Select(nested_a, arb), Int(42)),
                                        Int(7))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.get_logic_by_name("QF_AUFBVLIRA*")
                ),

            Example(hr="(abb[bv1 := y_][bv1 := z_] = abb[bv1 := z_])",
                    expr=Equals(Store(Store(abb, bv8, Symbol("y_", BV8)),
                                      bv8, Symbol("z_", BV8)),
                                Store(abb, bv8, Symbol("z_", BV8))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_ABV
                ),

            Example(hr="((r / s) = (r * s))",
                    expr=Equals(Div(r, s), Times(r,s)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_NRA
                ),

            Example(hr="(2.0 = (r * r))",
                    expr=Equals(Real(2), Times(r,r)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_NRA
                ),

            Example(hr="((p ^ 2) = 0)",
                    expr=Equals(Pow(p, Int(2)), Int(0)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_NIA
                ),

            Example(hr="((r ^ 2.0) = 0.0)",
                    expr=Equals(Pow(r, Real(2)), Real(0)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_NRA
                ),

            Example(hr="((r * r * r) = 25.0)",
                    expr=Equals(Times(r, r, r), Real(25)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_NRA
                ),

            Example(hr="((5.0 * r * 5.0) = 25.0)",
                    expr=Equals(Times(Real(5), r, Real(5)), Real(25)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LRA
                ),

            Example(hr="((p * p * p) = 25)",
                    expr=Equals(Times(p, p, p), Int(25)),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_NIA
                ),

            Example(hr="((5 * p * 5) = 25)",
                    expr=Equals(Times(Int(5), p, Int(5)), Int(25)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),

            Example(hr="(((1 - 1) * p * 1) = 0)",
                    expr=Equals(Times(Minus(Int(1), Int(1)), p, Int(1)),
                                Int(0)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),

            # Huge Fractions:
            Example(hr="((r * 1606938044258990275541962092341162602522202993782792835301376/7) = -20480000000000000000000000.0)",
                    expr=Equals(Times(r, Real(Fraction(2**200,7))),
                                Real(-200**11)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LRA
                ),

            Example(hr="(((r + 5.0 + s) * (s + 2.0 + r)) = 0.0)",
                    expr=Equals(Times(Plus(r, Real(5), s),
                                      Plus(s, Real(2), r)),
                                Real(0)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_NRA),

            Example(hr="(((p + 5 + q) * (p - (q - 5))) = ((p * p) + (10 * p) + 25 + (-1 * q * q)))",
                    expr=Equals(Times(Plus(p, Int(5), q),
                                      Minus(p, Minus(q, Int(5)))),
                                Plus(Times(p, p),
                                     Times(Int(10), p),
                                     Int(25),
                                     Times(Int(-1), q, q))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_NIA
                ),

        ]
    return result


def get_example_formulae(environment=None):
    """Generates a stream of SExample using the given environment."""
    for (hr, expr, is_valid, is_sat, logic) in get_full_example_formulae(environment):
        yield SExample(expr, is_valid, is_sat, logic)


def get_str_example_formulae(environment=None):
    """Returns a triple from each Example."""
    for (hr, expr, is_valid, is_sat, logic) in get_full_example_formulae(environment):
        yield (hr, expr, logic)
