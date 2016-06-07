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
from fractions import Fraction

import pysmt.logics
from pysmt.environment import get_env
from pysmt.shortcuts import (Symbol, Function,
                             Int, Real, FALSE, TRUE,
                             And, Iff, Or, Not, Implies, Ite,
                             LT, LE, GT, GE,
                             Times, Equals, Plus, Minus, Div, ToReal,
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

from pysmt.typing import REAL, BOOL, INT, BV8, BV16, ARRAY_INT_INT
from pysmt.typing import FunctionType, ArrayType


Example = namedtuple('Example',
                     ['expr',
                      'is_valid',
                      'is_sat',
                      'logic'])

def get_example_formulae(environment=None):
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
            # x /\ y
            Example(expr=And(x, y),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL
                ),

            # x <-> y
            Example(expr=Iff(x, y),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL
                ),

            # (x \/ y )  /\ ! ( x \/ y )
            Example(expr=And(Or(x, y), Not(Or(x, y))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BOOL
                ),

            # (x /\ !y)
            Example(expr=And(x, Not(y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL),

            # False -> True
            Example(expr=Implies(FALSE(),TRUE()),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL
                ),

            #
            #  LIA
            #
            # (p > q) /\ x -> y
            Example(expr=And(GT(p, q), Implies(x, y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_IDL
                ),

            # (p + q) = 5 /\ (p > q)
            Example(expr=And(Equals(Plus(p,q),Int(5)) , GT(p, q)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),

            # (p >= q) \/ ( p <= q)
            Example(expr=Or(GE(p, q), LE(p, q)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_IDL
                ),

            # !( p < q * 2 )
            Example(expr=Not(LT(p, Times(q, Int(2)))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),

            # p - (5 - 2) > p
            Example(expr=GT(Minus(p, Minus(Int(5), Int(2))), p),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_IDL
                ),

            # x ? 7: (p + -1) * 3 = q
            Example(expr=Equals(Ite(x,
                                    Int(7),
                                    Times(Plus(p, Int(-1)), Int(3))), q),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),

            Example(expr=LT(p, Plus(q, Int(1))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LIA
                ),
            #
            # LRA
            #
            # (r > s) /\ x -> y
            Example(expr=And(GT(r, s), Implies(x, y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_RDL
                ),

            # (r + s) = 5.6 /\ (r > s)
            Example(expr=And(Equals(Plus(r,s), Real(Fraction("5.6"))) , GT(r, s)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LRA
                ),

            # (r >= s) \/ ( r <= s)
            Example(expr=Or(GE(r, s), LE(r, s)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_RDL
                ),

            # !( (r / (1/2)) < s * 2 )
            Example(expr=Not(LT(Div(r, Real((1,2))), Times(s, Real(2)))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LRA
                ),

            # ! ( r - (5 - 2) > r )
            Example(expr=Not(GT(Minus(r, Minus(Real(5), Real(2))), r)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_RDL
                ),

            # x ? 7: (s + -1) * 3 = r
            Example(expr=Equals( Ite(x, Real(7), Times(Plus(s, Real(-1)), Real(3))), r),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_LRA
                ),

            #
            # EUF
            #

            # f(x) = g(x)
            Example(expr=Iff(Function(bf, (x,)), Function(bg, (x,))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_UF
                ),

            # rf(5, rg(2)) = 0
            Example(expr=Equals(Function(rf, (Real(5), Function(rg, (r,)))), Real(0)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLRA
                ),

            # (rg(r) = 5 + 2) <-> (rg(r) = 7)
            Example(expr=Iff(Equals(Function(rg, [r]), Plus(Real(5), Real(2))),
                             Equals(Function(rg, [r]), Real(7))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLRA
                ),

            # (r = s + 1) & (rg(s) = 5) & (rg(r - 1) = 7)
            Example(expr=And([Equals(r, Plus(s, Real(1))),
                              Equals(Function(rg, [s]), Real(5)),
                              Equals(
                                  Function(rg, [Minus(r, Real(1))]), Real(7))]),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_UFLRA),

            #
            # BV
            #

            # bv_one & bv_zero == bv_zero
            Example(expr=Equals(BVAnd(BVOne(32), BVZero(32)),
                                BVZero(32)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # ~(010) == 101
            Example(expr=Equals(BVNot(BV("010")),
                                BV("101")),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # "111" xor "000" == "000"
            Example(expr=Equals(BVXor(BV("111"), BV("000")),
                                BV("000")),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV),

            # bv8 :: bv8 < bv_zero
            Example(expr=BVULT(BVConcat(bv8, bv8),
                               BVZero(16)),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV),

            # bv_one[:7] == bv_one
            Example(expr=Equals(BVExtract(BVOne(32), end=7),
                                BVOne(8)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # (((bv8 + bv_one) * bv(5)) / bv(5)) > bv(0)
            Example(expr=BVUGT(BVUDiv(BVMul(BVAdd(bv8, BVOne(8)), BV(5, width=8)),
                                      BV(5, width=8)),
                               BVZero(8)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # bv16 >=u bv(0)
            Example(expr=BVUGE(bv16, BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # bv16 >=s bv(0)
            Example(expr=BVSGE(bv16, BVZero(16)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # (BV(5) rem BV(2) > bv_zero) /\ (BV(5) rem BV(2) < bv_one)
            Example(expr=And(BVUGT(BVURem(BV(5, width=32), BV(2, width=32)), BVZero(32)),
                             BVULE(BVURem(BV(5, width=32), BV(2, width=32)), BVOne(32))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # ((bv_one + (- bv_one)) << 1) >> 1 == bv_one
            Example(expr=Equals(BVLShr(BVLShl(BVAdd(BVOne(32),
                                                    BVNeg(BVOne(32))),
                                              1), 1),
                                BVOne(32)),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV),

            # bv_one - bv_one == bv_zero
            Example(expr=Equals(BVSub(BVOne(32), BVOne(32)), BVZero(32)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # Rotations
            Example(expr=Equals(BVRor(BVRol(BVOne(32), 1),1), BVOne(32)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # Extensions
            Example(expr=Equals(BVZExt(BVZero(5), 11),
                                BVSExt(BVZero(1), 15)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # bv16 - bv16 = 0_16
            Example(expr=Equals(BVSub(bv16, bv16), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # (bv16 - bv16)[0:7] = bv8
            Example(expr=Equals(BVExtract(BVSub(bv16, bv16), 0, 7), bv8),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # (bv16[0,7] comp bv8) = bv1
            Example(expr=Equals(BVComp(BVExtract(bv16, 0, 7), bv8), BVOne(1)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # (bv16 comp bv16) = bv0
            Example(expr=Equals(BVComp(bv16, bv16), BVZero(1)),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV),

            # (bv16 s< bv16)
            Example(expr=BVSLT(bv16, bv16),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV),

            # (bv16 s< 0_16)
            Example(expr=BVSLT(bv16, BVZero(16)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # (0_16 >s bv16 | bv16 >= 0_16)
            Example(expr=Or(BVSGT(BVZero(16), bv16), BVSGE(bv16, BVZero(16))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),


            # (bv16 u< bv16)
            Example(expr=BVULT(bv16, bv16),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV),

            # (bv16 s< 0_16)
            Example(expr=BVULT(bv16, BVZero(16)),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV),

            # (bv16 | 0_16) = bv16
            Example(expr=Equals(BVOr(bv16, BVZero(16)), bv16),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # (bv16 & 0_16) = 0_16
            Example(expr=Equals(BVAnd(bv16, BVZero(16)), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # 0_16 s< bv16 & ((bv16 s/ -1) s< 0)
            Example(expr=And(BVSLT(BVZero(16), bv16),
                             BVSLT(BVSDiv(bv16, SBV(-1, 16)), BVZero(16))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # 0_16 s< bv16 & ((bv16 s% -1) s< 0)
            Example(expr=And(BVSLT(BVZero(16), bv16),
                             BVSLT(BVSRem(bv16, BVOne(16)), BVZero(16))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_BV),

            # bv16 u% 1 = 0_16
            Example(expr=Equals(BVURem(bv16, BVOne(16)), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # bv16 s% 1 = 0_16
            Example(expr=Equals(BVSRem(bv16, BVOne(16)), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # bv16 s% -1 = 0_16
            Example(expr=Equals(BVSRem(bv16, BVNeg(BVOne(16))), BVZero(16)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # bv16 a>> 0 = bv16
            Example(expr=Equals(BVAShr(bv16, BVZero(16)), bv16),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),

            # 0 s<= bv16 & bv16 a>> 1 = bv16 >> 1
            Example(expr=And(BVSLE(BVZero(16), bv16),
                             Equals(BVAShr(bv16, BVOne(16)),
                                    BVLShr(bv16, BVOne(16)))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BV),


            #
            # Quantification
            #

            # forall y . x -> y
            Example(expr=ForAll([y], Implies(x,y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.BOOL
                ),


            # forall p,q . p + q = 0
            Example(expr=ForAll([p,q], Equals(Plus(p,q), Int(0))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.LIA
                ),

            # forall r,s . ((r > 0) & (s > 0)) -> (r - s < r)
            Example(expr=ForAll([r,s],
                                Implies(And(GT(r, Real(0)), GT(s, Real(0))),
                                        (LT(Minus(r,s), r)))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.LRA
                ),

            # exists x,y . x -> y
            Example(expr=Exists([x,y], Implies(x,y)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.BOOL
                ),

            # exists p,q . p + q = 0
            Example(expr=Exists([p,q], Equals(Plus(p,q), Int(0))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.LIA
                ),

            # exists r . forall s .  (r - s > r)
            Example(expr=Exists([r], ForAll([s], GT(Minus(r,s), r))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.LRA
                ),

            # forall r . exists s .  (r - s > r)
            Example(expr=ForAll([r], Exists([s], GT(Minus(r,s), r))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.LRA
                ),

            # x /\ forall r. (r + s = 5)
            Example(expr=And(x, ForAll([r], Equals(Plus(r,s), Real(5)))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.LRA
                ),

            # exists x . ((x <-> (s > 5)) & (s < 3))
            Example(expr=Exists([x], (And(Iff(x, GT(s, Real(5))),
                                          LT(s, Real(3))))),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.LRA),

            #
            # UFLIRA
            #

            # ih(r,q) > p /\ (x -> y)
            Example(expr=And(GT(Function(ih, (r, q)), p), Implies(x, y)),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLIRA
                ),

            # ( (p - 3) = q ) -> ( ih(r, q + 3) > p \/ ih(r, p) <= p )
            Example(expr=Implies(Equals(Minus(p, Int(3)), q),
                                 Or(GT(Function(ih, (r, Plus(q, Int(3)))), p),
                                    LE(Function(ih, (r, p)), p))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLIRA
                ),

            # ( (ToReal(p - 3) = r) /\ (ToReal(q) = r) ) ->
            #     ( ( ih(ToReal(p - 3), q + 3) > p ) \/ (ih(r, p) <= p) )
            Example(expr=Implies(And(Equals(ToReal(Minus(p, Int(3))), r),
                                     Equals(ToReal(q), r)),
                                 Or(GT(Function(ih, (ToReal(Minus(p, Int(3))),
                                                     Plus(q, Int(3)))), p),
                                    LE(Function(ih, (r, p)), p))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_UFLIRA
                ),

            # ! ( (ToReal(p - 3) = r /\ ToReal(q) = r) ->
            #        ( ih(ToReal(p - 3), q + 3) > p  \/
            #          ih(r,p) <= p ) )
            Example(expr=Not(Implies(And(Equals(ToReal(Minus(p, Int(3))), r),
                                         Equals(ToReal(q), r)),
                                     Or(GT(Function(ih, (ToReal(Minus(p, Int(3))),
                                                         Plus(q, Int(3)))), p),
                                        LE(Function(ih, (r, p)), p)))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.QF_UFLIRA
                ),

            # Test complex names
            Example(expr=And(Symbol("Did you know that any string works? #yolo"),
                             Symbol("10"),
                             Symbol("|#somesolverskeepthe||"),
                             Symbol(" ")),
                    is_valid=False,
                    is_sat=True,
                    logic=pysmt.logics.QF_BOOL
                ),
            # Arrays
            # q=0 -> Store(aii, 0, 0) = Store(aii, 0, q)
            Example(expr=Implies(Equals(q, Int(0)),
                                 Equals(Store(aii, Int(0), Int(0)),
                                        Store(aii, Int(0), q))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_ALIA),
            # Select(Store(aii, 0, 0), 0) = 0
            Example(expr=Equals(Select(Store(aii, Int(0), Int(0)), Int(0)),
                                Int(0)),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_ALIA),

            # Array<Int,Int>(0)[1 := 1] = aii & aii[1] = 0
            Example(expr=And(Equals(Array(INT, Int(0), {Int(1) : Int(1)}), aii), Equals(Select(aii, Int(1)), Int(0))),
                    is_valid=False,
                    is_sat=False,
                    logic=pysmt.logics.get_logic_by_name("QF_ALIA*")),

            # nested_a = Array<Array<Real,BV8>,Array<Int,Int>>(Array<Int,Int>(7))
            #  -> Select(Select(nested_a, arb), 42) = 7
            Example(expr=Implies(Equals(nested_a, Array(ArrayType(REAL, BV8),
                                                        Array(INT, Int(7)))),
                                 Equals(Select(Select(nested_a, arb), Int(42)),
                                        Int(7))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.get_logic_by_name("QF_AUFBVLIRA*")),

            # Store(Store(a, x, y), x, z) = Store(a, x, z)
            Example(expr=Equals(Store(Store(abb, bv8, Symbol("y_", BV8)),
                                      bv8, Symbol("z_", BV8)),
                                Store(abb, bv8, Symbol("z_", BV8))),
                    is_valid=True,
                    is_sat=True,
                    logic=pysmt.logics.QF_ABV),
        ]
        return result


EXAMPLE_FORMULAS = get_example_formulae(get_env())
EXAMPLE_FORMULAE = EXAMPLE_FORMULAS
