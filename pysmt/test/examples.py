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
                             BV, BVOne, BVZero,
                             BVNot, BVAnd, BVOr, BVXor,
                             BVConcat, BVExtract,
                             BVULT, BVUGT, BVULE, BVUGE,
                             BVNeg, BVAdd, BVMul, BVUDiv, BVURem, BVSub,
                             BVLShl, BVLShr,BVRol, BVRor,
                             BVZExt, BVSExt)
from pysmt.typing import REAL, BOOL, INT, FunctionType, BV8, BV16


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

        rf = Symbol("rf", FunctionType(REAL, [REAL, REAL]))
        rg = Symbol("rg", FunctionType(REAL, [REAL]))

        ih = Symbol("ih", FunctionType(INT, [REAL, INT]))
        ig = Symbol("ig", FunctionType(INT, [INT]))

        bv8 = Symbol("bv1", BV8)
        bv16 =Symbol("bv2", BV16)

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

            # (((bv8 + bv_one) * bv(5)) / bv(5)) < bv(0)
            Example(expr=BVUGT(BVUDiv(BVMul(BVAdd(bv8, BVOne(8)), BV(5, width=8)),
                                      BV(5, width=8)),
                               BVZero(8)),
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


        ]
        return result


EXAMPLE_FORMULAS = get_example_formulae(get_env())
EXAMPLE_FORMULAE = EXAMPLE_FORMULAS
