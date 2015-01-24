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
from pysmt.shortcuts import *
from pysmt.typing import REAL, BOOL, INT, FunctionType


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
                    logic=pysmt.logics.QF_LIA
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
                    logic=pysmt.logics.QF_LIA
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
                    logic=pysmt.logics.QF_LIA
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
                    logic=pysmt.logics.QF_LRA
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
                    logic=pysmt.logics.QF_LRA
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
                    logic=pysmt.logics.QF_LRA
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
