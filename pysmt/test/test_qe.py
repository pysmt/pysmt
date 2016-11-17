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
from pysmt.shortcuts import Symbol, ForAll, Exists, And, Iff, GE, LT, Real, Int
from pysmt.shortcuts import Minus, Equals, Plus, ToReal, Implies, LE, TRUE, Not
from pysmt.shortcuts import Times, QuantifierEliminator
from pysmt.shortcuts import is_sat, is_valid
from pysmt.typing import REAL, BOOL, INT
from pysmt.test import TestCase, main
from pysmt.test import (skipIfNoSolverForLogic, skipIfNoQEForLogic,
                        skipIfQENotAvailable)
from pysmt.test.examples import get_example_formulae
from pysmt.exceptions import (SolverReturnedUnknownResultError, PysmtValueError,
                              NoSolverAvailableError, ConvertExpressionError)
from pysmt.logics import LRA, LIA, UFLIRA


class TestQE(TestCase):

    @skipIfNoSolverForLogic(LRA)
    @skipIfNoQEForLogic(LRA)
    def test_qe_eq(self):
        qe = QuantifierEliminator(logic=LRA)

        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        varAt = Symbol("At", REAL)
        varBt = Symbol("Bt", REAL)

        f = And(Iff(varA, GE(Minus(varAt, varBt), Real(0))),
                Iff(varB, LT(Minus(varAt, varBt), Real(1))))

        qf = Exists([varBt, varA], f)
        r1 = qe.eliminate_quantifiers(qf)

        try:
            self.assertValid(Iff(r1, qf), logic=LRA,
                             msg="The two formulas should be equivalent.")
        except SolverReturnedUnknownResultError:
            pass

    def test_selection(self):
        with self.assertRaises(NoSolverAvailableError):
            QuantifierEliminator(logic=UFLIRA)

        with self.assertRaises(NoSolverAvailableError):
            QuantifierEliminator(name="nonexistent")


    @skipIfNoQEForLogic(LRA)
    def test_selection_lra(self):
        QuantifierEliminator(logic=LRA)

    @skipIfQENotAvailable('z3')
    def test_qe_z3(self):
        qe = QuantifierEliminator(name='z3')
        self._bool_example(qe)
        self._real_example(qe)
        self._int_example(qe)
        self._alternation_bool_example(qe)
        self._alternation_real_example(qe)
        self._alternation_int_example(qe)
        self._std_examples(qe, LRA)
        self._std_examples(qe, LIA)
        self._modular_congruence(qe)

        # Additional test for raising error on back conversion of
        # quantified formulae
        p, q = Symbol("p", INT), Symbol("q", INT)

        f = ForAll([p], Exists([q], Equals(ToReal(p),
                                           Plus(ToReal(q), ToReal(Int(1))))))
        with self.assertRaises(PysmtValueError):
            qe.eliminate_quantifiers(f).simplify()


    @skipIfQENotAvailable('msat_fm')
    def test_qe_msat_fm(self):
        qe = QuantifierEliminator(name='msat_fm')
        self._bool_example(qe)
        self._real_example(qe)
        self._alternation_bool_example(qe)
        self._alternation_real_example(qe)
        self._std_examples(qe, LRA)

        with self.assertRaises(PysmtValueError):
            self._int_example(qe)

        with self.assertRaises(PysmtValueError):
            self._alternation_int_example(qe)

        # Additional test for raising error on back conversion of
        # quantified formulae
        p, q = Symbol("p", INT), Symbol("q", INT)

        f = ForAll([p], Exists([q], Equals(ToReal(p),
                                           Plus(ToReal(q), ToReal(Int(1))))))
        with self.assertRaises(PysmtValueError):
            qe.eliminate_quantifiers(f).simplify()


    @skipIfQENotAvailable('msat_lw')
    def test_qe_msat_lw(self):
        qe = QuantifierEliminator(name='msat_lw')
        self._bool_example(qe)
        self._real_example(qe)
        self._alternation_bool_example(qe)
        self._alternation_real_example(qe)
        self._int_example(qe)
        self._alternation_int_example(qe)
        self._std_examples(qe, LIA)

        self._modular_congruence(qe)

        # Additional test for raising error on back conversion of
        # quantified formulae
        p, q = Symbol("p", INT), Symbol("q", INT)

        f = ForAll([p], Exists([q], Equals(ToReal(p),
                                           Plus(ToReal(q), ToReal(Int(1))))))
        with self.assertRaises(PysmtValueError):
            qe.eliminate_quantifiers(f).simplify()

    def _modular_congruence(self, qe):
        p, q = (Symbol(n, INT) for n in "pq")
        f = Exists([q], Equals(Times(q, Int(2)), p))
        with self.assertRaises(ConvertExpressionError):
            qe.eliminate_quantifiers(f)


    def _bool_example(self, qe):
        # Bool Example
        x, y = Symbol("x"), Symbol("y")

        f = ForAll([x], Implies(x,y))
        qf = qe.eliminate_quantifiers(f).simplify()

        self.assertEqual(qf, y)


    def _real_example(self, qe):
        # Real Example
        r, s = Symbol("r", REAL), Symbol("s", REAL)

        f = ForAll([r], Implies(LT(Real(0), r), LT(s, r)))
        qf = qe.eliminate_quantifiers(f).simplify()

        self.assertEqual(qf, LE(s, Real(0)))


    def _int_example(self, qe):
        # Int Example
        p, q = Symbol("p", INT), Symbol("q", INT)

        f = ForAll([p], Implies(LT(Int(0), p), LT(q, p)))
        qf = qe.eliminate_quantifiers(f).simplify()

        self.assertValid(Iff(qf, LE(q, Int(0))))

    def _alternation_bool_example(self, qe):
        # Alternation of quantifiers
        x, y = Symbol("x"), Symbol("y")

        f = ForAll([x], Exists([y], Iff(x, Not(y))))
        qf = qe.eliminate_quantifiers(f).simplify()

        self.assertEqual(qf, TRUE())


    def _alternation_real_example(self, qe):
        # Alternation of quantifiers
        r, s = Symbol("r", REAL), Symbol("s", REAL)

        f = ForAll([r], Exists([s], Equals(r, Plus(s, Real(1)))))
        qf = qe.eliminate_quantifiers(f).simplify()

        self.assertEqual(qf, TRUE())

    def _alternation_int_example(self, qe):
        # Alternation of quantifiers
        p, q = Symbol("p", INT), Symbol("q", INT)

        f = ForAll([p], Exists([q], Equals(p, Plus(q, Int(1)))))
        qf = qe.eliminate_quantifiers(f).simplify()

        self.assertEqual(qf, TRUE())

    def _std_examples(self, qe, target_logic):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if logic != target_logic: continue
            qf = qe.eliminate_quantifiers(f)
            s = is_sat(qf)
            v = is_valid(qf)

            self.assertEqual(validity, v, f)
            self.assertEqual(satisfiability, s, f)

if __name__ == '__main__':
    main()
