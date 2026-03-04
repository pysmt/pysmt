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
from pysmt.shortcuts import (And, Iff, Or, Symbol, Implies, Not,
                             Exists, ForAll,
                             Times, Plus, Minus, Equals, Real,
                             LT,
                             Int,
                             is_valid, is_sat, Function)
from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.rewritings import prenex_normal_form, nnf, conjunctive_partition, aig
from pysmt.rewritings import disjunctive_partition, propagate_toplevel
from pysmt.rewritings import TimesDistributor, Ackermannizer
from pysmt.test.examples import get_example_formulae
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.logics import BOOL, QF_NRA, QF_LRA, QF_LIA, QF_AUFLIA
from pysmt.typing import REAL, INT, FunctionType


class TestRewritings(TestCase):

    def test_prenex_basic(self):
        a,b,c = (Symbol(x) for x in "abc")
        f = Not(And(a, Exists([b], And(a, b)), ForAll([c], Or(a, c))))
        prenex = prenex_normal_form(f)
        # Two prenex normal forms are possible
        my_prenex_1 = Exists([c], ForAll([b], Not(And(a, And(a, b), Or(a, c)))))
        my_prenex_2 = ForAll([b], Exists([c], Not(And(a, And(a, b), Or(a, c)))))
        self.assertTrue(prenex == my_prenex_1 or prenex == my_prenex_2)

    @skipIfNoSolverForLogic(BOOL)
    def test_prenex_simple_exists(self):
        a,b = (Symbol(x) for x in "ab")
        f = And(b, Exists([b], Implies(a, b)))
        prenex = prenex_normal_form(f)
        self.assertTrue(prenex.is_exists())
        self.assertValid(Iff(f, prenex), logic=BOOL)

    @skipIfNoSolverForLogic(BOOL)
    def test_prenex_simple_forall(self):
        a,b = (Symbol(x) for x in "ab")
        f = Or(b, ForAll([b], Implies(a, b)))
        prenex = prenex_normal_form(f)
        self.assertTrue(prenex.is_forall())
        self.assertValid(Iff(f, prenex), logic=BOOL)

    @skipIfNoSolverForLogic(BOOL)
    def test_prenex_negated_exists(self):
        a,b = (Symbol(x) for x in "ab")
        f = Implies(Exists([b], Implies(a, b)), b)
        prenex = prenex_normal_form(f)
        self.assertTrue(prenex.is_forall())
        self.assertValid(Iff(f, prenex), logic=BOOL)

    @skipIfNoSolverForLogic(BOOL)
    def test_prenex_negated_forall(self):
        a,b = (Symbol(x) for x in "ab")
        f = Implies(ForAll([b], Implies(a, b)), b)
        prenex = prenex_normal_form(f)
        self.assertTrue(prenex.is_exists())
        self.assertValid(Iff(f, prenex), logic=BOOL)

    def test_prenex_examples(self):
        for (f, _, _, logic) in get_example_formulae():
            if self.env.factory.has_solvers(logic=logic):
                prenex = prenex_normal_form(f)
                if ( prenex is not None):
                    try:
                        ok = is_valid(Iff(f, prenex), logic=logic)
                    except SolverReturnedUnknownResultError:
                        ok = not logic.quantifier_free
                    self.assertTrue(ok)

    @skipIfNoSolverForLogic(QF_AUFLIA)
    def test_ackermannization_unary(self):
        self.env.enable_infix_notation = True
        a, b = (Symbol(x, INT) for x in "ab")
        f, g, h = (Symbol(x, FunctionType(INT, [INT])) for x in "fgh")

        formula1 = Not(Equals(f(g(h(a))),
                              f(g(h(b)))))
        formula2 = Equals(a, b)
        formula = And(formula1, formula2)
        self._verify_ackermannization(formula)

    @skipIfNoSolverForLogic(QF_AUFLIA)
    def test_ackermannization_pairwise(self):
        self.env.enable_infix_notation = True
        a, b, c, d = (Symbol(x, INT) for x in "abcd")
        f = Symbol("f", FunctionType(INT, [INT]))
        formula = And(Not(Equals(f(b), f(c))),
                      Equals(f(a), f(b)),
                      Equals(f(c), f(d)),
                      Equals(a, d))
        self.assertUnsat(formula)
        formula_ack = Ackermannizer().do_ackermannization(formula)
        self.assertUnsat(formula_ack)


    @skipIfNoSolverForLogic(QF_AUFLIA)
    def test_ackermannization_explicit(self):
        self.env.enable_infix_notation = True
        a,b = (Symbol(x, INT) for x in "ab")
        f,g = (Symbol(x, FunctionType(INT, [INT, INT])) for x in "fg")
        h = Symbol("h", FunctionType(INT, [INT]))

        formula1 = Not(Equals(f(a, g(a, h(a))),
                              f(b, g(b, h(b)))))

        # Explicit the Ackermanization of this expression We end up
        # with a conjunction of implications that is then conjoined
        # with the original formula.
        ackermannization = Ackermannizer()
        actual_ack = ackermannization.do_ackermannization(formula1)

        terms_to_consts = ackermannization.get_term_to_const_dict()
        ack_h_a = terms_to_consts[h(a)]
        ack_h_b = terms_to_consts[h(b)]
        ack_g_a_h_a = terms_to_consts[g(a, h(a))]
        ack_g_b_h_b = terms_to_consts[g(b, h(b))]
        ack_f_a_g_a_h_a = terms_to_consts[f(a, g(a, h(a)))]
        ack_f_b_g_b_h_b = terms_to_consts[f(b, g(b, h(b)))]

        target_ack = And(
            Equals(a, b).Implies(Equals(ack_h_a, ack_h_b)),
            And(Equals(a, b),
                Equals(ack_h_a, ack_h_b)).Implies(
                    Equals(ack_g_a_h_a, ack_g_b_h_b)),
            And(Equals(a, b),
                Equals(ack_h_a, ack_h_b),
                Equals(ack_g_a_h_a, ack_g_b_h_b)).Implies(
                    Equals(ack_f_a_g_a_h_a, ack_f_b_g_b_h_b)))
        target_ack = And(target_ack,
                         Not(Equals(ack_f_a_g_a_h_a, ack_f_b_g_b_h_b)))
        self.assertValid(target_ack.Iff(actual_ack))

    @skipIfNoSolverForLogic(QF_AUFLIA)
    def test_ackermannization_binary(self):
        self.env.enable_infix_notation = True
        a,b = (Symbol(x, INT) for x in "ab")
        f,g = (Symbol(x, FunctionType(INT, [INT, INT])) for x in "fg")
        h = Symbol("h", FunctionType(INT, [INT]))

        formula1 = Not(Equals(f(a, g(a, h(a))),
                              f(b, g(b, h(b)))))

        formula2 = Equals(a, b)
        formula = And(formula1, formula2)
        self._verify_ackermannization(formula)

    def test_ackermannization_for_examples(self):
        for (f, _, _, logic) in get_example_formulae():
            if not logic.is_quantified() and logic.theory.uninterpreted:
                if self.env.factory.has_solvers(logic=logic):
                    self._verify_ackermannization(f)

    def test_ackermannization_dictionaries(self):
        self.env.enable_infix_notation = True
        a,b = (Symbol(x, INT) for x in "ab")
        f,g = (Symbol(x, FunctionType(INT, [INT, INT])) for x in "fg")
        h = Symbol("h", FunctionType(INT, [INT]))

        formula1 = Not(Equals(f(a, g(a, h(a))),
                              f(b, g(b, h(b)))))
        formula2 = Equals(a, b)
        formula = And(formula1, formula2)
        ackermannization = Ackermannizer()
        _ = ackermannization.do_ackermannization(formula)
        terms_to_consts = ackermannization.get_term_to_const_dict()
        consts_to_terms = ackermannization.get_const_to_term_dict()
        # The maps have the same length
        self.assertEqual(len(terms_to_consts), len(consts_to_terms))
        # The maps are the inverse of each other
        for t in terms_to_consts:
            self.assertEqual(t, consts_to_terms[terms_to_consts[t]])
        # Check that the the functions are there
        for atom in formula.get_atoms():
            if atom.is_function_application():
                self.assertIsNotNone(terms_to_consts[atom])

    def _verify_ackermannization(self, formula):
        ackermannization = Ackermannizer()
        ack = ackermannization.do_ackermannization(formula)
        #verify that there are no functions in ack
        atoms = ack.get_atoms()
        for atom in atoms:
            for arg in atom.args():
                self.assertFalse(arg.is_function_application())
        #verify that ack and formula are equisat
        formula_sat = is_sat(formula)
        ack_sat = is_sat(ack)
        self.assertTrue(formula_sat == ack_sat)

    def test_nnf_examples(self):
        for (f, _, _, logic) in get_example_formulae():
            if self.env.factory.has_solvers(logic=logic):
                rf = nnf(f)
                try:
                    ok = is_valid(Iff(f, rf), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok)

    def test_conj_partitioning(self):
        for (f, _, _, logic) in get_example_formulae():
            if self.env.factory.has_solvers(logic=logic):
                conjuncts = list(conjunctive_partition(f))
                try:
                    ok = is_valid(Iff(f, And(conjuncts)), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok)

    def test_disj_partitioning(self):
        for (f, _, _, logic) in get_example_formulae():
            if self.env.factory.has_solvers(logic=logic):
                disjuncts = list(disjunctive_partition(f))
                try:
                    ok = is_valid(Iff(f, Or(disjuncts)), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok)

    def test_propagate_toplevel_examples(self):
       for (f, _, _, logic) in get_example_formulae():
            if self.env.factory.has_solvers(logic=logic):
                rwf = propagate_toplevel(f)
                try:
                    ok = is_valid(Iff(f, rwf), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok)

    def test_propagate_toplevel(self):
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)

        f = And(LT(Real(4), Times(x, x)), Equals(Real(1), x))
        fp = propagate_toplevel(f)
        self.assertTrue(fp.is_false())
        if self.env.factory.has_solvers(logic=QF_NRA):
            try:
                ok = is_valid(Iff(f, fp))
            except SolverReturnedUnknownResultError:
                ok = not logic.quantifier_free
            self.assertTrue(ok)

        f = And(LT(Real(4), Times(x, x)), Equals(y, x), Equals(y, Real(1)))
        fp = propagate_toplevel(f)
        self.assertTrue(fp.is_false())
        if self.env.factory.has_solvers(logic=QF_NRA):
            try:
                ok = is_valid(Iff(f, fp))
            except SolverReturnedUnknownResultError:
                ok = not logic.quantifier_free
            self.assertTrue(ok)

        f = And(Equals(Real(4), x), Equals(y, x), Equals(y, Real(0)))
        fp = propagate_toplevel(f)
        self.assertTrue(fp.is_false())
        fp = propagate_toplevel(f, preserve_equivalence=False)
        self.assertTrue(fp.is_false())
        fp = propagate_toplevel(f, preserve_equivalence=False, do_simplify=False)
        self.assertTrue(fp.is_false())

        f = Equals(Real(4), Real(5))
        fp = propagate_toplevel(f, do_simplify=False)
        self.assertTrue(fp.is_false())

    def test_aig_examples(self):
        for (f, _, _, logic) in get_example_formulae():
            if self.env.factory.has_solvers(logic=logic):
                f_aig = aig(f)
                try:
                    ok = is_valid(Iff(f, f_aig), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok, "Was: %s\n Got:%s" % (f, f_aig))

    @skipIfNoSolverForLogic(QF_NRA)
    def test_times_distributivity(self):
        r = Symbol("r", REAL)
        s = Symbol("s", REAL)
        td = TimesDistributor()

        f = Times(Plus(r, Real(1)), Real(3))
        fp = td.walk(f)
        self.assertValid(Equals(f, fp), (f, fp))

        f = Times(Plus(r, Real(1)), s)
        fp = td.walk(f)
        self.assertValid(Equals(f, fp), (f, fp))

        f = Times(Plus(r, Real(1), s), Real(3))
        fp = td.walk(f)
        self.assertValid(Equals(f, fp), (f, fp))

        f = Times(Minus(r, Real(1)), Real(3))
        fp = td.walk(f)
        self.assertValid(Equals(f, fp), (f, fp))

        f = Times(Minus(r, Real(1)), s)
        fp = td.walk(f)
        self.assertValid(Equals(f, fp), (f, fp))

        f = Times(Minus(Real(1), s), Real(3))
        fp = td.walk(f)
        self.assertValid(Equals(f, fp), (f, fp))

        f = Times(Minus(r, Real(1)), Plus(r, s))
        fp = td.walk(f)
        self.assertValid(Equals(f, fp), (f, fp))

        # (r + 1) * (s-1) = r*s + (-r) + s - 1
        f = Times(Plus(r, Real(1)), Minus(s, Real(1)))
        fp = td.walk(f).simplify()
        target = Plus(Times(r, s),
                      Times(r, Real(-1)),
                      s,
                      Real(-1))
        self.assertValid(Equals(fp, target), fp)

    @skipIfNoSolverForLogic(QF_NRA)
    def test_times_distributivity_smtlib_nra(self):
        from pysmt.test.smtlib.parser_utils import formulas_from_smtlib_test_set
        test_set = formulas_from_smtlib_test_set(logics=[QF_LRA, QF_NRA])
        for (_, fname, f, _) in test_set:
            td = TimesDistributor()
            _ = td.walk(f)
            for (old, new) in td.memoization.items():
                if not old.is_times(): continue
                if old is new: continue # Nothing changed
                self.assertValid(Equals(old, new),
                                 (old, new), solver_name="z3")

    @skipIfNoSolverForLogic(QF_LIA)
    def test_minus_0(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        i_0 = Int(0)
        src = Plus(x, y)
        src = Minus(x, src)
        src = LT(src, i_0)
        td = TimesDistributor()
        res = td.walk(src)
        self.assertValid(Iff(src, res))

    @skipIfNoSolverForLogic(QF_LIA)
    def test_minus_1(self):
        """walk_minus should not create nested Plus nodes"""
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        oldx = Symbol("oldx", INT)
        m_1 = Int(-1)
        i_2 = Int(2)
        i_4 = Int(4)
        src = Times(i_2, oldx)
        src = Plus(src, x)
        src = Minus(src, Times(i_4, y))
        src = Times(m_1, src)
        td = TimesDistributor()
        res = td.walk(src)
        self.assertValid(Equals(src, res))
        # root is Plus.
        self.assertTrue(res.is_plus(),
                        "Expeted summation, got: {}".format(res))
        # no other Plus in children: only Times of symbs and constants.
        stack = list(res.args())
        while stack:
            curr = stack.pop()
            if curr.is_times():
                stack.extend(curr.args())
            else:
                self.assertTrue(curr.is_symbol() or curr.is_constant(),
                                "Expected leaf, got: {}".format(res))


if __name__ == "__main__":
    main()
