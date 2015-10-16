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
from pysmt.shortcuts import And, get_env, Iff, Or, is_valid, Symbol, Exists, Implies, ForAll, Not
from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.rewritings import prenex_normal_form, nnf, conjunctive_partition, aig
from pysmt.rewritings import disjunctive_partition
from pysmt.test.examples import get_example_formulae
from pysmt.exceptions import SolverReturnedUnknownResultError
from pysmt.logics import BOOL

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
            if get_env().factory.has_solvers(logic=logic):
                prenex = prenex_normal_form(f)
                try:
                    ok = is_valid(Iff(f, prenex), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok)

    def test_nnf_examples(self):
        for (f, _, _, logic) in get_example_formulae():
            if get_env().factory.has_solvers(logic=logic):
                rf = nnf(f)
                try:
                    ok = is_valid(Iff(f, rf), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok)

    def test_conj_partitioning(self):
        for (f, _, _, logic) in get_example_formulae():
            if get_env().factory.has_solvers(logic=logic):
                conjuncts = list(conjunctive_partition(f))
                try:
                    ok = is_valid(Iff(f, And(conjuncts)), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok)

    def test_disj_partitioning(self):
        for (f, _, _, logic) in get_example_formulae():
            if get_env().factory.has_solvers(logic=logic):
                disjuncts = list(disjunctive_partition(f))
                try:
                    ok = is_valid(Iff(f, Or(disjuncts)), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok)

    def test_aig_examples(self):
        for (f, _, _, logic) in get_example_formulae():
            if get_env().factory.has_solvers(logic=logic):
                f_aig = aig(f)
                try:
                    ok = is_valid(Iff(f, f_aig), logic=logic)
                except SolverReturnedUnknownResultError:
                    ok = not logic.quantifier_free
                self.assertTrue(ok, "Was: %s\n Got:%s" % (f, f_aig))

if __name__ == "__main__":
    main()
