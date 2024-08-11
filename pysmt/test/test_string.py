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
from pysmt.test import TestCase, skipIfNoSolverForLogic
from pysmt.shortcuts import (Not, Implies, Equals, Symbol, GE, GT, LT, And,
                             Int, Plus, TRUE, FALSE)
from pysmt.shortcuts import (String, StrConcat, StrLength, StrContains,
                             StrIndexOf, StrReplace, StrSubstr,
                             StrPrefixOf, StrSuffixOf, StrToInt, IntToStr,
                             StrCharAt, Solver)
from pysmt.typing import INT, STRING
from pysmt.logics import QF_SLIA


class TestString(TestCase):
    #MG: This test suit overlaps with examples.py
    #    we might want to include tests of more things like:
    #    - Simplifications at construction time
    #    - Infix notation
    #    - Constants and unicode support

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_length(self):
        s1 = Symbol("s1", STRING)
        s2 = Symbol("s2", STRING)
        f = Not(Implies(Equals(s1, s2),
                        Equals(StrLength(s2), StrLength(s1))))
        self.assertUnsat(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_concat(self):
        s1 = Symbol("s1", STRING)
        s2 = Symbol("s2", STRING)

        f = Equals(StrConcat(s1, s1), s2)
        self.assertSat(f)
        f = Not(And(GE(StrLength(StrConcat(s1, s2)),
                       StrLength(s1)),
                    GE(StrLength(StrConcat(s1, s2)),
                       StrLength(s2))))
        self.assertUnsat(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_contains(self):
        s1 = Symbol("s1", STRING)
        s2 = Symbol("s2", STRING)
        f = Not(Implies(And(StrContains(s1, s2),
                            StrContains(s2, s1)),
                        Equals(s1, s2)))
        self.assertUnsat(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_indexof(self):
        s1 = String("Hello World")
        t1 = String("o")
        # MG: Make offset argument optional (default 0) StrIndexOf
        f = Not(Equals(StrIndexOf(s1, t1, Int(0)), Int(4)))
        self.assertUnsat(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_replace(self):
        s1 = Symbol("s1", STRING)
        s2 = Symbol("s2", STRING)
        s3 = Symbol("s3", STRING)

        f = Equals(StrReplace(s1, s2, s3), s3)
        self.assertSat(f)
        f = And(GT(StrLength(s1), Int(0)),
                GT(StrLength(s2), Int(0)),
                GT(StrLength(s3), Int(0)),
                Not(StrContains(s1, s2)),
                Not(StrContains(s1, s3)),
                Not(Equals(StrReplace(StrReplace(s1, s2,s3), s3, s2), s1)))
        self.assertUnsat(f)

        # Replace first v Replace First
        f = Implies(And(Equals(s1, String("Hello")),
                        Equals(s2, StrReplace(s1, String("l"), String(" ")))),
                    Equals(s2, String("He lo")))
        self.assertValid(f, logic="QF_SLIA")

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_substr(self):
        s1 = Symbol("s1", STRING)
        i = Symbol("index", INT)
        f = And(GT(i, Int(0)),
                GT(StrLength(s1), Int(1)),
                LT(i, StrLength(s1)),
                Equals(StrConcat(StrSubstr(s1, Int(0), i),
                                 StrSubstr(s1, Plus(i, Int(1)),
                                           StrLength(s1))),
                       s1))
        self.assertUnsat(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_prefixof(self):
        s1 = Symbol("s1", STRING)
        s2 = Symbol("s2", STRING)
        f = And(GT(StrLength(s1), Int(2)),
                GT(StrLength(s2), StrLength(s1)),
                And(StrPrefixOf(s2, s1), StrContains(s2, s1)))
        self.assertUnsat(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_suffixof(self):
        s1 = Symbol("s1", STRING)
        s2 = Symbol("s2", STRING)
        f = And(GT(StrLength(s1), Int(2)),
                GT(StrLength(s2), StrLength(s1)),
                And(StrSuffixOf(s2, s1), StrContains(s2, s1)))
        self.assertUnsat(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_to_int(self):
        f = Equals(StrToInt(String("1")), Int(1))
        self.assertValid(f)
        f = Equals(StrToInt(String("-55")), Int(-1))
        self.assertValid(f)
        f = Equals(StrToInt(String("pippo")), Int(-1))
        self.assertValid(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_int_to_str(self):
        f = Equals((IntToStr(Int(1))), String("1"))
        self.assertValid(f)
        f = Equals(IntToStr(Int(-1)), String(""))
        self.assertValid(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_charat(self):
        s1 = String("Hello")
        f = Equals(StrCharAt(s1, Int(0)), String("H"))
        self.assertValid(f)

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_model(self):
        s = Symbol("s", STRING)
        f = [ Equals(StrLength(s), Int(5)),
              Equals(StrCharAt(s, Int(0)), String("A")),
              Not(Equals(StrCharAt(s, Int(2)), String("B")))]
        with Solver(logic=QF_SLIA) as solver:
            solver.add_assertion(And(f))
            res = solver.solve()
            self.assertTrue(res)
            s_value = solver.get_value(s)
            py_value = s_value.constant_value()
            self.assertEqual(py_value[0], "A")
            self.assertNotEqual(py_value[1], "B")
            self.assertEqual(len(py_value), 5)

    def test_simplification(self):
        constA, constB = String("Hello"), String("World")
        test_set = [(StrLength(constA), Int(5)),
                    (StrConcat(constA, constB), String("HelloWorld")),
                    (StrContains(constA, String("H")), TRUE()),
                    (StrContains(constB, String("H")), FALSE()),
                    (StrIndexOf(constA, String("e"), Int(0)), Int(1)),
                    (StrReplace(constA, String("l"), String(" ")), String("He lo")),
                    (StrSubstr(constA, Int(1), Int(2)), String("el")),
                    (StrPrefixOf(constA, constB), FALSE()),
                    (StrPrefixOf(String("He"), constA), TRUE()),
                    (StrSuffixOf(constA, constB), FALSE()),
                    (StrSuffixOf(String("lo"), constB), FALSE()),
                    (StrToInt(constA), Int(-1)),
                    (StrToInt(String("55")), Int(55)),
                    (IntToStr(Int(10)), String("10")),
                    (IntToStr(Int(-1)), String("")),
                    (StrCharAt(constA, Int(2)), String("l")),
                ]

        for (f, simplified) in test_set:
            self.assertEqual(f.simplify(), simplified)

    def test_theory_oracle(self):
        from pysmt.oracles import get_logic
        s1 = Symbol("s1", STRING)
        s2 = Symbol("s2", STRING)

        f = Equals(StrConcat(s1, s1), s2)
        theory = get_logic(f).theory
        self.assertTrue(theory.strings, theory)

        f = Not(And(GE(StrLength(StrConcat(s1, s2)),
                       StrLength(s1)),
                    GE(StrLength(StrConcat(s1, s2)),
                       StrLength(s2))))
        theory = get_logic(f).theory
        self.assertTrue(theory.strings, theory)

        f = And(GT(StrLength(s1), Int(2)),
                GT(StrLength(s2), StrLength(s1)),
                And(StrSuffixOf(s2, s1), StrContains(s2, s1)))
        theory = get_logic(f).theory
        self.assertTrue(theory.strings, theory)

if __name__ == "__main__":
    from pysmt.test import main
    main()
