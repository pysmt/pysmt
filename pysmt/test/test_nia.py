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
from pysmt.shortcuts import *
from pysmt.typing import INT, REAL, FunctionType
from pysmt.test import TestCase, main
from pysmt.logics import QF_NIA, NIA


class TestNIA(TestCase):

    def test_nia_pos_const_div_pos_const(self):
        """Integer division between positive constants"""
        a = Symbol("a", INT)
        i_2 = Int(2)
        i_5 = Int(5)

        # a = 5 / 2 = 2
        check = And(Equals(a, Div(i_5, i_2)))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(a), i_2)

    def test_nia_pos_const_div_neg_const(self):
        """Integer division between positive and negative constants"""
        a = Symbol("a", INT)
        m_2 = Int(-2)
        i_5 = Int(5)

        # a = 5 / (-2) = -2
        check = And(Equals(a, Div(i_5, m_2)))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(a), m_2)

    def test_nia_neg_const_div_pos_const(self):
        """Integer division between negative and positive constants"""
        a = Symbol("a", INT)
        m_5 = Int(-5)
        m_3 = Int(-3)
        i_2 = Int(2)

        # a = -5 / 2 = -3
        check = And(Equals(a, Div(m_5, i_2)))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(a), m_3)

    def test_nia_neg_const_div_neg_const(self):
        """Integer division between negative constants"""
        a = Symbol("a", INT)
        m_5 = Int(-5)
        m_2 = Int(-2)
        i_3 = Int(3)

        # a = -5 / (-2) = 3
        check = And(Equals(a, Div(m_5, m_2)))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(a), i_3)

    def test_nia_pos_symb_div_pos_const(self):
        """Positive symbol divided by positive constant"""
        a = Symbol("a", INT)
        i_2 = Int(2)
        i_3 = Int(3)
        i_6 = Int(6)
        i_7 = Int(7)

        # a > 6 & a/2 = 3
        check = And(GT(a, i_6), Equals(Div(a, i_2), i_3))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(a), i_7)

    def test_nia_pos_symb_div_neg_const(self):
        """Positive symbol divided by negative constant"""
        a = Symbol("a", INT)
        m_2 = Int(-2)
        m_3 = Int(-3)
        i_6 = Int(6)
        i_7 = Int(7)

        # a > 6 & a / -2 = -3
        check = And(GT(a, i_6), Equals(Div(a, m_2), m_3))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(a), i_7)

    def test_nia_neg_symb_div_pos_const(self):
        """Negative symbol divided by positive constant"""
        a = Symbol("a", INT)
        i_2 = Int(2)
        m_4 = Int(-4)
        m_6 = Int(6)
        m_7 = Int(-7)
        m_8 = Int(-8)

        # a != -8 & a < -6 & a/2 = -4
        check = And(Not(Equals(a, m_8)), LT(a, m_6), Equals(Div(a, i_2), m_4))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(a), m_7)

    def test_nia_neg_symb_div_neg_const(self):
        """Negative symbol divided by negative constant"""
        a = Symbol("a", INT)
        m_2 = Int(-2)
        i_4 = Int(4)
        m_6 = Int(6)
        m_7 = Int(-7)
        m_8 = Int(-8)

        # a != -8 & a < -6 & a / -2 = 4
        check = And(Not(Equals(a, m_8)), LT(a, m_6), Equals(Div(a, m_2), i_4))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(a), m_7)

    def test_nia_const_div_symb(self):
        """Constant divided by symbol"""
        a = Symbol("a", INT)
        i_0 = Int(0)
        i_2 = Int(2)
        i_5 = Int(5)

        # a > 0 & 5/a = 2
        check = And(GT(a, i_0), Equals(Div(i_5, a), i_2))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(a), i_2)

    def test_nia_symb_div_symb(self):
        """Symbol divided by symbol"""
        a = Symbol("a", INT)
        b = Symbol("b", INT)
        i_0 = Int(0)
        i_2 = Int(2)
        i_5 = Int(5)

        # a = 5 & b > 0 & (a / b) = 2
        check = And(Equals(a, i_5), GT(b, i_0),
                    Equals(Div(a, b), i_2))
        for sname in get_env().factory.all_solvers(logic=QF_NIA):
            with Solver(name=sname) as s:
                s.add_assertion(check)
                c = s.solve()
                self.assertTrue(c)
                self.assertEqual(s.get_value(b), i_2)
