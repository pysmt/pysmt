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
from six.moves import cStringIO
import unittest
from six.moves import xrange

from pysmt.shortcuts import Or, And, Not, Plus, Iff, Implies
from pysmt.shortcuts import Exists, ForAll, Ite
from pysmt.shortcuts import Bool, Real, Int, Symbol, Function
from pysmt.shortcuts import Times, Minus, Equals, LE, LT, ToReal
from pysmt.typing import REAL, INT, FunctionType
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.test import TestCase

class TestPrinting(TestCase):
    def print_to_string(self, formula):
        buf = cStringIO()
        printer = SmtPrinter(buf)
        printer.printer(formula)

        return buf.getvalue()

    def test_real(self):
        f = Plus([ Real(1),
                   Symbol("x", REAL),
                   Symbol("y", REAL)])

        f_string = self.print_to_string(f)
        self.assertEqual(f_string, "(+ 1.0 x y)")

    def test_boolean(self):
        x, y, z = Symbol("x"), Symbol("y"), Symbol("z")
        f = Or(And(Not(x), Iff(x, y)), Implies(x, z))

        f_string = self.print_to_string(f)
        self.assertEqual(f_string,
                          "(or (and (not x) (= x y)) (=> x z))")

    def test_int(self):
        p, q = Symbol("p", INT), Symbol("q", INT)
        f = Or(Equals(Times(p, Int(5)), Minus(p,q)),
               LT(p,q), LE(Int(6), Int(1)))

        f_string = self.print_to_string(f)
        self.assertEqual(f_string,
                          "(or (= (* p 5) (- p q)) (< p q) (<= 6 1))")

    def test_ite(self):
        x = Symbol("x")
        p, q = Symbol("p", INT), Symbol("q", INT)

        f = Ite(x, p, q)
        f_string = self.print_to_string(f)

        self.assertEqual(f_string,
                          "(ite x p q)")

    def test_quantifiers(self):
        x = Symbol("x")
        fa = ForAll([x], And(x, Not(x)))
        fe = Exists([x], And(x, Not(x)))

        fa_string = self.print_to_string(fa)
        fe_string = self.print_to_string(fe)

        self.assertEqual(fa_string,
                          "(forall ((x Bool)) (and x (not x)))")

        self.assertEqual(fe_string,
                          "(exists ((x Bool)) (and x (not x)))")


    def test_constant(self):
        b1 = Bool(True)
        b2 = Bool(False)
        r1 = Real(5.5)
        r2 = Real(5)
        r3 = Real(-5.5)
        i1 = Int(4)
        i2 = Int(-4)

        b1_string = self.print_to_string(b1)
        b2_string = self.print_to_string(b2)

        self.assertEqual(b1_string, "true")
        self.assertEqual(b2_string, "false")

        r1_string = self.print_to_string(r1)
        r2_string = self.print_to_string(r2)
        r3_string = self.print_to_string(r3)

        self.assertEqual(r1_string, "(/ 11 2)")
        self.assertEqual(r2_string, "5.0")
        self.assertEqual(r3_string, "(- (/ 11 2))")

        i1_string = self.print_to_string(i1)
        i2_string = self.print_to_string(i2)

        self.assertEqual(i1_string, "4")
        self.assertEqual(i2_string, "(- 4)")

    def test_function(self):
        f1_type = FunctionType(REAL, [REAL, REAL])
        f2_type = FunctionType(REAL, [])

        p,q = Symbol("p", REAL), Symbol("q", REAL)
        f1_symbol = Symbol("f1", f1_type)
        f2_symbol = Symbol("f2", f2_type)

        f1 = Function(f1_symbol, [p,q])
        f2 = Function(f2_symbol, [])

        f1_string = self.print_to_string(f1)
        f2_string = self.print_to_string(f2)

        self.assertEqual(f1_string, "(f1 p q)")
        self.assertEqual(f2_string, "(f2)")

    def test_toreal(self):
        p = Symbol("p", INT)
        rp = ToReal(p)

        rp_string = self.print_to_string(rp)
        self.assertEqual(rp_string, "(to_real p)")

    def test_threshold_printing(self):
        x = Symbol("x")
        f = And(x,x)
        for _ in xrange(10):
            f = And(f,f)

        short_f_str = str(f)
        long_f_str = f.serialize()
        self.assertTrue(len(short_f_str) < len(long_f_str))

    def test_daggify(self):
        x = Symbol("x")
        f = And(x,x)
        for _ in xrange(10):
            f = And(f,f)

        tree_buf = cStringIO()
        dag_buf = cStringIO()
        tree_printer = SmtPrinter(tree_buf)
        dag_printer = SmtDagPrinter(dag_buf)

        dag_printer.printer(f)
        tree_printer.printer(f)

        short_f_str = dag_buf.getvalue()
        long_f_str = tree_buf.getvalue()

        self.assertTrue(len(short_f_str) < len(long_f_str))

if __name__ == '__main__':
    unittest.main()
