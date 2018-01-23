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
from six.moves import xrange

from pysmt.shortcuts import Or, And, Not, Plus, Iff, Implies
from pysmt.shortcuts import Exists, ForAll, Ite, ExactlyOne
from pysmt.shortcuts import Bool, Real, Int, Symbol, Function
from pysmt.shortcuts import Times, Minus, Equals, LE, LT, ToReal, FreshSymbol
from pysmt.typing import REAL, INT, FunctionType
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.printers import smart_serialize
from pysmt.test import TestCase, main
from pysmt.test.examples import get_str_example_formulae


class TestPrinting(TestCase):
    def print_to_string(self, formula):
        return formula.to_smtlib(daggify=False)

    def test_real(self):
        f = Plus([ Real(1),
                   Symbol("x", REAL),
                   Symbol("y", REAL)])

        self.assertEqual(f.to_smtlib(daggify=False), "(+ 1.0 x y)")
        self.assertEqual(f.to_smtlib(daggify=True), "(let ((.def_0 (+ 1.0 x y))) .def_0)")

    def test_boolean(self):
        x, y, z = Symbol("x"), Symbol("y"), Symbol("z")
        f = Or(And(Not(x), Iff(x, y)), Implies(x, z))

        self.assertEqual(f.to_smtlib(daggify=False),
                          "(or (and (not x) (= x y)) (=> x z))")
        self.assertEqual(f.to_smtlib(daggify=True),
                          "(let ((.def_0 (=> x z))) (let ((.def_1 (= x y))) (let ((.def_2 (not x))) (let ((.def_3 (and .def_2 .def_1))) (let ((.def_4 (or .def_3 .def_0))) .def_4)))))")

    def test_int(self):
        p, q = Symbol("p", INT), Symbol("q", INT)
        f = Or(Equals(Times(p, Int(5)), Minus(p,q)),
               LT(p,q), LE(Int(6), Int(1)))

        self.assertEqual(f.to_smtlib(daggify=False),
                          "(or (= (* p 5) (- p q)) (< p q) (<= 6 1))")
        self.assertEqual(f.to_smtlib(daggify=True),
                          "(let ((.def_0 (<= 6 1))) (let ((.def_1 (< p q))) (let ((.def_2 (- p q))) (let ((.def_3 (* p 5))) (let ((.def_4 (= .def_3 .def_2))) (let ((.def_5 (or .def_4 .def_1 .def_0))) .def_5))))))")

    def test_ite(self):
        x = Symbol("x")
        p, q = Symbol("p", INT), Symbol("q", INT)

        f = Ite(x, p, q)

        self.assertEqual(f.to_smtlib(daggify=False),
                         "(ite x p q)")
        self.assertEqual(f.to_smtlib(daggify=True),
                         "(let ((.def_0 (ite x p q))) .def_0)")

    def test_quantifiers(self):
        x = Symbol("x")
        fa = ForAll([x], And(x, Not(x)))
        fe = Exists([x], And(x, Not(x)))

        self.assertEqual(fa.to_smtlib(daggify=False),
                         "(forall ((x Bool)) (and x (not x)))")
        self.assertEqual(fe.to_smtlib(daggify=False),
                         "(exists ((x Bool)) (and x (not x)))")
        self.assertEqual(fa.to_smtlib(daggify=True),
                         "(let ((.def_0 (forall ((x Bool)) (let ((.def_0 (not x))) (let ((.def_1 (and x .def_0))) .def_1))))).def_0)")
        self.assertEqual(fe.to_smtlib(daggify=True),
                         "(let ((.def_0 (exists ((x Bool)) (let ((.def_0 (not x))) (let ((.def_1 (and x .def_0))) .def_1))))).def_0)")


    def test_constant(self):
        b1 = Bool(True)
        b2 = Bool(False)
        r1 = Real(5.5)
        r2 = Real(5)
        r3 = Real(-5.5)
        i1 = Int(4)
        i2 = Int(-4)

        self.assertEqual(b1.to_smtlib(daggify=True), "true")
        self.assertEqual(b2.to_smtlib(daggify=True), "false")

        self.assertEqual(r1.to_smtlib(daggify=True), "(/ 11 2)")
        self.assertEqual(r2.to_smtlib(daggify=True), "5.0")
        self.assertEqual(r3.to_smtlib(daggify=True), "(- (/ 11 2))")

        self.assertEqual(i1.to_smtlib(daggify=True), "4")
        self.assertEqual(i2.to_smtlib(daggify=True), "(- 4)")

        self.assertEqual(b1.to_smtlib(daggify=False), "true")
        self.assertEqual(b2.to_smtlib(daggify=False), "false")

        self.assertEqual(r1.to_smtlib(daggify=False), "(/ 11 2)")
        self.assertEqual(r2.to_smtlib(daggify=False), "5.0")
        self.assertEqual(r3.to_smtlib(daggify=False), "(- (/ 11 2))")

        self.assertEqual(i1.to_smtlib(daggify=False), "4")
        self.assertEqual(i2.to_smtlib(daggify=False), "(- 4)")

    def test_function(self):
        f1_type = FunctionType(REAL, [REAL, REAL])
        f2_type = FunctionType(REAL, [])

        p,q = Symbol("p", REAL), Symbol("q", REAL)
        f1_symbol = Symbol("f1", f1_type)
        f2_symbol = Symbol("f2", f2_type)

        f1 = Function(f1_symbol, [p,q])
        f2 = Function(f2_symbol, [])

        self.assertEqual(f1.to_smtlib(daggify=False), "(f1 p q)")
        self.assertEqual(f2.to_smtlib(daggify=False), "f2")

        self.assertEqual(f1.to_smtlib(daggify=True), "(let ((.def_0 (f1 p q))) .def_0)")
        self.assertEqual(f2.to_smtlib(daggify=True), "f2")

    def test_toreal(self):
        p = Symbol("p", INT)
        rp = ToReal(p)

        self.assertEqual(rp.to_smtlib(daggify=False), "(to_real p)")
        self.assertEqual(rp.to_smtlib(daggify=True), "(let ((.def_0 (to_real p))) .def_0)")

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

    def test_examples(self):
        for s, f, logic in get_str_example_formulae(environment=None):
            str_f = f.serialize()
            self.assertTrue(len(str_f) >= 1, str_f)
            self.assertEqual(str_f, s)

    def test_smart_serialize(self):
        x, y = Symbol("x"), Symbol("y")
        f1 = And(x,y)
        f = Implies(x, f1)
        substitutions = {f1: "f1"}  # Mapping FNode -> String
        res = smart_serialize(f, subs=substitutions)
        self.assertEqual("(x -> f1)", res)

        # If no smarties are provided, the printing is compatible
        # with standard one
        res = smart_serialize(f)
        self.assertIsNotNone(res)
        self.assertEqual(str(f), res)

        fvars = [Symbol("x%d" % i) for i in xrange(5)]
        ex = ExactlyOne(fvars)
        substitutions = {ex: "ExactlyOne(%s)" % ",".join(str(v) for v in fvars)}
        old_str = ex.serialize()
        smart_str = smart_serialize(ex, subs=substitutions)
        self.assertTrue(len(old_str) > len(smart_str))
        self.assertEqual("ExactlyOne(x0,x1,x2,x3,x4)", smart_str)

    def test_stack_recursion(self):
        import sys
        limit = sys.getrecursionlimit()
        f = FreshSymbol()
        p = FreshSymbol()
        for _ in xrange(limit):
            f = Or(p, And(f, p))
        self.assertTrue(f.size() >= limit)
        s = f.serialize()
        self.assertIsNotNone(s)

if __name__ == '__main__':
    main()
