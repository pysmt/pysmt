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
from pysmt.shortcuts import Times, Minus, Equals, LE, LT, ToReal
from pysmt.typing import REAL, INT, FunctionType
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.printers import smart_serialize
from pysmt.test import TestCase, main
from pysmt.test.examples import get_example_formulae


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
        self.assertEqual(f2_string, "f2")

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

    def test_examples(self):
        for i, (f, _, _, _) in enumerate(get_example_formulae()):
            self.assertTrue(len(str(f)) >= 1, str(f))
            self.assertEqual(str(f), SERIALIZED_EXAMPLES[i])

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


SERIALIZED_EXAMPLES = [
    """(x & y)""",
    """(x <-> y)""",
    """((x | y) & (! (x | y)))""",
    """(x & (! y))""",
    """(False -> True)""",
    """((q < p) & (x -> y))""",
    """(((p + q) = 5) & (q < p))""",
    """((q <= p) | (p <= q))""",
    """(! (p < (q * 2)))""",
    """(p < (p - (5 - 2)))""",
    """((x ? 7 : ((p + -1) * 3)) = q)""",
    """(p < (q + 1))""",
    """((s < r) & (x -> y))""",
    """(((r + s) = 28/5) & (s < r))""",
    """((s <= r) | (r <= s))""",
    """(! ((r * 2.0) < (s * 2.0)))""",
    """(! (r < (r - (5.0 - 2.0))))""",
    """((x ? 7.0 : ((s + -1.0) * 3.0)) = r)""",
    """(bf(x) <-> bg(x))""",
    """(rf(5.0, rg(r)) = 0.0)""",
    """((rg(r) = (5.0 + 2.0)) <-> (rg(r) = 7.0))""",
    """((r = (s + 1.0)) & (rg(s) = 5.0) & (rg((r - 1.0)) = 7.0))""",
    """((1_32 & 0_32) = 0_32)""",
    """((! 2_3) = 5_3)""",
    """((7_3 xor 0_3) = 0_3)""",
    """((bv1::bv1) u< 0_16)""",
    """(1_32[0:7] = 1_8)""",
    """(0_8 u< (((bv1 + 1_8) * 5_8) u/ 5_8))""",
    """(0_16 u<= bv2)""",
    """(0_16 s<= bv2)""",
    """((0_32 u< (5_32 u% 2_32)) & ((5_32 u% 2_32) u<= 1_32))""",
    """((((1_32 + (- ...)) << 1_32) >> 1_32) = 1_32)""",
    """((1_32 - 1_32) = 0_32)""",
    """(((1_32 ROL 1) ROR 1) = 1_32)""",
    """((0_5 ZEXT 11) = (0_1 SEXT 15))""",
    """((bv2 - bv2) = 0_16)""",
    """((bv2 - bv2)[0:7] = bv1)""",
    """((bv2[0:7] bvcomp bv1) = 1_1)""",
    """((bv2 bvcomp bv2) = 0_1)""",
    """(bv2 s< bv2)""",
    """(bv2 s< 0_16)""",
    """((bv2 s< 0_16) | (0_16 s<= bv2))""",
    """(bv2 u< bv2)""",
    """(bv2 u< 0_16)""",
    """((bv2 | 0_16) = bv2)""",
    """((bv2 & 0_16) = 0_16)""",
    """((0_16 s< bv2) & ((bv2 s/ 65535_16) s< 0_16))""",
    """((0_16 s< bv2) & ((bv2 s% 1_16) s< 0_16))""",
    """((bv2 u% 1_16) = 0_16)""",
    """((bv2 s% 1_16) = 0_16)""",
    """((bv2 s% (- 1_16)) = 0_16)""",
    """((bv2 a>> 0_16) = bv2)""",
    """((0_16 s<= bv2) & ((bv2 a>> 1_16) = (bv2 >> 1_16)))""",
    """(forall y . (x -> y))""",
    """(forall p, q . ((p + q) = 0))""",
    """(forall r, s . (((0.0 < r) & (0.0 < s)) -> ((r - s) < r)))""",
    """(exists x, y . (x -> y))""",
    """(exists p, q . ((p + q) = 0))""",
    """(exists r . (forall s . (r < (r - s))))""",
    """(forall r . (exists s . (r < (r - s))))""",
    """(x & (forall r . ((r + s) = 5.0)))""",
    """(exists x . ((x <-> (5.0 < s)) & (s < 3.0)))""",
    """((p < ih(r, q)) & (x -> y))""",
    """(((p - 3) = q) -> ((p < ih(r, (... + ...))) | (ih(r, p) <= p)))""",
    """(((ToReal((... - ...)) = r) & (ToReal(q) = r)) -> ((p < ih(ToReal(...), (... + ...))) | (ih(r, p) <= p)))""",
    """(! (((ToReal(...) = r) & (ToReal(...) = r)) -> ((p < ...(..., ...)) | (...(..., ...) <= p))))""",
    """("Did you know that any string works? #yolo" & "10" & "|#somesolverskeepthe||" & " ")""",
    """((q = 0) -> (aii[0 := 0] = aii[0 := q]))""",
    """(aii[0 := 0][0] = 0)""",
    """((Array{Int, Int}(0)[1 := 1] = aii) & (aii[1] = 0))""",
    """((a_arb_aii = Array{Array{Real, BV{8}}, Array{Int, Int}}(Array{Int, Int}(7))) -> (a_arb_aii[arb][42] = 7))""",
    """(abb[bv1 := y_][bv1 := z_] = abb[bv1 := z_])"""
]


if __name__ == '__main__':
    main()
