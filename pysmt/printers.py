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
from fractions import Fraction

from pysmt.walkers import TreeWalker
from six.moves import cStringIO


class HRPrinter(TreeWalker):

    def __init__(self, stream):
        TreeWalker.__init__(self)
        self.stream = stream
        return


    def printer(self, f, threshold=None):
        if threshold is not None:
            self.threshold_cnt = threshold
        self.walk(f)
        return

    def walk_threshold(self, formula):
        self.stream.write("...")
        return

    def walk_and(self, formula):
        self.stream.write("(")
        sons = formula.get_sons()
        count = 0
        for s in sons:
            self.walk(s)
            count += 1
            if count != len(sons):
                self.stream.write(" & ")
        self.stream.write(")")
        return


    def walk_or(self, formula):
        self.stream.write("(")
        sons = formula.get_sons()
        count = 0
        for s in sons:
            self.walk(s)
            count += 1
            if count != len(sons):
                self.stream.write(" | ")
        self.stream.write(")")
        return


    def walk_not(self, formula):
        self.stream.write("(! ")
        self.walk(formula.arg(0))
        self.stream.write(")")
        return


    def walk_symbol(self, formula):
        self.stream.write(formula.symbol_name())
        return


    def walk_plus(self, formula):
        self.stream.write("(")
        sons = formula.get_sons()
        count = 0
        for s in sons:
            self.walk(s)
            count += 1
            if count != len(sons):
                self.stream.write(" + ")
        self.stream.write(")")
        return


    def walk_times(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" * ")
        self.walk(formula.arg(1))
        self.stream.write(")")
        return

    def walk_iff(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" <-> ")
        self.walk(formula.arg(1))
        self.stream.write(")")
        return

    def walk_implies(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" -> ")
        self.walk(formula.arg(1))
        self.stream.write(")")
        return

    def walk_minus(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" - ")
        self.walk(formula.arg(1))
        self.stream.write(")")
        return


    def walk_equals(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" = ")
        self.walk(formula.arg(1))
        self.stream.write(")")
        return


    def walk_le(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" <= ")
        self.walk(formula.arg(1))
        self.stream.write(")")
        return


    def walk_lt(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" < ")
        self.walk(formula.arg(1))
        self.stream.write(")")
        return


    def walk_function(self, formula):
        self.walk(formula.function_name())
        self.stream.write("(")
        count = 0
        for p in formula.args():
            self.walk(p)
            count += 1
            if count != len(formula.args()):
                self.stream.write(", ")
        self.stream.write(")")
        return


    def walk_real_constant(self, formula):
        assert type(formula.constant_value()) == Fraction, \
            "The type was " + str(type(formula.constant_value()))
        self.stream.write(str(formula.constant_value()))
        if formula.constant_value().denominator == 1:
            self.stream.write(".0")
        return

    def walk_int_constant(self, formula):
        assert (type(formula.constant_value()) == int or
                type(formula.constant_value()) == long) , \
            "The type was " + str(type(formula.constant_value()))
        self.stream.write(str(formula.constant_value()))
        return


    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.stream.write("True")
        else:
            self.stream.write("False")
        return

    def walk_bv_constant(self, formula):
        # This is the simplest SMT-LIB way of printing the value of a BV
        # self.stream.write("(_ bv%d %d)" % (formula.bv_width(),
        #                                    formula.constant_value()))
        self.stream.write("%d_%d" % (formula.constant_value(),
                                     formula.bv_width()))
        return

    def walk_bv_xor(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" xor ")
        self.walk(formula.arg(1))
        self.stream.write(")")

    def walk_bv_concat(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write("::")
        self.walk(formula.arg(1))
        self.stream.write(")")

    def walk_bv_extract(self, formula):
        self.walk(formula.arg(0))
        self.stream.write("[%d:%d]" % (formula.bv_extract_start(),
                                       formula.bv_extract_end()))

    def walk_bv_neg(self, formula):
        self.stream.write("(- ")
        self.walk(formula.arg(0))
        self.stream.write(")")

    def walk_bv_udiv(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" / ")
        self.walk(formula.arg(1))
        self.stream.write(")")

    def walk_bv_urem(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" % ")
        self.walk(formula.arg(1))
        self.stream.write(")")

    def walk_bv_lshl(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" << ")
        self.walk(formula.arg(1))
        self.stream.write(")")

    def walk_bv_lshr(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" >> ")
        self.walk(formula.arg(1))
        self.stream.write(")")

    def walk_bv_ror(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" ROR ")
        self.stream.write("%d)" % formula.bv_rotation_step())

    def walk_bv_rol(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" ROL ")
        self.stream.write("%d)" % formula.bv_rotation_step())

    def walk_bv_zext(self, formula):
        self.stream.write("Zext(")
        self.walk(formula.arg(0))
        self.stream.write(", %d)" % formula.bv_extend_step())

    def walk_bv_sext(self, formula):
        self.stream.write("Sext(")
        self.walk(formula.arg(0))
        self.stream.write(", %d)" % formula.bv_extend_step())

    # Recycling functions form LIRA
    walk_bv_not = walk_not
    walk_bv_and = walk_and
    walk_bv_or = walk_or
    walk_bv_ult = walk_lt
    walk_bv_ule = walk_le
    walk_bv_add = walk_plus
    walk_bv_mul = walk_times



    def walk_ite(self, formula):
        self.stream.write("(")
        self.walk(formula.arg(0))
        self.stream.write(" ? ")
        self.walk(formula.arg(1))
        self.stream.write(" : ")
        self.walk(formula.arg(2))
        self.stream.write(")")
        return


    def walk_forall(self, formula):
        if len(formula.quantifier_vars()) > 0:
            self.stream.write("(forall ")

            count = 0
            for s in formula.quantifier_vars():
                self.walk(s)
                count += 1
                if count != len(formula.quantifier_vars()):
                    self.stream.write(", ")

            self.stream.write(" . ")

            self.walk(formula.arg(0))

            self.stream.write(")")
        else:
            self.walk(formula.arg(0))
        return


    def walk_exists(self, formula):
        if len(formula.quantifier_vars()) > 0:
            self.stream.write("(exists ")

            count = 0
            for s in formula.quantifier_vars():
                self.walk(s)
                count += 1
                if count != len(formula.quantifier_vars()):
                    self.stream.write(", ")

            self.stream.write(" . ")

            self.walk(formula.arg(0))

            self.stream.write(")")
        else:
            self.walk(formula.arg(0))
        return


    def walk_toreal(self, formula):
        self.stream.write("ToReal(")
        self.walk(formula.arg(0))
        self.stream.write(")")
        return

class HRSerializer(object):

    def __init__(self, environment=None):
        self.environment = environment

    def serialize(self, formula, printer=None, threshold=None):
        buf = cStringIO()

        p = None
        if printer is None:
            p = HRPrinter(buf)
        else:
            p = printer(buf)

        p.printer(formula, threshold)
        res = buf.getvalue()
        buf.close()
        return res
