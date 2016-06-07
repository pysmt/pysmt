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
from six import iteritems
from pysmt.utils import quote

class HRPrinter(TreeWalker):
    """Performs serialization of a formula in a human-readable way.

    E.g., Implies(And(Symbol(x), Symbol(y)), Symbol(z))  ~>   '(x * y) -> z'
    """

    def __init__(self, stream, env=None):
        TreeWalker.__init__(self, env=env)
        self.stream = stream
        self.write = self.stream.write

    def printer(self, f, threshold=None):
        """Performs the serialization of 'f'.

        Thresholding can be used to define how deep in the formula to
        go. After reaching the thresholded value, "..." will be
        printed instead. This is mainly used for debugging.
        """
        if threshold is not None:
            self.threshold_cnt = threshold
        self.walk(f)

    def walk_threshold(self, formula):
        self.write("...")

    def walk_nary(self, op_symbol, formula):
        self.write("(")
        args = formula.args()
        for s in args[:-1]:
            self.walk(s)
            self.write(op_symbol)
        self.walk(args[-1])
        self.write(")")

    def walk_binary(self, op_symbol, formula):
        self.write("(")
        self.walk(formula.arg(0))
        self.write(op_symbol)
        self.walk(formula.arg(1))
        self.write(")")

    def walk_quantifier(self, op_symbol, var_sep, sep, formula):
        if len(formula.quantifier_vars()) > 0:
            self.write("(")
            self.write(op_symbol)
            for s in formula.quantifier_vars()[:-1]:
                self.walk(s)
                self.write(var_sep)
            self.walk(formula.quantifier_vars()[-1])
            self.write(sep)
            self.walk(formula.arg(0))
            self.write(")")
        else:
            self.walk(formula.arg(0))


    def walk_and(self, formula):
        self.walk_nary(" & ", formula)

    def walk_or(self, formula):
        self.walk_nary(" | ", formula)

    def walk_plus(self, formula):
        self.walk_nary(" + ", formula)

    def walk_not(self, formula):
        self.write("(! ")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_symbol(self, formula):
        self.write(quote(formula.symbol_name(), style='"'))

    def walk_times(self, formula):
        self.walk_binary(" * ", formula)

    def walk_iff(self, formula):
        self.walk_binary(" <-> ", formula)

    def walk_implies(self, formula):
        self.walk_binary(" -> ", formula)

    def walk_minus(self, formula):
        self.walk_binary(" - ", formula)

    def walk_equals(self, formula):
        self.walk_binary(" = ", formula)

    def walk_le(self, formula):
        self.walk_binary(" <= ", formula)

    def walk_lt(self, formula):
        self.walk_binary(" < ", formula)

    def walk_function(self, formula):
        self.walk(formula.function_name())
        self.write("(")
        for p in formula.args()[:-1]:
            self.walk(p)
            self.write(", ")
        self.walk(formula.args()[-1])
        self.write(")")

    def walk_real_constant(self, formula):
        assert type(formula.constant_value()) == Fraction, \
            "The type was " + str(type(formula.constant_value()))
        self.write(str(formula.constant_value()))
        if formula.constant_value().denominator == 1:
            self.write(".0")

    def walk_int_constant(self, formula):
        assert (type(formula.constant_value()) == int or
                type(formula.constant_value()) == long) , \
            "The type was " + str(type(formula.constant_value()))
        self.write(str(formula.constant_value()))

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("True")
        else:
            self.write("False")

    def walk_bv_constant(self, formula):
        # This is the simplest SMT-LIB way of printing the value of a BV
        # self.write("(_ bv%d %d)" % (formula.bv_width(),
        #                             formula.constant_value()))
        self.write("%d_%d" % (formula.constant_value(),
                              formula.bv_width()))

    def walk_bv_xor(self, formula):
        self.walk_binary(" xor ", formula)

    def walk_bv_concat(self, formula):
        self.walk_binary("::", formula)

    def walk_bv_extract(self, formula):
        self.walk(formula.arg(0))
        self.write("[%d:%d]" % (formula.bv_extract_start(),
                                       formula.bv_extract_end()))

    def walk_bv_neg(self, formula):
        self.write("(- ")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_bv_udiv(self, formula):
        self.walk_binary(" u/ ", formula)

    def walk_bv_urem(self, formula):
        self.walk_binary(" u% ", formula)

    def walk_bv_sdiv(self, formula):
        self.walk_binary(" s/ ", formula)

    def walk_bv_srem(self, formula):
        self.walk_binary(" s% ", formula)

    def walk_bv_sle(self, formula):
        self.walk_binary(" s<= ", formula)

    def walk_bv_slt(self, formula):
        self.walk_binary(" s< ", formula)

    def walk_bv_ule(self, formula):
        self.walk_binary(" u<= ", formula)

    def walk_bv_ult(self, formula):
        self.walk_binary(" u< ", formula)

    def walk_bv_lshl(self, formula):
        self.walk_binary(" << ", formula)

    def walk_bv_lshr(self, formula):
        self.walk_binary(" >> ", formula)

    def walk_bv_ashr(self, formula):
        self.walk_binary(" a>> ", formula)

    def walk_bv_ror(self, formula):
        self.write("(")
        self.walk(formula.arg(0))
        self.write(" ROR ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_rol(self, formula):
        self.write("(")
        self.walk(formula.arg(0))
        self.write(" ROL ")
        self.write("%d)" % formula.bv_rotation_step())

    def walk_bv_zext(self, formula):
        self.write("(")
        self.walk(formula.arg(0))
        self.write(" ZEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_bv_sext(self, formula):
        self.write("(")
        self.walk(formula.arg(0))
        self.write(" SEXT ")
        self.write("%d)" % formula.bv_extend_step())

    def walk_bv_comp(self, formula):
        self.walk_binary(" bvcomp ", formula)


    # Recycling functions form LIRA
    walk_bv_not = walk_not
    walk_bv_and = walk_and
    walk_bv_or = walk_or
    walk_bv_add = walk_plus
    walk_bv_sub = walk_minus
    walk_bv_mul = walk_times

    def walk_ite(self, formula):
        self.write("(")
        self.walk(formula.arg(0))
        self.write(" ? ")
        self.walk(formula.arg(1))
        self.write(" : ")
        self.walk(formula.arg(2))
        self.write(")")

    def walk_forall(self, formula):
        self.walk_quantifier("forall ", ", ", " . ", formula)

    def walk_exists(self, formula):
        self.walk_quantifier("exists ", ", ", " . ", formula)

    def walk_toreal(self, formula):
        self.write("ToReal(")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_array_select(self, formula):
        self.walk(formula.arg(0))
        self.write("[")
        self.walk(formula.arg(1))
        self.write("]")

    def walk_array_store(self, formula):
        self.walk(formula.arg(0))
        self.write("[")
        self.walk(formula.arg(1))
        self.write(" := ")
        self.walk(formula.arg(2))
        self.write("]")

    def walk_array_value(self, formula):
        self.write(str(self.env.stc.get_type(formula)))
        self.write("(")
        self.walk(formula.array_value_default())
        self.write(")")
        assign = formula.array_value_assigned_values_map()
        for k, v in iteritems(assign):
            self.write("[")
            self.walk(k)
            self.write(" := ")
            self.walk(v)
            self.write("]")


class HRSerializer(object):
    """Return the serialized version of the formula as a string."""

    def __init__(self, environment=None):
        self.environment = environment

    def serialize(self, formula, printer=None, threshold=None):
        """Returns a string with the human-readable version of the formula.

        'printer' is the printer to call to perform the serialization.
        'threshold' is the thresholding value for the printing function.
        """
        buf = cStringIO()
        if printer is None:
            p = HRPrinter(buf)
        else:
            p = printer(buf)

        p.printer(formula, threshold)
        res = buf.getvalue()
        buf.close()
        return res


class SmartPrinter(HRPrinter):
    """Better serialization allowing special printing of subformula.

    The formula is serialized according to the format defined in the
    HRPrinter. However, everytime a formula that is present in
    'subs' is found, this is replaced.

    E.g., subs  = {And(a,b): "ab"}

    Everytime that the subformula And(a,b) is found, "ab" will be
    printed instead of "a & b". This makes it possible to rename big
    subformulae, and provide better human-readable representation.
    """

    def __init__(self, stream, subs=None):
        HRPrinter.__init__(self, stream)
        if subs is None:
            self.subs = {}
        else:
            self.subs = subs

    def printer(self, f, threshold=None):
        oldvalues = (self.threshold_cnt, self.subs)

        if threshold is not None:
            self.threshold_cnt = threshold
        self.walk(f)
        self.threshold_cnt, self.subs = oldvalues

    def walk(self, formula):
        if self.smart_walk(formula):
            return

        if self.threshold_cnt == 0:
            self.walk_threshold(formula)
            return
        if self.threshold_cnt >= 0: self.threshold_cnt -= 1

        try:
            f = self.functions[formula.node_type()]
        except KeyError:
            f = self.walk_error

        f(formula) # Apply the function to the formula

        if self.threshold_cnt >= 0: self.threshold_cnt += 1
        return

    def smart_walk(self, formula):
        if formula not in self.subs:
            return False
        else:
            # Smarties contains a string.
            # In the future, we could allow for arbitrary function calls
            self.write(self.subs[formula])
            return True


def smart_serialize(formula, subs=None, threshold=None):
    """Creates and calls a SmartPrinter to perform smart serialization."""
    buf = cStringIO()
    p = SmartPrinter(buf, subs=subs)
    p.printer(formula, threshold=threshold)
    res = buf.getvalue()
    buf.close()
    return res
