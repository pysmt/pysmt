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
from functools import partial

from six.moves import xrange

import pysmt.operators as op
from pysmt.environment import get_env
from pysmt.walkers import TreeWalker, DagWalker
from pysmt.utils import quote


class SmtPrinter(TreeWalker):

    def __init__(self, stream):
        TreeWalker.__init__(self)
        self.stream = stream
        self.write = self.stream.write
        self.mgr = get_env().formula_manager


        self.set_function(partial(self._walk_nary, "and"), op.AND)
        self.set_function(partial(self._walk_nary, "or"), op.OR)
        self.set_function(partial(self._walk_nary, "not"), op.NOT)
        self.set_function(partial(self._walk_nary, "=>"), op.IMPLIES)
        self.set_function(partial(self._walk_nary, "="), op.IFF)
        self.set_function(partial(self._walk_nary, "+"), op.PLUS)
        self.set_function(partial(self._walk_nary, "-"), op.MINUS)
        self.set_function(partial(self._walk_nary, "*"), op.TIMES)
        self.set_function(partial(self._walk_nary, "="), op.EQUALS)
        self.set_function(partial(self._walk_nary, "<="), op.LE)
        self.set_function(partial(self._walk_nary, "<"), op.LT)
        self.set_function(partial(self._walk_nary, "ite"), op.ITE)
        self.set_function(partial(self._walk_nary, "to_real"), op.TOREAL)

        self.set_function(partial(self._walk_nary, "bvand"), op.BV_AND)
        self.set_function(partial(self._walk_nary, "bvor"), op.BV_OR)
        self.set_function(partial(self._walk_nary, "bvnot"), op.BV_NOT)
        self.set_function(partial(self._walk_nary, "bvxor"), op.BV_XOR)
        self.set_function(partial(self._walk_nary, "bvadd"), op.BV_ADD)
        self.set_function(partial(self._walk_nary, "bvsub"), op.BV_SUB)
        self.set_function(partial(self._walk_nary, "bvneg"), op.BV_NEG)
        self.set_function(partial(self._walk_nary, "bvmul"), op.BV_MUL)
        self.set_function(partial(self._walk_nary, "bvudiv"), op.BV_UDIV)
        self.set_function(partial(self._walk_nary, "bvurem"), op.BV_UREM)
        self.set_function(partial(self._walk_nary, "bvshl"), op.BV_LSHL)
        self.set_function(partial(self._walk_nary, "bvlshr"), op.BV_LSHR)
        self.set_function(partial(self._walk_nary, "bvult"), op.BV_ULT)
        self.set_function(partial(self._walk_nary, "bvule"), op.BV_ULE)
        self.set_function(partial(self._walk_nary, "bvslt"), op.BV_SLT)
        self.set_function(partial(self._walk_nary, "bvsle"), op.BV_SLE)
        self.set_function(partial(self._walk_nary, "concat"), op.BV_CONCAT)
        self.set_function(partial(self._walk_nary, "bvcomp"), op.BV_COMP)
        self.set_function(partial(self._walk_nary, "bvashr"), op.BV_ASHR)
        self.set_function(partial(self._walk_nary, "bvsdiv"), op.BV_SDIV)
        self.set_function(partial(self._walk_nary, "bvsrem"), op.BV_SREM)
        self.set_function(self.walk_bv_extract, op.BV_EXTRACT)
        self.set_function(self.walk_bv_rotate, op.BV_ROR)
        self.set_function(self.walk_bv_rotate, op.BV_ROL)
        self.set_function(self.walk_bv_extend, op.BV_ZEXT)
        self.set_function(self.walk_bv_extend, op.BV_SEXT)

        self.set_function(partial(self._walk_nary, "select"), op.ARRAY_SELECT)
        self.set_function(partial(self._walk_nary, "store"), op.ARRAY_STORE)

    def printer(self, f):
        self.walk(f)

    def walk_threshold(self, formula):
        """This is a complete printer"""
        raise NotImplementedError

    def _walk_nary(self, operator, formula):
        self.write("(%s" % operator)
        for s in formula.args():
            self.write(" ")
            self.walk(s)
        self.write(")")


    def walk_symbol(self, formula):
        self.write(quote(formula.symbol_name()))

    def walk_function(self, formula):
        return self._walk_nary(formula.function_name(), formula)

    def walk_int_constant(self, formula):
        if formula.constant_value() < 0:
            self.write("(- " + str(-formula.constant_value()) + ")")
        else:
            self.write(str(formula.constant_value()))

    def walk_real_constant(self, formula):
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template = "%s"

        (n,d) = abs(formula.constant_value().numerator), \
                    formula.constant_value().denominator
        if d != 1:
            res = template % ( "(/ " + str(n) + " " + str(d) + ")" )
        else:
            res = template % (str(n) + ".0")

        self.write(res)

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("true")
        else:
            self.write("false")

    def walk_bv_constant(self, formula):
        self.write("#b" + formula.bv_bin_str())

    def walk_forall(self, formula):
        self._walk_quantifier("forall", formula)

    def walk_exists(self, formula):
        self._walk_quantifier("exists", formula)

    def _walk_quantifier(self, operator, formula):
        assert len(formula.quantifier_vars()) > 0
        self.write("(%s (" % operator)

        for s in formula.quantifier_vars():
            self.write("(")
            self.walk(s)
            self.write(" %s)" % s.symbol_type().as_smtlib(False))

        self.write(") ")
        self.walk(formula.arg(0))
        self.write(")")

    def walk_bv_extract(self, formula):
        self.write("((_ extract %d %d) " % (formula.bv_extract_end(),
                                            formula.bv_extract_start()))
        self.walk(formula.arg(0))
        self.write(")")

    def walk_bv_rotate(self, formula):
        if formula.is_bv_ror():
            rotate_type = "rotate_right"
        else:
            assert formula.is_bv_rol()
            rotate_type = "rotate_left"
        self.write("((_ %s %d ) " % (rotate_type,
                                     formula.bv_rotation_step()))
        self.walk(formula.arg(0))
        self.write(")")

    def walk_bv_extend(self, formula):
        if formula.is_bv_zext():
            extend_type = "zero_extend"
        else:
            assert formula.is_bv_sext()
            extend_type = "sign_extend"
        self.write("((_ %s %d ) " % (extend_type,
                                     formula.bv_extend_step()))
        self.walk(formula.arg(0))
        self.write(")")

    def walk_array_value(self, formula):
        assign = formula.array_value_assigned_values_map()
        for _ in xrange(len(assign)):
            self.write("(store ")

        self.write("((as const %s) " % formula.get_type().as_smtlib(False))
        self.walk(formula.array_value_default())
        self.write(")")

        for k in sorted(assign):
            self.write(" ")
            self.walk(k)
            self.write(" ")
            self.walk(assign[k])
            self.write(")")

class SmtDagPrinter(DagWalker):

    def __init__(self, stream, template=".def_%d"):
        DagWalker.__init__(self, invalidate_memoization=True)
        self.stream = stream
        self.write = self.stream.write
        self.openings = 0
        self.name_seed = 0
        self.template = template
        self.names = None
        self.mgr = get_env().formula_manager

        self.set_function(partial(self._walk_nary, "and"), op.AND)
        self.set_function(partial(self._walk_nary, "or"), op.OR)
        self.set_function(partial(self._walk_nary, "not"), op.NOT)
        self.set_function(partial(self._walk_nary, "=>"), op.IMPLIES)
        self.set_function(partial(self._walk_nary, "="), op.IFF)
        self.set_function(partial(self._walk_nary, "+"), op.PLUS)
        self.set_function(partial(self._walk_nary, "-"), op.MINUS)
        self.set_function(partial(self._walk_nary, "*"), op.TIMES)
        self.set_function(partial(self._walk_nary, "="), op.EQUALS)
        self.set_function(partial(self._walk_nary, "<="), op.LE)
        self.set_function(partial(self._walk_nary, "<"), op.LT)
        self.set_function(partial(self._walk_nary, "ite"), op.ITE)
        self.set_function(partial(self._walk_nary, "to_real"), op.TOREAL)

        self.set_function(partial(self._walk_nary, "bvand"), op.BV_AND)
        self.set_function(partial(self._walk_nary, "bvor"), op.BV_OR)
        self.set_function(partial(self._walk_nary, "bvnot"), op.BV_NOT)
        self.set_function(partial(self._walk_nary, "bvxor"), op.BV_XOR)
        self.set_function(partial(self._walk_nary, "bvadd"), op.BV_ADD)
        self.set_function(partial(self._walk_nary, "bvsub"), op.BV_SUB)
        self.set_function(partial(self._walk_nary, "bvneg"), op.BV_NEG)
        self.set_function(partial(self._walk_nary, "bvmul"), op.BV_MUL)
        self.set_function(partial(self._walk_nary, "bvudiv"), op.BV_UDIV)
        self.set_function(partial(self._walk_nary, "bvurem"), op.BV_UREM)
        self.set_function(partial(self._walk_nary, "bvshl"), op.BV_LSHL)
        self.set_function(partial(self._walk_nary, "bvlshr"), op.BV_LSHR)
        self.set_function(partial(self._walk_nary, "bvult"), op.BV_ULT)
        self.set_function(partial(self._walk_nary, "bvule"), op.BV_ULE)
        self.set_function(partial(self._walk_nary, "bvslt"), op.BV_SLT)
        self.set_function(partial(self._walk_nary, "bvsle"), op.BV_SLE)
        self.set_function(partial(self._walk_nary, "concat"), op.BV_CONCAT)
        self.set_function(partial(self._walk_nary, "bvcomp"), op.BV_COMP)
        self.set_function(partial(self._walk_nary, "bvashr"), op.BV_ASHR)
        self.set_function(partial(self._walk_nary, "bvsdiv"), op.BV_SDIV)
        self.set_function(partial(self._walk_nary, "bvsrem"), op.BV_SREM)
        self.set_function(self.walk_bv_extract, op.BV_EXTRACT)
        self.set_function(self.walk_bv_rotate, op.BV_ROR)
        self.set_function(self.walk_bv_rotate, op.BV_ROL)
        self.set_function(self.walk_bv_extend, op.BV_SEXT)
        self.set_function(self.walk_bv_extend, op.BV_ZEXT)

        self.set_function(partial(self._walk_nary, "select"), op.ARRAY_SELECT)
        self.set_function(partial(self._walk_nary, "store"), op.ARRAY_STORE)


    def _push_with_children_to_stack(self, formula, **kwargs):
        """Add children to the stack."""

        # Deal with quantifiers
        if formula.is_quantifier():
            # 1. We invoke the relevant function (walk_exists or
            #    walk_forall) to print the formula
            fun = self.functions[formula.node_type()]
            res = fun(formula, args=None, **kwargs)

            # 2. We memoize the result
            key = self._get_key(formula, **kwargs)
            self.memoization[key] = res
        else:
            DagWalker._push_with_children_to_stack(self,
                                                   formula,
                                                   **kwargs)

    def printer(self, f):
        self.openings = 0
        self.name_seed = 0
        self.names = set(quote(x.symbol_name()) for x in f.get_free_variables())

        key = self.walk(f)
        self.write(key)
        self.write(")" * self.openings)


    def _new_symbol(self):
        while (self.template % self.name_seed) in self.names:
            self.name_seed += 1
        res = (self.template % self.name_seed)
        self.name_seed += 1
        return res

    def _walk_nary(self, operator, formula, args):
        assert formula is not None
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s (%s" % (sym, operator))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_symbol(self, formula, **kwargs):
        return quote(formula.symbol_name())

    def walk_function(self, formula, args, **kwargs):
        return self._walk_nary(formula.function_name(), formula, args)

    def walk_int_constant(self, formula, **kwargs):
        if formula.constant_value() < 0:
            return "(- " + str(-formula.constant_value()) + ")"
        else:
            return str(formula.constant_value())

    def walk_real_constant(self, formula, **kwargs):
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template = "%s"

        (n,d) = abs(formula.constant_value().numerator), \
                    formula.constant_value().denominator
        if d != 1:
            return template % ( "(/ " + str(n) + " " + str(d) + ")" )
        else:
            return template % (str(n) + ".0")

    def walk_bv_constant(self, formula, **kwargs):
        short_res = str(bin(formula.constant_value()))[2:]
        if formula.constant_value() >= 0:
            filler = "0"
        else:
            raise NotImplementedError
        res = short_res.rjust(formula.bv_width(), filler)
        return "#b" + res


    def walk_bool_constant(self, formula, **kwargs):
        if formula.constant_value():
            return "true"
        else:
            return "false"

    def walk_forall(self, formula, args, **kwargs):
        return self._walk_quantifier("forall", formula, args)

    def walk_exists(self, formula, args, **kwargs):
        return self._walk_quantifier("exists", formula, args)

    def _walk_quantifier(self, operator, formula, args):
        assert args is None
        assert len(formula.quantifier_vars()) > 0
        sym = self._new_symbol()
        self.openings += 1

        self.write("(let ((%s (%s (" % (sym, operator))

        for s in formula.quantifier_vars():
            self.write("(")
            self.write(quote(s.symbol_name()))
            self.write(" %s)" % s.symbol_type().as_smtlib(False))
        self.write(") ")

        subprinter = SmtDagPrinter(self.stream)
        subprinter.printer(formula.arg(0))

        self.write(")))")
        return sym

    def walk_bv_extract(self, formula, args, **kwargs):
        assert formula is not None
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s ((_ extract %d %d)" % (sym,
                                                     formula.bv_extract_end(),
                                                     formula.bv_extract_start()))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_bv_extend(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_bv_zext():
            extend_type = "zero_extend"
        else:
            assert formula.is_bv_sext()
            extend_type = "sign_extend"

        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s ((_ %s %d)" % (sym, extend_type,
                                                formula.bv_extend_step()))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_bv_rotate(self, formula, args, **kwargs):
        #pylint: disable=unused-argument
        if formula.is_bv_ror():
            rotate_type = "rotate_right"
        else:
            assert formula.is_bv_rol()
            rotate_type = "rotate_left"

        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s ((_ %s %d)" % (sym, rotate_type,
                                             formula.bv_rotation_step()))
        for s in args:
            self.write(" ")
            self.write(s)
        self.write("))) ")
        return sym

    def walk_array_value(self, formula, args, **kwargs):
        sym = self._new_symbol()
        self.openings += 1
        self.write("(let ((%s " % sym)

        for _ in xrange((len(args) - 1) // 2):
            self.write("(store ")

        self.write("((as const %s) " % formula.get_type().as_smtlib(False))
        self.write(args[0])
        self.write(")")

        for i, k in enumerate(args[1::2]):
            self.write(" ")
            self.write(k)
            self.write(" ")
            self.write(args[2*i + 2])
            self.write(")")
        self.write("))")
        return sym
