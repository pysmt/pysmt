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

from pysmt.walkers import TreeWalker, DagWalker
import pysmt.operators as op

class SmtPrinter(TreeWalker):

    def __init__(self, stream):
        TreeWalker.__init__(self)
        self.stream = stream
        self.write = self.stream.write

        self.functions[op.FORALL] = self.walk_forall
        self.functions[op.EXISTS] = self.walk_exists
        self.functions[op.SYMBOL] = self.walk_symbol
        self.functions[op.FUNCTION] = self.walk_function
        self.functions[op.REAL_CONSTANT] = self.walk_real_constant
        self.functions[op.BOOL_CONSTANT] = self.walk_bool_constant
        self.functions[op.INT_CONSTANT] = self.walk_int_constant

        self.functions[op.AND] = partial(self._walk_nary, "and")
        self.functions[op.OR] = partial(self._walk_nary, "or")
        self.functions[op.NOT] = partial(self._walk_nary, "not")
        self.functions[op.IMPLIES] = partial(self._walk_nary, "=>")
        self.functions[op.IFF] = partial(self._walk_nary, "=")
        self.functions[op.PLUS]   = partial(self._walk_nary, "+")
        self.functions[op.MINUS]  = partial(self._walk_nary, "-")
        self.functions[op.TIMES]  = partial(self._walk_nary, "*")
        self.functions[op.EQUALS] = partial(self._walk_nary, "=")
        self.functions[op.LE]     = partial(self._walk_nary, "<=")
        self.functions[op.LT]     = partial(self._walk_nary, "<")
        self.functions[op.ITE]    = partial(self._walk_nary, "ite")
        self.functions[op.TOREAL] = partial(self._walk_nary, "to_real")


    def printer(self, f):
        self.walk(f)

    def walk_threshold(self, formula):
        """This is a complete printer"""
        raise NotImplementedError

    def _walk_nary(self, operator, formula):
        self.write("(%s" % operator)
        for s in formula.get_sons():
            self.write(" ")
            self.walk(s)
        self.write(")")

    def walk_symbol(self, formula):
        self.write(formula.symbol_name())

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
            res = template % str(n)

        self.write(res)

    def walk_bool_constant(self, formula):
        if formula.constant_value():
            self.write("true")
        else:
            self.write("false")


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


class SmtDagPrinter(DagWalker):

    def __init__(self, stream, template=".def_%d"):
        DagWalker.__init__(self, invalidate_memoization=True)
        self.stream = stream
        self.write = self.stream.write
        self.openings = 0
        self.name_seed = 0
        self.template = template
        self.names = None

        self.functions[op.FORALL] = self.walk_forall
        self.functions[op.EXISTS] = self.walk_exists
        self.functions[op.SYMBOL] = self.walk_symbol
        self.functions[op.FUNCTION] = self.walk_function
        self.functions[op.REAL_CONSTANT] = self.walk_real_constant
        self.functions[op.BOOL_CONSTANT] = self.walk_bool_constant
        self.functions[op.INT_CONSTANT] = self.walk_int_constant

        self.functions[op.AND] = partial(self._walk_nary, "and")
        self.functions[op.OR] = partial(self._walk_nary, "or")
        self.functions[op.NOT] = partial(self._walk_nary, "not")
        self.functions[op.IMPLIES] = partial(self._walk_nary, "=>")
        self.functions[op.IFF] = partial(self._walk_nary, "=")
        self.functions[op.PLUS]   = partial(self._walk_nary, "+")
        self.functions[op.MINUS]  = partial(self._walk_nary, "-")
        self.functions[op.TIMES]  = partial(self._walk_nary, "*")
        self.functions[op.EQUALS] = partial(self._walk_nary, "=")
        self.functions[op.LE]     = partial(self._walk_nary, "<=")
        self.functions[op.LT]     = partial(self._walk_nary, "<")
        self.functions[op.ITE]    = partial(self._walk_nary, "ite")
        self.functions[op.TOREAL] = partial(self._walk_nary, "to_real")


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
        self.names = set(x.symbol_name() for x in f.get_dependencies())

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

    def walk_symbol(self, formula, args, **kwargs):
        return formula.symbol_name()

    def walk_function(self, formula, args, **kwargs):
        return self._walk_nary(formula.function_name(), formula, args)

    def walk_int_constant(self, formula, args, **kwargs):
        if formula.constant_value() < 0:
            return "(- " + str(-formula.constant_value()) + ")"
        else:
            return str(formula.constant_value())

    def walk_real_constant(self, formula, args, **kwargs):
        if formula.constant_value() < 0:
            template = "(- %s)"
        else:
            template = "%s"

        (n,d) = abs(formula.constant_value().numerator), \
                    formula.constant_value().denominator
        if d != 1:
            return template % ( "(/ " + str(n) + " " + str(d) + ")" )
        else:
            return template % str(n)

    def walk_bool_constant(self, formula, args, **kwargs):
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
            self.write(s.symbol_name())
            self.write(" %s)" % s.symbol_type().as_smtlib(False))
        self.write(") ")

        subprinter = SmtDagPrinter(self.stream)
        subprinter.printer(formula.arg(0))

        self.write(")))")
        return sym
