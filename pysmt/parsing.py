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

import re
from fractions import Fraction

from pysmt.shortcuts import get_env


##
## Precedence table (from low priority to high priority):
##
# 10 ## Xor, Implies, Iff
# 20 ## Forall, Exists
# 30 ## Or
# 40 ## And
# 50 ## Not
# 60 ## LE, LT, Equals, GE, GT, BVULE, BVUGE, BVULT, BVUGT, BVSLE, BVSGE, BVSGT
# 70 ## Plus, Minus, BVAdd, BVSub
# 80 ## Times, Div, BVMul, BVUDiv, BVSDiv, BVSRem, BVURem
# 90 ## BVLShl, BVLShr, BVAShr, BVConcat, BVXor, BVRor, BVRol, BVZExt, BVSExt, BVComp
# 100 ## ToReal Uminus BVNeg
# 200 ## ()
# 300 ## []


class HRLexer(object):
    """This class produces a stream of token objects for the Pratt-parser"""

    def __init__(self, env=None):
        if env is None:
            env = get_env()
        self.env = env
        self.mgr = env.formula_manager
        self.get_type = env.stc.get_type

        self.rules = []
        self.rules.append((r"(\s+)", None, False)) # whitespace
        self.rules.append((r"(-?\d+/\d+)", self.real_constant, True)) # fractions
        self.rules.append((r"(-?\d+\.\d+)", self.real_constant, True)) # decimals
        self.rules.append((r"(-?\d+_\d+)", self.bv_constant, True)) # bv
        self.rules.append((r"(-?\d+)", self.int_constant, True)) # integer literals
        self.rules.append((r"(&)", InfixOpAdapter(self.AndOrBVAnd, 40), False)) # conjunction
        self.rules.append((r"(\|)", InfixOpAdapter(self.OrOrBVOr, 30), False)) # disjunction
        self.rules.append((r"(!)", UnaryOpAdapter(self.NotOrBVNot, 50), False)) # negation
        self.rules.append((r"(\()", OpenPar(), False)) # open parenthesis
        self.rules.append((r"(\))", ClosePar(), False)) # closed parenthesis
        self.rules.append((r"(\[)", OpenBrak(), False)) # open parenthesis
        self.rules.append((r"(\])", CloseBrak(), False)) # closed parenthesis
        self.rules.append((r"(<<)", InfixOpAdapter(self.mgr.BVLShl, 90), False)) # iff
        self.rules.append((r"(>>)", InfixOpAdapter(self.mgr.BVLShr, 90), False)) # iff
        self.rules.append((r"(a>>)", InfixOpAdapter(self.mgr.BVAShr, 90), False)) # iff
        self.rules.append((r"(<->)", InfixOpAdapter(self.mgr.Iff, 10), False)) # iff
        self.rules.append((r"(->)", InfixOpAdapter(self.mgr.Implies, 10), False)) # implies
        self.rules.append((r"(u<=)", InfixOpAdapter(self.mgr.BVULE, 60), False)) # bvult
        self.rules.append((r"(u>=)", InfixOpAdapter(self.mgr.BVUGE, 60), False)) # bvult
        self.rules.append((r"(u<)", InfixOpAdapter(self.mgr.BVULT, 60), False)) # bvult
        self.rules.append((r"(u>)", InfixOpAdapter(self.mgr.BVUGT, 60), False)) # bvult
        self.rules.append((r"(s<=)", InfixOpAdapter(self.mgr.BVSLE, 60), False)) # bvslt
        self.rules.append((r"(s>=)", InfixOpAdapter(self.mgr.BVSGE, 60), False)) # bvslt
        self.rules.append((r"(s<)", InfixOpAdapter(self.mgr.BVSLT, 60), False)) # bvslt
        self.rules.append((r"(s>)", InfixOpAdapter(self.mgr.BVSGT, 60), False)) # bvslt
        self.rules.append((r"(>=)", InfixOpAdapter(self.mgr.GE, 60), False)) # ge
        self.rules.append((r"(<=)", InfixOpAdapter(self.mgr.LE, 60), False)) # le
        self.rules.append((r"(>)", InfixOpAdapter(self.mgr.GT, 60), False)) # gt
        self.rules.append((r"(<)", InfixOpAdapter(self.mgr.LT, 60), False)) # lt
        self.rules.append((r"(=)", InfixOpAdapter(self.mgr.Equals, 60), False)) # eq
        self.rules.append((r"(\+)", InfixOpAdapter(self.PlusOrBVAdd, 70), False)) # plus
        self.rules.append((r"(-)", InfixOrUnaryOpAdapter(self.MinusOrBVSub, self.UMinusOrBvNeg, 70, 100), False)) # minus
        self.rules.append((r"(\*)", InfixOpAdapter(self.TimesOrBVMul, 80), False)) # times
        self.rules.append((r"(u/)", InfixOpAdapter(self.mgr.BVUDiv, 80), False)) # div
        self.rules.append((r"(s/)", InfixOpAdapter(self.mgr.BVSDiv, 80), False)) # div
        self.rules.append((r"(/)", InfixOpAdapter(self.mgr.Div, 80), False)) # div
        self.rules.append((r"(s%)", InfixOpAdapter(self.mgr.BVSRem, 80), False)) # div
        self.rules.append((r"(u%)", InfixOpAdapter(self.mgr.BVURem, 80), False)) # div
        self.rules.append((r"(\?)", ExprIf(), False)) # question
        self.rules.append((r"(::)", InfixOpAdapter(self.mgr.BVConcat, 90), False)) # BVXor
        self.rules.append((r"(:)", ExprElse(), False)) # colon
        self.rules.append((r"(False)", Constant(self.mgr.FALSE()) , False)) # False
        self.rules.append((r"(True)", Constant(self.mgr.TRUE()), False)) # True
        self.rules.append((r"(,)", ExprComma(), False)) # comma
        self.rules.append((r"(\.)", ExprDot(), False)) # dot
        self.rules.append((r"(xor)", InfixOpAdapter(self.mgr.BVXor, 10), False)) # BVXor
        self.rules.append((r"(ROR)", InfixOpAdapter(self.BVHack(self.mgr.BVRor), 90), False)) # BVXor
        self.rules.append((r"(ROL)", InfixOpAdapter(self.BVHack(self.mgr.BVRol), 90), False)) # BVXor
        self.rules.append((r"(ZEXT)", InfixOpAdapter(self.BVHack(self.mgr.BVZExt), 90), False)) # BVXor
        self.rules.append((r"(SEXT)", InfixOpAdapter(self.BVHack(self.mgr.BVSExt), 90), False)) # BVXor
        self.rules.append((r"(bvcomp)", InfixOpAdapter(self.mgr.BVComp, 90), False)) # BVXor
        self.rules.append((r"(forall)", Quantifier(self.mgr.ForAll, 20), False)) # BVXor
        self.rules.append((r"(exists)", Quantifier(self.mgr.Exists, 20), False)) # BVXor
        self.rules.append((r"(ToReal)", UnaryOpAdapter(self.mgr.ToReal, 100), False)) # BVXor
        self.rules.append((r"\"(.*?)\"", self.identifier, True)) # quoted identifiers
        self.rules.append((r"([A-Za-z_][A-Za-z0-9_]*)", self.identifier, True)) # identifiers
        self.rules.append((r"(.)", self.lexing_error, True)) # input error

        self.scanner = re.compile("|".join(x for x,_,_ in self.rules),
                                  re.DOTALL | re.VERBOSE)
        self.eoi = EndOfInput()

    def real_constant(self, read):
        return Constant(self.mgr.Real(Fraction(read)))

    def bv_constant(self, read):
        v, w = read.split("_")
        return Constant(self.mgr.BV(int(v), width=int(w)))

    def int_constant(self, read):
        return Constant(self.mgr.Int(int(read)))

    def identifier(self, read):
        return Identifier(read)

    def lexing_error(self, read):
        raise SyntaxError("Unexpected input: %s" % read)

    def tokenize(self, data):
        """The token generator for the given string"""
        for match in re.finditer(self.scanner, data):
            for idx, capture in enumerate(match.groups()):
                if capture is not None:
                    _, rule, fun = self.rules[idx]
                    if rule is not None:
                        if fun:
                            yield rule(capture)
                        else:
                            yield rule
                    break
        yield self.eoi

    def UMinusOrBvNeg(self, x):
        ty = self.get_type(x)
        if ty.is_int_type():
            return self.mgr.Times(self.mgr.Int(-1), x)
        elif ty.is_real_type():
            return self.mgr.Times(self.mgr.Real(-1), x)
        else:
            return self.mgr.BVNeg(x)

    def AndOrBVAnd(self, l, r):
        if self.get_type(l).is_bool_type():
            return self.mgr.And(l, r)
        else:
            return self.mgr.BVAnd(l, r)

    def OrOrBVOr(self, l, r):
        if self.get_type(l).is_bool_type():
            return self.mgr.Or(l, r)
        else:
            return self.mgr.BVOr(l, r)

    def NotOrBVNot(self, x):
        if self.get_type(x).is_bool_type():
            return self.mgr.Not(x)
        else:
            return self.mgr.BVNot(x)

    def PlusOrBVAdd(self, l, r):
        if self.get_type(l).is_bv_type():
            return self.mgr.BVAdd(l, r)
        else:
            return self.mgr.Plus(l, r)

    def MinusOrBVSub(self, l, r):
        if self.get_type(l).is_bv_type():
            return self.mgr.BVSub(l, r)
        else:
            return self.mgr.Minus(l, r)

    def TimesOrBVMul(self, l, r):
        if self.get_type(l).is_bv_type():
            return self.mgr.BVMul(l, r)
        else:
            return self.mgr.Times(l, r)

    def BVHack(self, op):
        def _res(a, b):
            if b.is_constant():
                return op(a, b.constant_value())
            else:
                raise SyntaxError("Constant expected, got '%s'" % b)
        return _res


class HRParser(object):
    """The Pratt-parser for the Human-Readable pySMT syntax"""

    def __init__(self, env=None):
        if env is None:
            env = get_env()
        self.env = env
        self.mgr = env.formula_manager
        self.get_type = env.stc.get_type
        self.lexer = HRLexer(env)

        self.token = None
        self.tokenizer = None

    def expression(self, rbp=0):
        """Parses an expression: this function should not be directly called
        by classes outside this module
        """
        t = self.token
        self.token = next(self.tokenizer)
        left = t.nud(self)
        while rbp < self.token.lbp:
            t = self.token
            self.token = next(self.tokenizer)
            left = t.led(self, left)
        return left

    def parse_fname(self, fname):
        """Parses the content of the given file name"""
        with open(fname, "r") as f:
            return self.parse(f.read())

    def parse(self, string):
        """Parses the content of the given string"""
        self.token = None
        self.tokenizer = self.lexer.tokenize(string)
        self.token = next(self.tokenizer)
        result = self.expression()
        try:
            bd = next(self.tokenizer)
            raise SyntaxError("Bogus data after expression: '%s' (Partial: %s)" \
                              % (bd, result))
        except StopIteration:
            return result

    def advance(self):
        """Advance reading of one token"""
        self.token = next(self.tokenizer)


class GrammarSymbol(object):
    """Base class for all the parsing tokens"""
    def __init__(self, lbp=0, value=None, payload=None):
        self.lbp = lbp
        self.value = value
        self.payload = payload

    def nud(self, parser):
        raise SyntaxError("Syntax error at token '%s'." % parser.token)

    def led(self, parser, left):
        raise SyntaxError("Syntax error at token '%s' (Read: '%s')." % \
                          (parser.token, left))


## Placeholder tokens
#####################

class EndOfInput(GrammarSymbol):
    pass

class ClosePar(GrammarSymbol):
    pass

class CloseBrak(GrammarSymbol):
    pass

class ExprElse(GrammarSymbol):
    pass

class ExprComma(GrammarSymbol):
    pass

class ExprDot(GrammarSymbol):
    pass


## Grammar tokens
#####################

class Constant(GrammarSymbol):
    def __init__(self, value):
        GrammarSymbol.__init__(self)
        self.value = value

    def nud(self, parser):
        return self.value


class Identifier(GrammarSymbol):
    def __init__(self, name):
        GrammarSymbol.__init__(self)
        self.value = get_env().formula_manager.get_symbol(name)
        if self.value is None:
            raise ValueError("Undefined symbol: '%s'" % name)

    def nud(self, parser):
        return self.value


class ExprIf(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 5

    def led(self, parser, left):
        cond_ = left
        then_ = parser.expression(self.lbp)
        if type(parser.token) != ExprElse:
            raise SyntaxError("Expected ':'")
        parser.advance()
        else_ = parser.expression(self.lbp)
        return parser.mgr.Ite(cond_, then_, else_)


class OpenPar(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 200

    def nud(self, parser):
        r = parser.expression()
        if type(parser.token) != ClosePar:
            raise SyntaxError("Expected ')', got '%s'" )
        parser.advance()
        return r

    def led(self, parser, left):
        # a function call
        fun = left
        params = []
        if type(parser.token) != ClosePar:
            while True:
                r = parser.expression()
                params.append(r)
                if type(parser.token) != ExprComma:
                    break
                parser.advance()
        if type(parser.token) != ClosePar:
            raise SyntaxError("Expected ')'")
        parser.advance()
        return parser.mgr.Function(fun, params)


class OpenBrak(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 300

    def led(self, parser, left):
        # BVExtract
        bv = left
        start = parser.expression()
        if type(parser.token) != ExprElse:
            raise SyntaxError("Expected ':'")
        parser.advance()
        end = parser.expression()
        if type(parser.token) != CloseBrak:
            raise SyntaxError("Expected ']'")
        parser.advance()
        return parser.mgr.BVExtract(bv,
                                    start.constant_value(),
                                    end.constant_value())


class InfixOpAdapter(GrammarSymbol):
    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def led(self, parser, left):
        right = parser.expression(self.lbp)
        return self.operator(left, right)

    def __repr__(self):
        return repr(self.operator)


class UnaryOpAdapter(GrammarSymbol):
    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def nud(self, parser):
        right = parser.expression(self.lbp)
        return self.operator(right)


class Quantifier(GrammarSymbol):
    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def nud(self, parser):
        qvars = []
        if type(parser.token) != ExprDot:
            while True:
                r = parser.expression()
                qvars.append(r)
                if type(parser.token) != ExprComma:
                    break
                parser.advance()
        if type(parser.token) != ExprDot:
            raise SyntaxError("Expected '.'")
        parser.advance()
        matrix = parser.expression(self.lbp)
        return self.operator(qvars, matrix)


class InfixOrUnaryOpAdapter(GrammarSymbol):
    def __init__(self, b_operator, u_operator, b_lbp, u_lbp):
        GrammarSymbol.__init__(self)
        self.b_operator = b_operator
        self.u_operator = u_operator
        self.lbp = b_lbp
        self.u_lbp = u_lbp

    def nud(self, parser):
        right = parser.expression(self.u_lbp)
        return self.u_operator(right)

    def led(self, parser, left):
        right = parser.expression(self.lbp)
        return self.b_operator(left, right)
