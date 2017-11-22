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
from collections import namedtuple

import pysmt.typing as types
from pysmt.environment import get_env
from pysmt.exceptions import PysmtSyntaxError, UndefinedSymbolError
from pysmt.constants import Fraction


def HRParser(env=None):
    """Parser for HR format of pySMT."""
    return PrattParser(HRLexer, env=env)


def parse(string):
    """Parse an hr-string."""
    return HRParser().parse(string)


# Rules for the Lexer
Rule = namedtuple('Rule', ['regex', 'symbol', 'is_functional'])


class Lexer(object):
    """This class produces a stream of token objects for the Pratt-parser.

    The rules for the token are store in self.rules. Call self.compile() after
    modifying rules.
    """

    def __init__(self, env=None):
        if env is None:
            env = get_env()
        self.env = env
        self.mgr = env.formula_manager
        self.get_type = env.stc.get_type

        self.rules = []
        self.scanner = None
        self.eoi = EndOfInput()

    def compile(self):
        self.scanner = re.compile("|".join(rule.regex for rule in self.rules),
                                  re.DOTALL | re.VERBOSE)
    def lexing_error(self, read):
        raise PysmtSyntaxError("Unexpected input: %s" % read)

    def tokenize(self, data):
        """The token generator for the given string"""
        for match in re.finditer(self.scanner, data):
            for idx, capture in enumerate(match.groups()):
                if capture is not None:
                    rule = self.rules[idx]
                    symbol = rule.symbol
                    if rule.symbol is not None:
                        if rule.is_functional:
                            yield symbol(capture)
                        else:
                            yield symbol
                    break
        yield self.eoi

# EOC Lexer


class GrammarSymbol(object):
    """Base class for all the parsing tokens"""

    def __init__(self, lbp=0, value=None, payload=None):
        self.lbp = lbp
        self.value = value
        self.payload = payload

    def nud(self, parser):
        raise PysmtSyntaxError("Syntax error at token '%s'." % parser.token)

    def led(self, parser, left):
        raise PysmtSyntaxError("Syntax error at token '%s' (Read: '%s')." % \
                          (parser.token, left))

#
# Precedence table (from low priority to high priority):
#
# 10 : Xor, Implies, Iff
# 20 : Forall, Exists
# 30 : Or
# 40 : And
# 50 : Not
# 60 : LE, LT, Equals, GE, GT, BVULE, BVUGE, BVULT, BVUGT, BVSLE, BVSGE, BVSGT
# 70 : Plus, Minus, BVAdd, BVSub
# 80 : Times, Div, BVMul, BVUDiv, BVSDiv, BVSRem, BVURem
# 90 : BVLShl, BVLShr, BVAShr, BVConcat, BVXor, BVRor, BVRol, BVZExt, BVSExt, BVComp
# 100 : ToReal Uminus BVNeg BVToNat
# 200 : ()
# 300 : []

class HRLexer(Lexer):
    """Produces a stream of token objects for the Human-Readable format."""

    def __init__(self, env=None):
        Lexer.__init__(self, env=env)

        hr_rules = [
            Rule(r"(\s+)", None, False),                    # whitespace
            Rule(r"(-?\d+/\d+)", self.real_constant, True), # fractions
            Rule(r"(-?\d+\.\d+)", self.real_constant, True),# decimals
            Rule(r"(-?\d+_\d+)", self.bv_constant, True),# bv
            Rule(r"(-?\d+)", self.int_constant, True),# integer literals
            Rule(r"\"(.*?)\"", self.string_constant, True), # String Constant
            Rule(r"BV\{(\d+)\}", self.bv_type, True),# BV Type
            Rule(r"(Array\{)", OpenArrayTypeTok(), False),# Array Type
            Rule(r"(Int)", IntTypeTok(), False),# Int Type
            Rule(r"(Real)", RealTypeTok(), False),# Real Type
            Rule(r"(Bool)", BoolTypeTok(), False),# Bool Type
            Rule(r"(&)", InfixOpAdapter(self.AndOrBVAnd, 40), False),# conjunction
            Rule(r"(\|)", InfixOpAdapter(self.OrOrBVOr, 30), False),# disjunction
            Rule(r"(!)", UnaryOpAdapter(self.NotOrBVNot, 50), False),# negation
            Rule(r"(\()", OpenPar(), False),# open parenthesis
            Rule(r"(\))", ClosePar(), False),# closed parenthesis
            Rule(r"(\[)", OpenBrak(), False),# open parenthesis
            Rule(r"(\])", CloseBrak(), False),# closed parenthesis
            Rule(r"(\})", CloseBrace(), False),# closed parenthesis
            Rule(r"(<<)", InfixOpAdapter(self.mgr.BVLShl, 90), False),# Shl
            Rule(r"(>>)", InfixOpAdapter(self.mgr.BVLShr, 90), False),# Shr
            Rule(r"(a>>)", InfixOpAdapter(self.mgr.BVAShr, 90), False),# AShr
            Rule(r"(<->)", InfixOpAdapter(self.mgr.Iff, 10), False),# iff
            Rule(r"(->)", InfixOpAdapter(self.mgr.Implies, 10), False),# implies
            Rule(r"(u<=)", InfixOpAdapter(self.mgr.BVULE, 60), False),# bvule
            Rule(r"(u>=)", InfixOpAdapter(self.mgr.BVUGE, 60), False),# bvuge
            Rule(r"(u<)", InfixOpAdapter(self.mgr.BVULT, 60), False),# bvult
            Rule(r"(u>)", InfixOpAdapter(self.mgr.BVUGT, 60), False),# bvugt
            Rule(r"(s<=)", InfixOpAdapter(self.mgr.BVSLE, 60), False),# bvsle
            Rule(r"(s>=)", InfixOpAdapter(self.mgr.BVSGE, 60), False),# bvsge
            Rule(r"(s<)", InfixOpAdapter(self.mgr.BVSLT, 60), False),# bvslt
            Rule(r"(s>)", InfixOpAdapter(self.mgr.BVSGT, 60), False),# bvsgt
            Rule(r"(>=)", InfixOpAdapter(self.mgr.GE, 60), False),# ge
            Rule(r"(<=)", InfixOpAdapter(self.mgr.LE, 60), False),# le
            Rule(r"(>)", InfixOpAdapter(self.mgr.GT, 60), False),# gt
            Rule(r"(<)", InfixOpAdapter(self.mgr.LT, 60), False),# lt
            Rule(r"(=)", InfixOpAdapter(self.mgr.Equals, 60), False),# eq
            Rule(r"(\+)", InfixOpAdapter(self.PlusOrBVAdd, 70), False),# plus
            Rule(r"(-)", InfixOrUnaryOpAdapter(self.MinusOrBVSub, self.UMinusOrBvNeg, 70, 100), False),# minus
            Rule(r"(\*)", InfixOpAdapter(self.TimesOrBVMul, 80), False),# times
            Rule(r"(\^)", InfixOpAdapter(self.mgr.Pow, 80), False),# pow
            Rule(r"(u/)", InfixOpAdapter(self.mgr.BVUDiv, 80), False),# udiv
            Rule(r"(s/)", InfixOpAdapter(self.mgr.BVSDiv, 80), False),# sdiv
            Rule(r"(/)", InfixOpAdapter(self.mgr.Div, 80), False),# div
            Rule(r"(s%)", InfixOpAdapter(self.mgr.BVSRem, 80), False),# srem
            Rule(r"(u%)", InfixOpAdapter(self.mgr.BVURem, 80), False),# urem
            Rule(r"(\?)", ExprIf(), False), # question
            Rule(r"(:=)", ArrStore(), False),# ArrStore
            Rule(r"(::)", InfixOpAdapter(self.mgr.BVConcat, 90), False),# BVXor
            Rule(r"(:)", ExprElse(), False),# colon
            Rule(r"(False)", Constant(self.mgr.FALSE()), False), # False
            Rule(r"(True)", Constant(self.mgr.TRUE()), False),# True
            Rule(r"(,)", ExprComma(), False),# comma
            Rule(r"(\.)", ExprDot(), False),# dot
            Rule(r"(xor)", InfixOpAdapter(self.mgr.BVXor, 10), False),# BVXor
            Rule(r"(ROR)", InfixOpAdapter(self.BVHack(self.mgr.BVRor), 90), False),# BVRor
            Rule(r"(ROL)", InfixOpAdapter(self.BVHack(self.mgr.BVRol), 90), False),# BVRol
            Rule(r"(ZEXT)", InfixOpAdapter(self.BVHack(self.mgr.BVZExt), 90), False),# BVZext
            Rule(r"(SEXT)", InfixOpAdapter(self.BVHack(self.mgr.BVSExt), 90), False),# BVSext
            Rule(r"(bvcomp)", InfixOpAdapter(self.mgr.BVComp, 90), False),#
            Rule(r"(forall)", Quantifier(self.mgr.ForAll, 20), False),#
            Rule(r"(exists)", Quantifier(self.mgr.Exists, 20), False),#
            Rule(r"(ToReal)", UnaryOpAdapter(self.mgr.ToReal, 100), False),#
            Rule(r"(str\.len)", FunctionCallAdapter(self.mgr.StrLength, 100), False), # str_length
            Rule(r"(str\.\+\+)", FunctionCallAdapter(self.mgr.StrConcat, 100), False), # str_concat
            Rule(r"(str\.at)", FunctionCallAdapter(self.mgr.StrCharAt, 100), False), # str_charat
            Rule(r"(str\.contains)", FunctionCallAdapter(self.mgr.StrContains, 100), False), # str_contains
            Rule(r"(str\.indexof)", FunctionCallAdapter(self.mgr.StrIndexOf, 100), False), # str_indexof
            Rule(r"(str\.replace)", FunctionCallAdapter(self.mgr.StrReplace, 100), False), # str_replace
            Rule(r"(str\.substr)", FunctionCallAdapter(self.mgr.StrSubstr, 100), False), # str_substr
            Rule(r"(str\.prefixof)", FunctionCallAdapter(self.mgr.StrPrefixOf, 100), False), # str_prefixof
            Rule(r"(str\.suffixof)", FunctionCallAdapter(self.mgr.StrSuffixOf, 100), False), # str_suffixof
            Rule(r"(str\.to\.int)", FunctionCallAdapter(self.mgr.StrToInt, 100), False), # str_to_int
            Rule(r"(int\.to\.str)", FunctionCallAdapter(self.mgr.IntToStr, 100), False), # int_to_str
            Rule(r"(bv2nat)", UnaryOpAdapter(self.mgr.BVToNatural, 100), False),#
            Rule(r"'(.*?)'", self.identifier, True), # quoted identifiers
            Rule(r"([A-Za-z_][A-Za-z0-9_]*)", self.identifier, True),# identifiers
            Rule(r"(.)", self.lexing_error, True), # input error
        ]

        self.rules += hr_rules

        self.compile()

    def bv_type(self, read):
        return BVTypeTok(int(read))

    def real_constant(self, read):
        return Constant(self.mgr.Real(Fraction(read)))

    def bv_constant(self, read):
        v, w = read.split("_")
        return Constant(self.mgr.BV(int(v), width=int(w)))

    def int_constant(self, read):
        return Constant(self.mgr.Int(int(read)))

    def string_constant(self, read):
        return Constant(self.mgr.String(read))

    def identifier(self, read):
        return Identifier(read, env=self.env)

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
                raise PysmtSyntaxError("Constant expected, got '%s'" % b)
        return _res


# EOC HRLexer

#
# Grammar tokens
#

# Placeholder tokens


class CloseBrace(GrammarSymbol):
    pass

class ArrStore(GrammarSymbol):
    pass


class BVTypeTok(GrammarSymbol):
    def __init__(self, width):
        GrammarSymbol.__init__(self)
        self.width = width

    def nud(self, parser):
        return types.BVType(self.width)

class IntTypeTok(GrammarSymbol):
    def nud(self, parser):
        return types.INT

class RealTypeTok(GrammarSymbol):
    def nud(self, parser):
        return types.REAL

class BoolTypeTok(GrammarSymbol):
    def nud(self, parser):
        return types.BOOL

class Constant(GrammarSymbol):
    def __init__(self, value):
        GrammarSymbol.__init__(self)
        self.value = value

    def nud(self, parser):
        return self.value


class Identifier(GrammarSymbol):
    def __init__(self, name, env):
        GrammarSymbol.__init__(self)
        self.value = env.formula_manager.get_symbol(name)
        if self.value is None:
            raise UndefinedSymbolError(name)

    def nud(self, parser):
        return self.value


class ExprIf(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 5

    def led(self, parser, left):
        cond_ = left
        then_ = parser.expression(self.lbp)
        parser.expect(ExprElse, ':')
        else_ = parser.expression(self.lbp)
        return parser.mgr.Ite(cond_, then_, else_)


class OpenArrayTypeTok(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 5

    def nud(self, parser):
        idx_type = parser.expression()
        parser.expect(ExprComma, ",")
        el_type = parser.expression()
        parser.expect(CloseBrace, "}")
        if type(parser.token) == OpenPar:
            parser.advance()
            default = parser.expression()
            parser.expect(ClosePar, ")")
            return parser.mgr.Array(idx_type, default)
        else:
            return types.ArrayType(idx_type, el_type)


class OpenPar(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 200

    def nud(self, parser):
        r = parser.expression()
        if type(parser.token) != ClosePar:
            raise SyntaxError("Expected ')', got '%s'" % parser.token)
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
        parser.expect(ClosePar, ")")
        return parser.mgr.Function(fun, params)


class OpenBrak(GrammarSymbol):
    def __init__(self):
        GrammarSymbol.__init__(self)
        self.lbp = 300

    def led(self, parser, left):
        # BVExtract, Select or Store
        op = left
        e1 = parser.expression()
        if type(parser.token) == ExprElse:
            #BVExtract
            parser.advance()
            end = parser.expression()
            parser.expect(CloseBrak, "]")
            return parser.mgr.BVExtract(op,
                                        e1.constant_value(),
                                        end.constant_value())
        elif type(parser.token) == CloseBrak:
            # Select
            parser.advance()
            return parser.mgr.Select(op, e1)
        elif type(parser.token) == ArrStore:
            #Store
            parser.advance()
            e2 = parser.expression()
            parser.expect(CloseBrak, "]")
            return parser.mgr.Store(op, e1, e2)
        else:
            raise PysmtSyntaxError("Unexpected token:" + str(parser.token))


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
        parser.expect(ExprDot, ".")
        matrix = parser.expression(self.lbp)
        return self.operator(qvars, matrix)


class PrattParser(object):
    """The Pratt-Parser

    This parser is explained in:
       http://effbot.org/zone/simple-top-down-parsing.htm

    The LexerClass is required, and is the one doing the heavy lifting.
    """

    def __init__(self, LexerClass, env=None):
        if env is None:
            env = get_env()

        self.env = env
        self.mgr = env.formula_manager
        self.get_type = env.stc.get_type
        self.lexer = LexerClass(env)

        self.token = None
        self.tokenizer = None

    def expression(self, rbp=0):
        """Parses an expression"""
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
            raise PysmtSyntaxError("Bogus data after expression: '%s' "
                                   "(Partial: %s)" % (bd, result))
        except StopIteration:
            return result

    def advance(self):
        """Advance reading of one token"""
        self.token = next(self.tokenizer)


    def expect(self, token_class, token_repr):
        """
        Check that the next token is the specified one or fail with a
        ParserError
        """
        if type(self.token) != token_class:
            raise PysmtSyntaxError("Expected '%s'" % token_repr)
        self.advance()

# EOC PrattParser

#
# Adapters
#
# These are adapters used to create tokens for various types of symbols
#

class EndOfInput(GrammarSymbol):
    pass


class UnaryOpAdapter(GrammarSymbol):
    """Adapter for unary operator."""

    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def nud(self, parser):
        right = parser.expression(self.lbp)
        return self.operator(right)


class InfixOpAdapter(GrammarSymbol):
    """Adapter for infix operator."""

    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def led(self, parser, left):
        right = parser.expression(self.lbp)
        return self.operator(left, right)

    def __repr__(self):
        return repr(self.operator)


class InfixOrUnaryOpAdapter(GrammarSymbol):
    """Adapter for operators that can be both binary infix or unary.

    b_operator and b_lbp: define the behavior when considering the symbol
                          as a binary operator.
    u_operator and u_lbp: define the behavior when considering the symbol
                          as a unary operator.
    """

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


class FunctionCallAdapter(GrammarSymbol):
    """Adapter for function calls."""

    def __init__(self, operator, lbp):
        GrammarSymbol.__init__(self)
        self.operator = operator
        self.lbp = lbp

    def nud(self, parser):
        parser.advance() # OpenPar
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
        return self.operator(*params)

    def __repr__(self):
        return repr(self.operator)


class ClosePar(GrammarSymbol):
    pass


class CloseBrak(GrammarSymbol):
    pass


class ExprElse(GrammarSymbol):
    pass


class ExprDot(GrammarSymbol):
    pass


class ExprComma(GrammarSymbol):
    pass
