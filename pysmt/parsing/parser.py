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

from pysmt.parsing.pratt import PrattParser, Lexer, Rule, GrammarSymbol
from pysmt.parsing.pratt import (UnaryOpAdapter, InfixOpAdapter,
                                 InfixOrUnaryOpAdapter, FunctionCallAdapter)
from pysmt.parsing.pratt import ClosePar, CloseBrak, ExprElse, ExprComma, ExprDot


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
# 100 : ToReal Uminus BVNeg
# 200 : ()
# 300 : []

def HRParser(env=None):
    """Parser for HR format of pySMT."""
    return PrattParser(HRLexer, env=env)


def parse(string):
    """Parse a hr-string."""
    return HRParser().parse(string)


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
            Rule(r"(&)", InfixOpAdapter(self.AndOrBVAnd, 40), False),# conjunction
            Rule(r"(\|)", InfixOpAdapter(self.OrOrBVOr, 30), False),# disjunction
            Rule(r"(!)", UnaryOpAdapter(self.NotOrBVNot, 50), False),# negation
            Rule(r"(\()", OpenPar(), False),# open parenthesis
            Rule(r"(\))", ClosePar(), False),# closed parenthesis
            Rule(r"(\[)", OpenBrak(), False),# open parenthesis
            Rule(r"(\])", CloseBrak(), False),# closed parenthesis
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
            Rule(r"(u/)", InfixOpAdapter(self.mgr.BVUDiv, 80), False),# udiv
            Rule(r"(s/)", InfixOpAdapter(self.mgr.BVSDiv, 80), False),# sdiv
            Rule(r"(/)", InfixOpAdapter(self.mgr.Div, 80), False),# div
            Rule(r"(s%)", InfixOpAdapter(self.mgr.BVSRem, 80), False),# srem
            Rule(r"(u%)", InfixOpAdapter(self.mgr.BVURem, 80), False),# urem
            Rule(r"(\?)", ExprIf(), False), # question
            Rule(r"(::)", InfixOpAdapter(self.mgr.BVConcat, 90), False),# BVXor
            Rule(r"(:)", ExprElse(), False),# colon
            Rule(r"(False)", Constant(self.mgr.FALSE()), False), # False
            Rule(r"(True)", Constant(self.mgr.TRUE()), False),# True
            Rule(r"(,)", ExprComma(), False),# comma
            Rule(r"(\.)", ExprDot(), False),# dot
            Rule(r"(xor)", InfixOpAdapter(self.mgr.BVXor, 10), False),# BVXor
            Rule(r"(ROR)", InfixOpAdapter(self.BVHack(self.mgr.BVRor), 90), False),# BVXor
            Rule(r"(ROL)", InfixOpAdapter(self.BVHack(self.mgr.BVRol), 90), False),# BVXor
            Rule(r"(ZEXT)", InfixOpAdapter(self.BVHack(self.mgr.BVZExt), 90), False),# BVXor
            Rule(r"(SEXT)", InfixOpAdapter(self.BVHack(self.mgr.BVSExt), 90), False),# BVXor
            Rule(r"(bvcomp)", InfixOpAdapter(self.mgr.BVComp, 90), False),# BVXor
            Rule(r"(forall)", Quantifier(self.mgr.ForAll, 20), False),# BVXor
            Rule(r"(exists)", Quantifier(self.mgr.Exists, 20), False),# BVXor
            Rule(r"(ToReal)", UnaryOpAdapter(self.mgr.ToReal, 100), False),# BVXor
            Rule(r"(str\.len)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrLength, 100), False), # str_length
            Rule(r"(str\.\+\+)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrConcat, 100), False), # str_concat
            Rule(r"(str\.at)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrCharat, 100), False), # str_charat
            Rule(r"(str\.contains)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrContains, 100), False), # str_contains
            Rule(r"(str\.indexof)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrIndexof, 100), False), # str_indexof
            Rule(r"(str\.replace)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrReplace, 100), False), # str_replace
            Rule(r"(str\.substr)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrSubstr, 100), False), # str_substr
            Rule(r"(str\.prefixof)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrPrefixof, 100), False), # str_prefixof
            Rule(r"(str\.suffixof)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrSuffixof, 100), False), # str_suffixof
            Rule(r"(str\.to\.int)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrToInt, 100), False), # str_to_int
            Rule(r"(int\.to\.str)", FunctionCallAdapter(self.StrFunctions, self.mgr.IntToStr, 100), False), # int_to_str
            Rule(r"(str\.to\.uint16)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrToUint16, 100), False), # str_to_uint16
            Rule(r"(uint16\.to\.str)", FunctionCallAdapter(self.StrFunctions, self.mgr.Uint16ToStr, 100), False), # uint16_to_str
            Rule(r"(str\.to\.uint32)", FunctionCallAdapter(self.StrFunctions, self.mgr.StrToUint32, 100), False), # str_to_uint32
            Rule(r"(uint32\.to\.str)", FunctionCallAdapter(self.StrFunctions, self.mgr.Uint32ToStr, 100), False), # uint32_to_str
            Rule(r"'(.*?)'", self.identifier, True), # quoted identifiers
            Rule(r"([A-Za-z_][A-Za-z0-9_]*)", self.identifier, True),# identifiers
            Rule(r"(.)", self.lexing_error, True), # input error
        ]

        self.rules += hr_rules

        self.compile()

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
                raise SyntaxError("Constant expected, got '%s'" % b)
        return _res

    def StrFunctions(self, funcCallAdapter):
        if (funcCallAdapter.funcName == self.mgr.StrLength ):
            if(len(funcCallAdapter.params) != 1):
                raise SyntaxError("str.len expects exactly one argument")
            return self.mgr.StrLength(funcCallAdapter.params[0])
        elif (funcCallAdapter.funcName == self.mgr.StrConcat ):
            if(len(funcCallAdapter.params) < 2):
                raise SyntaxError("str.++ expects atleast two arguments")
            return self.mgr.StrConcat(funcCallAdapter.params)
        elif (funcCallAdapter.funcName == self.mgr.StrCharat ):
            if(len(funcCallAdapter.params) != 2):
                raise SyntaxError("str.at expects exactly two arguments")
            return self.mgr.StrCharat(funcCallAdapter.params[0],funcCallAdapter.params[1]) 
        elif (funcCallAdapter.funcName == self.mgr.StrContains ):
            if(len(funcCallAdapter.params) != 2):
                raise SyntaxError("str_contains expects exactly two arguments")
            return self.mgr.StrContains(funcCallAdapter.params[0],funcCallAdapter.params[1]) 
        elif (funcCallAdapter.funcName == self.mgr.StrIndexof ):
            if(len(funcCallAdapter.params) != 3):
                raise SyntaxError("str.indexof expects exactly three arguments")
            return self.mgr.StrIndexof(funcCallAdapter.params[0],funcCallAdapter.params[1],funcCallAdapter.params[2]) 
        elif (funcCallAdapter.funcName == self.mgr.StrReplace ):
            if(len(funcCallAdapter.params) != 3):
                raise SyntaxError("str.replace expects exactly three arguments")
            return self.mgr.StrReplace(funcCallAdapter.params[0],funcCallAdapter.params[1],funcCallAdapter.params[2]) 
        elif (funcCallAdapter.funcName == self.mgr.StrSubstr ):
            if(len(funcCallAdapter.params) != 3):
                raise SyntaxError("str.substr expects exactly three arguments")
            return self.mgr.StrSubstr(funcCallAdapter.params[0],funcCallAdapter.params[1],funcCallAdapter.params[2]) 
        elif (funcCallAdapter.funcName == self.mgr.StrPrefixof ):
            if(len(funcCallAdapter.params) != 2):
                raise SyntaxError("str.prefixof expects exactly two arguments")
            return self.mgr.StrPrefixof(funcCallAdapter.params[0],funcCallAdapter.params[1]) 
        elif (funcCallAdapter.funcName == self.mgr.StrSuffixof ):
            if(len(funcCallAdapter.params) != 2):
                raise SyntaxError("str.suffixof expects exactly two arguments")
            return self.mgr.StrSuffixof(funcCallAdapter.params[0],funcCallAdapter.params[1]) 
        elif (funcCallAdapter.funcName == self.mgr.StrToInt ):
            if(len(funcCallAdapter.params) != 1):
                raise SyntaxError("str.to.int expects only one parameter")
            return self.mgr.StrToInt(funcCallAdapter.params[0]) 
        elif (funcCallAdapter.funcName == self.mgr.IntToStr ):
            if(len(funcCallAdapter.params) != 1):
                raise SyntaxError("int.to.str expects only one parameter")
            return self.mgr.IntToStr(funcCallAdapter.params[0]) 
        elif (funcCallAdapter.funcName == self.mgr.StrToUint16 ):
            if(len(funcCallAdapter.params) != 1):
                raise SyntaxError("str.to.uint16 expects only one parameter")
            return self.mgr.StrToUint16(funcCallAdapter.params[0]) 
        elif (funcCallAdapter.funcName == self.mgr.Uint16ToStr ):
            if(len(funcCallAdapter.params) != 1):
                raise SyntaxError("uint16.to.str expects only one parameter")
            return self.mgr.Uint16ToStr(funcCallAdapter.params[0]) 
        elif (funcCallAdapter.funcName == self.mgr.StrToUint32 ):
            if(len(funcCallAdapter.params) != 1):
                raise SyntaxError("str.to.uint32 expects only one parameter")
            return self.mgr.StrToUint32(funcCallAdapter.params[0]) 
        elif (funcCallAdapter.funcName == self.mgr.Uint32ToStr ):
            if(len(funcCallAdapter.params) != 1):
                raise SyntaxError("uint32.to.str expects only one parameter")
            return self.mgr.Uint32ToStr(funcCallAdapter.params[0])
        else:
            raise SyntaxError("Unknown function")
        
            
# EOC HRLexer

#
# Grammar tokens
#

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
