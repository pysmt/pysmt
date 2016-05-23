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

from pysmt.environment import get_env


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
            raise SyntaxError("Bogus data after expression: '%s' (Partial: %s)" \
                              % (bd, result))
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
            raise SyntaxError("Expected '%s'" % token_repr)
        self.advance()

# EOC PrattParser


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
        raise SyntaxError("Unexpected input: %s" % read)

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
        raise SyntaxError("Syntax error at token '%s'." % parser.token)

    def led(self, parser, left):
        raise SyntaxError("Syntax error at token '%s' (Read: '%s')." % \
                          (parser.token, left))



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
