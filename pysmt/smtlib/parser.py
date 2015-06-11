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
import functools
from fractions import Fraction
from warnings import warn
from six import iteritems
from six.moves import xrange

import pysmt.smtlib.commands as smtcmd
from pysmt.environment import get_env
from pysmt.typing import BOOL, REAL, INT, FunctionType, BVType
from pysmt.logics import get_logic_by_name, UndefinedLogicError
from pysmt.exceptions import UnknownSmtLibCommandError
from pysmt.smtlib.script import SmtLibCommand, SmtLibScript
from pysmt.smtlib.annotations import Annotations
import pysmt.utils as utils

def get_formula(script_stream, environment=None):
    """
    Returns the formula asserted at the end of the given script

    script_stream is a file descriptor.
    """
    mgr = None
    if environment is not None:
        mgr = environment.formula_manager

    parser = SmtLibParser(environment)
    script = parser.get_script(script_stream)
    return script.get_last_formula(mgr)


def get_formula_strict(script_stream, environment=None):
    """Returns the formula defined in the SMTScript.

    This function assumes that only one formula is defined in the
    SMTScript. It will raise an exception if commands such as pop and
    push are present in the script, or if check-sat is called more
    than once.
    """
    mgr = None
    if environment is not None:
        mgr = environment.formula_manager

    parser = SmtLibParser(environment)
    script = parser.get_script(script_stream)
    return script.get_strict_formula(mgr)


def get_formula_fname(script_fname, environment=None, strict=True):
    """Returns the formula asserted at the end of the given script."""
    with utils.BufferedTextReader(script_fname) as script:
        if strict:
            return get_formula_strict(script, environment)
        else:
            return get_formula(script, environment)


class SmtLibExecutionCache(object):
    """Execution environment for SMT2 script execution"""
    def __init__(self):
        self.keys = {}
        self.definitions = {}
        self.annotations = Annotations()

    def bind(self, name, value):
        """Binds a symbol in this environment"""
        lst = self.keys.setdefault(name, [])
        lst.append(value)

    def unbind(self, name):
        """Unbinds the last binding of this symbol"""
        self.keys[name].pop()

    def define(self, name, parameters, expression):
        self.definitions[name] = (parameters, expression)

    def _define_adapter(self, formal_parameters, expression):
        def res(*actual_parameters):
            assert len(formal_parameters) == len(actual_parameters)
            submap = dict(zip(formal_parameters, actual_parameters))
            return expression.substitute(submap)
        return res

    def get(self, name):
        """Returns the last binding for 'name'"""
        if name in self.definitions:
            (parameters, expression) = self.definitions[name]
            if len(parameters) == 0:
                return expression
            return self._define_adapter(parameters, expression)
        if name in self.keys:
            if len(self.keys[name]) > 0:
                return self.keys[name][-1]
            else:
                return None
        else:
            return None

    def update(self, value_map):
        """Binds all the symbols in 'value_map'"""
        for k, val in iteritems(value_map):
            self.bind(k, val)

    def unbind_all(self, values):
        """UnBinds all the symbols in 'values'"""
        for k in values:
            self.unbind(k)


class Tokenizer(object):
    """
    Takes a file-like object and produces a stream of tokens following
    the LISP rules.
    """

    def __init__(self, handle):
        self.handle = handle
        self.spaces = set([" ", "\n", "\t"])
        self.separators = set(["(", ")", "|"])
        self.specials = self.spaces | self.separators | set([";", ""])
        self.read = self.handle.read
        self.eof = False

    def tokens(self):
        c = self.read(1)
        while not self.eof:
            if c in self.specials:
                # consume all the spaces
                if c in self.spaces:
                    while c and c in self.spaces:
                        c = self.read(1)

                elif c in self.separators:
                    if c == "|":
                        s = []
                        c = self.read(1)
                        while c and c != "|":
                            s.append(c)
                            c = self.read(1)
                        if not c:
                            raise SyntaxError("Expected '|'")
                        yield ("".join(s))
                    else:
                        yield c
                    c = self.read(1)

                elif c == ";":
                    while c and c != "\n":
                        c = self.read(1)
                    c = self.read(1)

                else:
                    # EOF
                    self.eof = True
                    assert len(c) == 0
            else:
                tk = []
                while c not in self.specials:
                    tk.append(c)
                    c = self.read(1)
                yield "".join(tk)



class SmtLibParser(object):
    """
    Parse an SmtLib file and builds an SmtLibScript object.

    The main function is get_script (and its wrapper
    get_script_fname).  This function relies on the Tokenizer (to
    split the inputs in token) that is consumed by the get_command
    function that returns a SmtLibCommand for each command in the
    original file.

    """

    def __init__(self, environment=None):
        self.pysmt_env = get_env() if environment is None else environment

        # Placeholders for fields filled by self._reset
        self._current_env = None
        self.cache = None
        self.logic = None
        self._reset()

        # Special tokens appearing in expressions
        self.parentheses = set(["(", ")"])
        self.specials = set(["let", "!", "exists", "forall"])



    def _reset(self):
        """Resets the parser to the initial state"""
        self.cache = SmtLibExecutionCache()
        self.logic = None
        self._current_env = self.pysmt_env

        mgr = self.pysmt_env.formula_manager
        self.cache.update({'+':mgr.Plus,
                           '-':self._minus_or_uminus,
                           '*':mgr.Times,
                           '/':self._division,
                           '>':mgr.GT,
                           '<':mgr.LT,
                           '>=':mgr.GE,
                           '<=':mgr.LE,
                           '=':self._equals_or_iff,
                           'not':mgr.Not,
                           'and':mgr.And,
                           'or':mgr.Or,
                           'xor':mgr.Xor,
                           '=>':mgr.Implies,
                           '<->':mgr.Iff,
                           'ite':mgr.Ite,
                           'false':mgr.FALSE(),
                           'true':mgr.TRUE(),
                           'to_real':mgr.ToReal,
                           'concat':mgr.BVConcat,
                           'bvnot':mgr.BVNot,
                           'bvand':mgr.BVAnd,
                           'bvor':mgr.BVOr,
                           'bvneg':mgr.BVNeg,
                           'bvadd':mgr.BVAdd,
                           'bvmul':mgr.BVMul,
                           'bvudiv':mgr.BVUDiv,
                           'bvurem':mgr.BVURem,
                           'bvshl':mgr.BVLShl,
                           'bvlshr':mgr.BVLShr,
                           'bvsub':mgr.BVSub,
                           'bvult':mgr.BVULT,
                           'bvxor':mgr.BVXor,
                           '_':self._smtlib_underscore,
                           # Extended Functions
                           'bvnand':mgr.BVNand,
                           'bvnor':mgr.BVNor,
                           'bvxnor':mgr.BVXnor,
                           'bvcomp':mgr.BVComp,
                           'bvsdiv':mgr.BVSDiv,
                           'bvsrem':mgr.BVSRem,
                           'bvsmod':mgr.BVSMod,
                           'bvashr':mgr.BVAShr,
                           'bvule':mgr.BVULE,
                           'bvugt':mgr.BVUGT,
                           'bvuge':mgr.BVUGE,
                           'bvslt':mgr.BVSLT,
                           'bvsle':mgr.BVSLE,
                           'bvsgt':mgr.BVSGT,
                           'bvsge':mgr.BVSGE,
                           })


    def _minus_or_uminus(self, *args):
        """Utility function that handles both unary and binary minus"""
        mgr = self._current_env.formula_manager
        if len(args) == 1:
            lty = self._current_env.stc.get_type(args[0])
            mult = None
            if lty == INT:
                if args[0].is_int_constant():
                    return mgr.Int(-1 * args[0].constant_value())
                mult = mgr.Int(-1)
            else:
                if args[0].is_real_constant():
                    return mgr.Real(-1 * args[0].constant_value())
                mult = mgr.Real(-1)
            return mgr.Times(mult, args[0])
        else:
            assert len(args) == 2
            return mgr.Minus(args[0], args[1])


    def _smtlib_underscore(self, *args):
        """Utility function that handles _ special function in SMTLIB"""
        mgr = self._current_env.formula_manager
        if args[0] == "extract":
            send, sstart = args[1:]
            try:
                start = int(sstart.constant_value())
                end = int(send.constant_value())
            except ValueError:
                raise SyntaxError("Expected number in '_ extract' expression")
            return lambda x : mgr.BVExtract(x, start, end)

        elif args[0] == "zero_extend":
            swidth = args[1]
            try:
                width = int(swidth.constant_value())
            except ValueError:
                raise SyntaxError("Expected number in '_ zero_extend' expression")
            return lambda x: mgr.BVZExt(x, width)

        elif args[0] == "repeat":
            scount = args[1]
            try:
                count = int(scount.constant_value())
            except ValueError:
                raise SyntaxError("Expected number in '_ repeat' expression")
            return lambda x: mgr.BVRepeat(x, count)

        elif args[0] == "rotate_left":
            sstep = args[1]
            try:
                step = int(sstep.constant_value())
            except ValueError:
                raise SyntaxError("Expected number in '_ rotate_left' expression")
            return lambda x: mgr.BVRol(x, step)

        elif args[0] == "rotate_right":
            sstep = args[1]
            try:
                step = int(sstep.constant_value())
            except ValueError:
                raise SyntaxError("Expected number in '_ rotate_left' expression")
            return lambda x: mgr.BVRor(x, step)

        elif args[0] == "sign_extend":
            swidth = args[1]
            try:
                width = int(swidth.constant_value())
            except ValueError:
                raise SyntaxError("Expected number in '(_ sign_extend) expression'")
            return lambda x: mgr.BVSExt(x, width)

        elif args[0].startswith("bv"):
            try:
                v = int(args[0][2:])
                l = int(args[1].constant_value())
            except ValueError:
                raise SyntaxError("Expected number in '_ bv' expression: '%s'" % args)
            return mgr.BV(v, l)

        else:
            raise SyntaxError("Unexpected '_' expression '%s'" % args[0])



    def _equals_or_iff(self, left, right):
        """Utility function that treats = between booleans as <->"""
        mgr = self._current_env.formula_manager
        lty = self._current_env.stc.get_type(left)
        if lty == BOOL:
            return mgr.Iff(left, right)
        else:
            return mgr.Equals(left, right)

    def _division(self, left, right):
        """Utility function that builds a division"""
        mgr = self._current_env.formula_manager
        if left.is_constant() and right.is_constant():
            return mgr.Real(Fraction(left.constant_value()) / \
                            Fraction(right.constant_value()))
        return mgr.Div(left, right)


    def _get_basic_type(self, type_name, params=None):
        """
        Returns the pysmt type representation for the given type name.
        If params is specified, the type is interpreted as a function type.
        """
        if params is None or len(params) == 0:
            if type_name == "Bool":
                return BOOL
            elif type_name == "Int":
                return INT
            elif type_name == "Real":
                return REAL
            elif type_name.startswith("BV"):
                size = int(type_name[2:])
                return BVType(size)
        else:
            rt = self._get_basic_type(type_name)
            pt = [self._get_basic_type(par) for par in params]
            return FunctionType(rt, pt)


    def _get_var(self, name, type_name, params=None):
        """Returns the PySMT variable corresponding to a declaration"""
        typename = self._get_basic_type(type_name, params)
        return self._current_env.formula_manager.Symbol(name=name,
                                                        typename=typename)


    def atom(self, token, mgr):
        """
        Given a token and a FormulaManager, returns the pysmt representation of
        the token
        """
        res = self.cache.get(token)
        if res is None:
            try:
                # This is a numerical constant
                if "." in token:
                    res = mgr.Real(Fraction(token))
                elif token.startswith("#"):
                    # it is a BitVector
                    value = None
                    width = None
                    if token[1] == "b":
                        # binary
                        width = len(token) - 2
                        value = int("0" + token[1:], 2)
                    else:
                        if token[1] != "x":
                            raise SyntaxError("Invalid bit-vector constant '%s'" % token)
                        width = (len(token) - 2) * 16
                        value = int("0" + token[1:], 16)
                    res = mgr.BV(value, width)
                else:
                    iterm = int(token)
                    # We found an integer, depending on the logic this can be
                    # an Int or a Real
                    if self.logic is None or self.logic.theory.integer_arithmetic:
                        res = mgr.Int(iterm)
                    else:
                        res = mgr.Real(iterm)
            except ValueError:
                res = token
            self.cache.bind(token, res)
        return res


    def _use_env(self, env):
        """
        Sets the current environment to be the specified env
        """
        self._current_env = env
        mgr = env.formula_manager
        self.cache.update({'+':mgr.Plus,
                           '*':mgr.Times,
                           '>':mgr.GT,
                           '<':mgr.LT,
                           '>=':mgr.GE,
                           '<=':mgr.LE,
                           'not':mgr.Not,
                           'and':mgr.And,
                           'or':mgr.Or,
                           'xor':mgr.Xor,
                           '=>':mgr.Implies,
                           '<->':mgr.Iff,
                           'ite':mgr.Ite,
                           'false':mgr.FALSE(),
                           'true':mgr.TRUE(),
                           'to_real':mgr.ToReal,
                       })

    def _reset_env(self, env):
        """
        Resets the status after a call of _use_env.
        """
        self.cache.unbind_all(['+', '*', '>', '<', '>=', '<=', 'not', 'and',
                               'or', 'xor', '=>', '<->', 'ite', 'false', 'true',
                               'to_real'])
        self._current_env = env


    def _handle_let(self, varlist, bdy):
        """ Cleans the execution environment when we exit the scope of a 'let' """
        for k in varlist:
            self.cache.unbind(k)
        return bdy


    def _handle_quantifier(self, fun, vrs, body):
        """
        Cleans the execution environment when we exit the scope of a quantifier
        """
        for var in vrs:
            self.cache.unbind(var.symbol_name())
        return fun(vrs, body)


    def _handle_annotation(self, pyterm, *attrs):
        """
        This method is invoked when we finish parsing an annotated expression
        """

        # Iterate on elements.
        i = 0
        while i < len(attrs):
            if i+1 < len(attrs) and str(attrs[i+1])[0] != ":" :
                key, value = str(attrs[i]), str(attrs[i+1])
                if key[0] != ":":
                    raise SyntaxError("Annotations keys should start with colon")
                self.cache.annotations.add(pyterm, key[1:], value)
                i += 2
            else:
                key = str(attrs[i])
                if key[0] != ":":
                    raise SyntaxError("Annotations keys should start with colon")
                self.cache.annotations.add(pyterm, key[1:])
                i += 1

        return pyterm


    def get_expression(self, tokens):
        """
        Returns the pysmt representation of the given parsed expression
        """
        mgr = self._current_env.formula_manager
        stack = []

        while True:
            tk = next(tokens)

            if tk in self.parentheses:
                if tk == "(":
                    key = tk
                    while key == "(":
                        stack.append([])
                        key = next(tokens)

                    if key in self.specials:
                        if key == 'let':
                            self.consume_opening(tokens, "expression")
                            newvals = {}
                            current = "("
                            self.consume_opening(tokens, "expression")
                            while current != ")":
                                if current != "(":
                                    raise SyntaxError("Expected '(' in let binding")
                                vname = self.parse_atom(tokens, "expression")
                                expr = self.get_expression(tokens)
                                newvals[vname] = expr
                                self.consume_closing(tokens, "expression")
                                current = next(tokens)

                            for k, val in iteritems(newvals):
                                self.cache.bind(k, val)
                            stack[-1].append(self._handle_let)
                            stack[-1].append(newvals.keys())

                        elif key == 'exists' or key == 'forall':
                            vrs = []
                            self.consume_opening(tokens, "expression")
                            current = "("
                            self.consume_opening(tokens, "expression")
                            while current != ")":
                                if current != "(":
                                    raise SyntaxError("Expected '(' in let binding")
                                vname = self.parse_atom(tokens, "expression")
                                typename = self.parse_type(tokens, "expression")

                                var = self._get_var(vname, typename)
                                self.cache.bind(vname, var)
                                vrs.append(var)

                                self.consume_closing(tokens, "expression")
                                current = next(tokens)


                            quant = None
                            if key == 'forall':
                                quant = mgr.ForAll
                            else:
                                quant = mgr.Exists

                            stack[-1].append(self._handle_quantifier)
                            stack[-1].append(quant)
                            stack[-1].append(vrs)

                        else: # assert key == '!'
                            # An annotation is made as:
                            #   (! term attr1 ... attrn)
                            # where an attribute is either a keyword, or a keyword and value.
                            stack[-1].append(self._handle_annotation)

                    else:
                        stack[-1].append(self.atom(key, mgr))

                else:
                    if len(stack) == 0:
                        raise SyntaxError("Unexpected ')'")
                    lst = stack.pop()
                    fun = lst.pop(0)
                    # print fun, lst
                    if not callable(fun):
                        raise NotImplementedError("Unknown function '%s'" % fun)

                    res = fun(*lst)
                    if len(stack) > 0:
                        stack[-1].append(res)
                    else:
                        return res
            else:
                if len(stack) == 0:
                    return self.atom(tk, mgr)
                else:
                    stack[-1].append(self.atom(tk, mgr))



    def get_script(self, script):
        """
        Takes a file object and returns a SmtLibScript object representing the file
        """
        self._reset() # prepare the parser
        res = SmtLibScript()
        for cmd in self.get_command_generator(script):
            res.add_command(cmd)
        res.annotations = self.cache.annotations
        return res

    def get_command_generator(self, script):
        """Returns a python generator of SmtLibCommand's given a file object
        to read from

        This function can be used interactively, and blocks until a
        whole command is read from the script.

        """
        tokenizer = Tokenizer(script)
        for cmd in self.get_command(tokenizer.tokens()):
            yield cmd

    def get_script_fname(self, script_fname):
        """Given a filename and a Solver, executes the solver on the file."""
        with utils.BufferedTextReader(script_fname) as script:
            return self.get_script(script)

    def parse_atoms(self, tokens, command, min_size, max_size=None):
        """
        Parses a sequence of N atoms (min_size <= N <= max_size) consuming
        the tokens
        """
        if max_size is None:
            max_size = min_size

        res = []
        current = None
        for _ in xrange(min_size):
            current = next(tokens)
            if current == ")":
                raise SyntaxError("Expected at least %d arguments in %s command." %\
                                  (min_size, command))
            if current == "(":
                raise SyntaxError("Unexpected token '(' in %s command." % command)
            res.append(current)

        for _ in xrange(min_size, max_size + 1):
            current = next(tokens)
            if current == ")":
                return res
            if current == "(":
                raise SyntaxError("Unexpected token '(' in %s command." % command)
            res.append(current)
        raise SyntaxError("Unexpected token '%s' in %s command. Expected at " \
                          "most %d arguments." % (current, command, max_size))


    def parse_type(self, tokens, command, additional_token=None):
        """Parses a single type name from the tokens"""
        if additional_token is not None:
            var = additional_token
        else:
            var = next(tokens)
        if var == "(":
            op = next(tokens)
            if op != "_":
                raise SyntaxError("Unexpected token '%s' in %s command." % \
                                  (op, command))
            ts = next(tokens)
            if ts != "BitVec":
                raise SyntaxError("Unexpected token '%s' in %s command." % \
                                  (ts, command))

            size = 0
            dim = next(tokens)
            try:
                size = int(dim)
            except ValueError:
                raise SyntaxError("Unexpected token '%s' in %s command." % \
                                  (dim, command))

            self.consume_closing(tokens, command)
            return "BV%d" % size

        elif var == ")":
            raise SyntaxError("Unexpected token '%s' in %s command." % \
                              (var, command))
        return var


    def parse_atom(self, tokens, command):
        """Parses a single name from the tokens"""
        var = next(tokens)
        if var == "(" or var == ")":
            raise SyntaxError("Unexpected token '%s' in %s command." % \
                              (var, command))
        return var

    def parse_params(self, tokens, command):
        """Parses a list of names form the tokens"""
        self.consume_opening(tokens, command)
        current = next(tokens)
        res = []
        while current != ")":
            res.append(self.parse_type(tokens, command,additional_token=current))
            current = next(tokens)
        return res

    def parse_expr_list(self, tokens, command):
        """Parses a list of expressions form the tokens"""
        self.consume_opening(tokens, command)
        res = []
        while True:
            try:
                current = self.get_expression(tokens)
                res.append(current)
            except SyntaxError:
                return res

    def consume_opening(self, tokens, command):
        """ Consumes a single '(' """
        p = next(tokens)
        if p != "(":
            raise SyntaxError("Unexpected token '%s' in %s command. " \
                              "Expected '('" % (p, command))

    def consume_closing(self, tokens, command):
        """ Consumes a single ')' """
        p = next(tokens)
        if p != ")":
            raise SyntaxError("Unexpected token '%s' in %s command. " \
                              "Expected ')'" % (p, command))


    def _function_call_helper(self, v, *args):
        """ Helper function for dealing with function calls """
        return self._current_env.formula_manager.Function(v, args)


    def get_assignment_list(self, script):
        """
        Parse an assignment list produced by get-model and get-value
        commands in SmtLib
        """
        symbols = self._current_env.formula_manager.symbols
        self.cache.update(symbols)
        tokenizer = Tokenizer(script)
        tokens = tokenizer.tokens()
        res = []
        self.consume_opening(tokens, "<main>")
        current = next(tokens)
        while current != ")":
            if current != "(":
                raise SyntaxError("'(' expected")
            vname = self.get_expression(tokens)
            expr = self.get_expression(tokens)
            self.consume_closing(tokens, current)
            res.append((vname, expr))
            current = next(tokens)
        self.cache.unbind_all(symbols)
        return res


    def get_command(self, tokens):
        """Builds an SmtLibCommand instance out of a parsed term."""

        while True:
            self.consume_opening(tokens, "<main>")
            current = next(tokens)
            if current in [smtcmd.SET_INFO, smtcmd.SET_OPTION]:
                elements = self.parse_atoms(tokens, current, 2)
                yield SmtLibCommand(current, elements)

            elif current == smtcmd.ASSERT:
                expr = self.get_expression(tokens)
                self.consume_closing(tokens, current)
                yield SmtLibCommand(current, [expr])

            elif current == smtcmd.CHECK_SAT:
                self.parse_atoms(tokens, current, 0)
                yield SmtLibCommand(current, [])

            elif current == smtcmd.PUSH:
                elements = self.parse_atoms(tokens, current, 0, 1)

                levels = 1
                if len(elements) > 0:
                    levels = int(elements[0])
                yield SmtLibCommand(current, [levels])

            elif current == smtcmd.POP:
                elements = self.parse_atoms(tokens, current, 0, 1)

                levels = 1
                if len(elements) > 0:
                    levels = int(elements[0])
                yield SmtLibCommand(current, [levels])

            elif current == smtcmd.EXIT:
                self.parse_atoms(tokens, current, 0)
                yield SmtLibCommand(current, [])

            elif current == smtcmd.SET_LOGIC:
                elements = self.parse_atoms(tokens, current, 1)

                name = elements[0]
                try:
                    self.logic = get_logic_by_name(name)
                    yield SmtLibCommand(current, [self.logic])
                except UndefinedLogicError:
                    warn("Unknown logic '" + name + \
                         "'. Ignoring set-logic command.")
                    yield SmtLibCommand(current, [None])

            elif current == smtcmd.DECLARE_CONST:
                elements = self.parse_atoms(tokens, current, 2)

                (var, typename) = elements
                v = self._get_var(var, typename)
                self.cache.bind(var, v)
                yield SmtLibCommand(current, [v])

            elif current == smtcmd.GET_VALUE:
                params = self.parse_expr_list(tokens, current)
                self.consume_closing(tokens, current)
                yield SmtLibCommand(current, params)

            elif current == smtcmd.DECLARE_FUN:
                var = self.parse_atom(tokens, current)
                params = self.parse_params(tokens, current)
                typename = self.parse_type(tokens, current)
                self.consume_closing(tokens, current)

                v = self._get_var(var, typename, params)
                if v.symbol_type().is_function_type():
                    self.cache.bind(var, \
                            functools.partial(self._function_call_helper, v))
                else:
                    self.cache.bind(var, v)
                yield SmtLibCommand(current, [v])

            elif current == smtcmd.DEFINE_FUN:
                var = self.parse_atom(tokens, current)
                params = self.parse_params(tokens, current)
                self.parse_type(tokens, current)
                ebody = self.get_expression(tokens)
                self.consume_closing(tokens, current)

                formal = []
                for k in params:
                    (x,t) = k[0], k[1]
                    v = self._get_var(x, t)
                    self.cache.bind(x, v)
                    formal.append(v)

                for x in formal:
                    self.cache.unbind(x.symbol_name())

                self.cache.define(var, formal, ebody)
                yield SmtLibCommand(current, [var, formal, ebody])

            else:
                raise UnknownSmtLibCommandError(current)


if __name__ == "__main__":
    import sys

    def main():
        """Simple testing script"""
        args = sys.argv
        if len(args) != 2:
            print("Usage %s <file.smt2>" % args[0])
            exit(1)

        fname = args[1]

        parser = SmtLibParser()
        res = parser.get_script_fname(fname)
        assert res is not None
        print("Done")

    main()
