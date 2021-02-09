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
import collections
from io import StringIO

from pysmt.test import TestCase, main
from pysmt.smtlib.parser import SmtLibParser
from pysmt.exceptions import UnknownSmtLibCommandError, PysmtValueError

TS = collections.namedtuple('TS', ['init', 'trans'])
TSFormula = collections.namedtuple('TSFormula', ['formula', "is_init"])

class TSSmtLibParser(SmtLibParser):
    def __init__(self, env=None, interactive=False):
        SmtLibParser.__init__(self, env, interactive)

        # Add new commands
        self.commands["init"] = self._cmd_init
        self.commands["trans"] = self._cmd_trans

        # Remove unused commands
        del self.commands["check-sat"]
        del self.commands["get-value"]
        # ...

        # Add 'next' function
        self.interpreted["next"] = self._operator_adapter(self._next_var)

    def _cmd_init(self, current, tokens):
        expr = self.get_expression(tokens)
        self.consume_closing(tokens, current)
        return TSFormula(expr, True)

    def _cmd_trans(self, current, tokens):
        expr = self.get_expression(tokens)
        self.consume_closing(tokens, current)
        return TSFormula(expr, False)

    def _next_var(self, symbol):
        if symbol.is_symbol():
            name = symbol.symbol_name()
            ty = symbol.symbol_type()
            return self.env.formula_manager.Symbol("next_" + name, ty)
        else:
            raise PysmtValueError("'next' operator can be applied only to symbols")

    def get_ts(self, script):
        init = self.env.formula_manager.TRUE()
        trans = self.env.formula_manager.TRUE()

        for cmd in self.get_command_generator(script):
            # Simply skip declarations and other commands...
            if type(cmd) == TSFormula:
                if cmd.is_init:
                    init = cmd.formula
                else:
                    trans = cmd.formula

        return TS(init, trans)

    def get_ts_fname(self, ts_fname):
        with open(ts_fname, 'r') as script:
            return self.get_ts(script)


class TestParserExtensibility(TestCase):

    def setUp(self):
        self.ts_parser = TSSmtLibParser()
        self.smt_parser = SmtLibParser()

    def test_wrong(self):
        txt = """
        (declare-fun A () Bool)
        (declare-fun B () Bool)
        (assert (and A B))
        (check-sat)
        (exit)
        """
        with self.assertRaises(UnknownSmtLibCommandError):
            self.ts_parser.get_ts(StringIO(txt))
        script = self.smt_parser.get_script(StringIO(txt))
        self.assertIsNotNone(script)

    def test_basic(self):
        txt = """
        (declare-fun A () Bool)
        (declare-fun B () Bool)
        (init (and A B))
        (trans (=> A (next A)))
        (exit)
        """
        with self.assertRaises(UnknownSmtLibCommandError):
            self.smt_parser.get_script(StringIO(txt))
        ts = self.ts_parser.get_ts(StringIO(txt))
        self.assertIsNotNone(ts)


if __name__ == '__main__':
    main()
