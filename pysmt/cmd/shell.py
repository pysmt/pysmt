#!/usr/bin/env python
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

import sys
import argparse
from warnings import warn

from pysmt import __version__
from pysmt.shortcuts import *
from pysmt.typing import INT, REAL, BOOL, BVType, BV32

from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import InterpreterOMT, InterpreterSMT
from pysmt.smtlib.commands import CHECK_SAT, GET_VALUE, GET_OBJECTIVES, ECHO
from pysmt.logics import PYSMT_LOGICS

welcome_msg = \
"""Welcome to pySMT!!!

You are within a Python shell enhanced with pySMT functionalities.

First time here? Try:

>>>> x = Symbol("x")    # Declares a symbol x
>>>> f = And(x, Not(x)) # Builds a simple formula
>>>> print(f)
(x & (! x))

>>>> is_sat(f)
False

>>>> is_unsat(f)
True

>>>> str(get_model(x))
'x := True'

Happy Solving!
"""



class PysmtShell(object):

    def __init__(self, argv):
        self.env = get_env()
        self.solvers = list(self.env.factory.all_solvers().keys())
        self.optimizers = list(self.env.factory.all_optimizers().keys())
        self.parser = self.get_parser()
        self.args = self.parser.parse_args(argv)


    def get_parser(self):
        parser = argparse.ArgumentParser(description="Command-line interface " \
                                         "for pySMT problems")
        parser.add_argument('--version', action='version',
                        version='%(prog)s {version}'.format(version=__version__))
        parser.add_argument('--file', '-f', metavar='filename', type=str,
                            help='A script file to read from instead of stdin')

        parser.add_argument('--interactive', '-i', action='store_true',
                            help="Start a python interactive shell instead of" \
                            " reading an SMT2 input")

        parser.add_argument('--solver', '-s', metavar='name', type=str,
                            choices=['auto'] + self.solvers,
                            default=None,
                            help='The solver to use (default: auto)')
        parser.add_argument('--optimizer', '-o', metavar='opt_name', type=str,
                            choices=['auto'] + self.optimizers,
                            default=None,
                            help='The OMT optimizer to use (default: auto)')
        parser.add_argument('--logic', '-l', metavar='logic_name', type=str,
                            choices=['auto'] + [str(l) for l in PYSMT_LOGICS],
                            default=None,
                            help='The logic to use for solver/optimizer selection (default: auto)')
        return parser


    def interactive(self):
        # Enable infix notation in Interactive mode
        get_env().enable_infix_notation = True
        try:
            import IPython
            print(welcome_msg)
            IPython.embed()
        except ImportError:
            import code
            code.interact(welcome_msg)


    def _print(self, val, stream_out):
        stream_out.write(val)
        stream_out.write("\n")
        stream_out.flush()


    def print_result(self, stream_out, cmd, result):
        name, _ = cmd
        if name == ECHO:
            self._print(result, stream_out)
        elif name == CHECK_SAT:
            if result == True:
                self._print("sat", stream_out)
            else:
                self._print("unsat", stream_out)
        elif name == GET_VALUE:
            self._print("(", stream_out)
            for k, r in result.items():
                self._print("  (%s %s)" % (k,r), stream_out)
            self._print(")", stream_out)
        elif name == GET_OBJECTIVES:
            self._print("(objectives", stream_out)
            for r in result:
                self._print("  (%s %s)" % (r[0], r[1]), stream_out)
            self._print(")", stream_out)


    def smtlib_solver(self, stream_in, stream_out):
        smt_parser = SmtLibParser()
        s_name = self.args.solver
        opt_name = self.args.optimizer
        logic = self.args.logic
        if logic == "auto":
            logic = None

        if opt_name is not None:
            if opt_name == "auto":
                solver = Optimizer(logic=logic)
            else:
                solver = Optimizer(name=opt_name, logic=logic)
            inter = InterpreterOMT()
        else:
            if s_name == "auto":
                solver = Solver(logic=logic)
            else:
                solver = Solver(name=s_name, logic=logic)
            inter = InterpreterSMT()
        for cmd in smt_parser.get_command_generator(stream_in):
            r = inter.evaluate(cmd, solver)
            self.print_result(stream_out, cmd, r)


    def main(self):
        if self.args.interactive:
            if self.args.file is not None:
                print("Unable to execute in interactive mode with an input file")
                sys.exit(1)
            if self.args.solver != "auto":
                warn("The solver option will be ignored in interactive mode")
            self.interactive()
        else:
            if self.args.file is None:
                self.smtlib_solver(sys.stdin, sys.stdout)
            else:
                with open(self.args.file, "r") as input_stream:
                    self.smtlib_solver(input_stream, sys.stdout)


def main_interactive():
    shell = PysmtShell(sys.argv[1:])
    shell.interactive()

def main():
    shell = PysmtShell(sys.argv[1:])
    shell.main()


if __name__ == "__main__":
    main()
