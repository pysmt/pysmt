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

from pysmt import git_version
from pysmt.shortcuts import *
from pysmt.typing import INT, REAL, BOOL, BVType, BV32

from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.script import evaluate_command
from pysmt.smtlib.commands import CHECK_SAT, GET_VALUE

welcome_msg = \
"""Welcome to pySMT!!!

You are within a Python shell enhanched with pySMT functionalities.

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
        self.parser = self.get_parser()
        self.args = self.parser.parse_args(argv)


    def get_parser(self):
        parser = argparse.ArgumentParser(description="Command-line interface " \
                                         "for pySMT problems")
        parser.add_argument('--version', action='version',
                        version='%(prog)s {version}'.format(version=git_version()))
        parser.add_argument('--file', '-f', metavar='filename', type=str,
                            help='A script file to read from instead of stdin')

        parser.add_argument('--interactive', '-i', action='store_true',
                            help="Start a python interactive shell instead of" \
                            " reading an SMT2 input")

        parser.add_argument('--solver', '-s', metavar='name', type=str,
                            choices=['auto'] + self.solvers,
                            default=None,
                            help='The solver to use (default: auto)')
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


    def print_result(self, cmd, result):
        name, _ = cmd
        if name == CHECK_SAT:
            if result == True:
                print("sat")
            else:
                print("unsat")
        elif name == GET_VALUE:
            print("(")
            for k, r in result.items():
                print("  (%s %s)" % (k,r))
            print(")")


    def smtlib_solver(self, stream):
        smt_parser = SmtLibParser()
        name = self.args.solver
        if name == "auto":
            solver = Solver()
        else:
            solver = Solver(name=name)

        for cmd in smt_parser.get_command_generator(stream):
            r = evaluate_command(cmd, solver)
            self.print_result(cmd, r)


    def main(self):
        if self.args.interactive:
            if self.args.file is not None:
                print("Unable to execute in interactive mode with an input file")
                sys.exit(1)
            if self.args.solver != "auto":
                warn("The solver option will be ignored in interactive mode")
            self.interactive()
        else:
            input_stream = sys.stdin
            if self.args.file is not None:
                input_stream = open(self.args.file, "r")
            self.smtlib_solver(input_stream)

def main_interactive():
    shell = PysmtShell(sys.argv[1:])
    shell.interactive()

def main():
    shell = PysmtShell(sys.argv[1:])
    shell.main()


if __name__ == "__main__":
    main()
