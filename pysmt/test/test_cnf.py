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
import unittest

import pysmt
from pysmt.shortcuts import And, Not, Symbol, Bool, Implies, is_sat, is_valid
from pysmt.cnf import CNFizer
from pysmt.logics import QF_BOOL, QF_LRA, QF_LIA
from pysmt.test import TestCase, skipIfNoSolverForLogic
from pysmt.test.examples import EXAMPLE_FORMULAS

class TestCnf(TestCase):

    def do_examples(self, logic):
        conv = CNFizer()
        for example in EXAMPLE_FORMULAS:
            if example.logic != logic:
                continue
            cnf = conv.convert_as_formula(example.expr)

            res = is_valid(Implies(cnf, example.expr), logic=logic)
            self.assertTrue(res)

            res = is_sat(cnf, logic=logic)
            self.assertEqual(res, example.is_sat)


    @skipIfNoSolverForLogic(QF_BOOL)
    def test_examples_solving_bool(self):
        self.do_examples(QF_BOOL)

    @skipIfNoSolverForLogic(QF_LRA)
    def test_examples_solving_lra(self):
        self.do_examples(QF_LRA)

    @skipIfNoSolverForLogic(QF_LIA)
    def test_examples_solving_lia(self):
        self.do_examples(QF_LIA)


if __name__ == '__main__':
    unittest.main()
