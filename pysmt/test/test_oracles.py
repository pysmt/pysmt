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
from unittest import skip

from pysmt.shortcuts import get_env, get_free_variables
from pysmt.shortcuts import Symbol, Implies, And, Not
from pysmt.test.examples import EXAMPLE_FORMULAS
from pysmt.test import TestCase
from pysmt.oracles import get_logic


class TestOracles(TestCase):
    @skip
    def test_quantifier_oracle(self):
        oracle = get_env().qfo
        for (f, _, _, logic) in EXAMPLE_FORMULAS:
            is_qf = oracle.is_qf(f)
            self.assertEqual(is_qf, logic.quantifier_free, f)

    def test_get_logic(self):
        for example in EXAMPLE_FORMULAS:
            target_logic = example.logic
            res = get_logic(example.expr)
            self.assertEqual(res, target_logic, "%s - %s != %s" % \
                              (example.expr, target_logic, res))

    def test_get_free_vars(self):
        x, y = Symbol("x"), Symbol("y")
        f = Implies(x, And(y, Not(x)))

        s = get_free_variables(f)
        self.assertEqual(set([x,y]), s)
