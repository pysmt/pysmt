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
from pysmt.test import TestCase, skipIfNoOptimizerForLogic
from pysmt.test import main

from pysmt.shortcuts import Optimizer, GE, Int, Symbol, INT, LE, GT, REAL, Real
from pysmt.logics import QF_LIA, QF_LRA

from pysmt.exceptions import PysmtUnboundedOptimizationError

class TestOptimization(TestCase):

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_basic(self):
        x = Symbol("x", INT)
        formula = GE(x, Int(10))
        with Optimizer(logic=QF_LIA) as opt:
            opt.add_assertion(formula)
            model = opt.optimize(x)
            self.assertEqual(model[x], Int(10))

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_unbounded(self):
        x = Symbol("x", INT)
        formula = LE(x, Int(10))
        with Optimizer(logic=QF_LIA) as opt:
            opt.add_assertion(formula)
            with self.assertRaises(PysmtUnboundedOptimizationError):
                opt.optimize(x)

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_infinitesimal(self):
        x = Symbol("x", REAL)
        formula = GT(x, Real(10))
        with Optimizer(logic=QF_LRA) as opt:
            opt.add_assertion(formula)
            with self.assertRaises(PysmtUnboundedOptimizationError):
                opt.optimize(x)


if __name__ == '__main__':
    main()
