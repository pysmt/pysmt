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
from pysmt.shortcuts import And, Plus, Minus, get_env
from pysmt.logics import QF_LIA, QF_LRA
from pysmt.optimization.goal import MaximizationGoal, MinimizationGoal

from pysmt.exceptions import PysmtUnboundedOptimizationError

class TestOptimization(TestCase):

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_minimization_basic(self):
        x = Symbol("x", INT)
        min = MinimizationGoal(x)
        formula = GE(x, Int(10))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(formula)
                model, cost = opt.optimize(min)
                self.assertEqual(model[x], Int(10))
                self.assertEqual(cost, Int(10))

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_maximization_basic(self):
        x = Symbol("x", INT)
        max = MaximizationGoal(x)
        formula = LE(x, Int(10))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(formula)
                model, cost = opt.optimize(max)
                self.assertEqual(model[x], Int(10))

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_unbounded(self):
        x = Symbol("x", INT)
        min = MinimizationGoal(x)
        formula = LE(x, Int(10))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                if opt.can_diverge_for_unbounded_cases():
                    continue
                opt.add_assertion(formula)
                with self.assertRaises(PysmtUnboundedOptimizationError):
                    opt.optimize(min)

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_infinitesimal(self):
        x = Symbol("x", REAL)
        min = MinimizationGoal(x)
        formula = GT(x, Real(10))
        for oname in get_env().factory.all_optimizers(logic=QF_LRA):
            with Optimizer(name=oname) as opt:
                if opt.can_diverge_for_unbounded_cases():
                    continue
                opt.add_assertion(formula)
                with self.assertRaises(PysmtUnboundedOptimizationError):
                    opt.optimize(min)

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_pareto(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        formula = And(GE(x, Int(0)), GE(y, Int(0)), LE(x, Int(10)), LE(y, Int(10)))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                try:
                    opt.add_assertion(formula)
                    models, costs = zip(*opt.pareto_optimize([Plus(x, y), Minus(x, y)]))
                    self.assertEqual(len(models), 11)
                    self.assertTrue(all(m[x].constant_value() == 0 for m in models))
                    self.assertTrue(all(x[0].constant_value() == -x[1].constant_value() for x in costs))
                except NotImplementedError:
                    pass # OptiMathSAT wrapping of pareto is incomplete

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_unbounded(self):
        x = Symbol("x", INT)
        formula = LE(x, Int(10))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                if opt.can_diverge_for_unbounded_cases():
                    continue
                opt.add_assertion(formula)
                with self.assertRaises(PysmtUnboundedOptimizationError):
                    opt.optimize(x)

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_infinitesimal(self):
        x = Symbol("x", REAL)
        formula = GT(x, Real(10))
        for oname in get_env().factory.all_optimizers(logic=QF_LRA):
            with Optimizer(name=oname) as opt:
                if opt.can_diverge_for_unbounded_cases():
                    continue
                opt.add_assertion(formula)
                with self.assertRaises(PysmtUnboundedOptimizationError):
                    opt.optimize(x)

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_pareto(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        formula = And(GE(x, Int(0)), GE(y, Int(0)), LE(x, Int(10)), LE(y, Int(10)))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                try:
                    opt.add_assertion(formula)
                    models = list(opt.pareto_optimize([Plus(x, y), Minus(x, y)]))
                    self.assertEqual(len(models), 11)
                    self.assertTrue(all(m[x].constant_value() == 0 for m in models))
                except NotImplementedError:
                    pass # OptiMathSAT wrapping of pareto is incomplete

if __name__ == '__main__':
    main()
