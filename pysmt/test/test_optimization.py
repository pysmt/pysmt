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
from itertools import chain
from pysmt.test import TestCase, skipIfNoOptimizerForLogic
from pysmt.test import main

from pysmt.shortcuts import Optimizer, GE, Int, Symbol, INT, LE, GT, REAL, Real, Equals, Times, Solver, Or, Div
from pysmt.shortcuts import BVType, BVUGE, BVSGE, BVULE, BVSLE, BVUGT, BVSGT, BVULT, BVSLT, BVZero, BVOne, BV
from pysmt.shortcuts import And, Plus, Minus, get_env
from pysmt.logics import QF_LIA, QF_LRA, QF_BV, QF_NRA, QF_NIA
from pysmt.optimization.goal import MaximizationGoal, MinimizationGoal, \
    MinMaxGoal, MaxMinGoal, MaxSMTGoal

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
    def test_maxmin_basic_lia(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        z = Symbol("z", INT)

        f11 = GE(x, Int(5))
        f12 = LE(x, Int(8))
        f21 = GE(y, Int(11))
        f22 = LE(y, Int(14))
        f31 = GE(z, Int(15))
        f32 = LE(z, Int(18))

        maxmin = MaxMinGoal([x, y, z])

        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(f11)
                opt.add_assertion(f12)

                opt.add_assertion(f21)
                opt.add_assertion(f22)

                opt.add_assertion(f31)
                opt.add_assertion(f32)

                model, cost = opt.optimize(maxmin)
                self.assertEqual(model[maxmin.term()], Int(8))

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_minmax_basic_lia(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        z = Symbol("z", INT)

        f11 = GE(x, Int(5))
        f12 = LE(x, Int(8))
        f21 = GE(y, Int(11))
        f22 = LE(y, Int(14))
        f31 = GE(z, Int(15))
        f32 = LE(z, Int(18))

        minmax = MinMaxGoal([x, y, z])

        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(f11)
                opt.add_assertion(f12)

                opt.add_assertion(f21)
                opt.add_assertion(f22)

                opt.add_assertion(f31)
                opt.add_assertion(f32)

                model, cost = opt.optimize(minmax)
                self.assertEqual(model[minmax.term()], Int(15))

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_maxmin_basic_lra(self):
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)
        z = Symbol("z", REAL)

        f11 = GE(x, Real(5.0))
        f12 = LE(x, Real(8.0))
        f21 = GE(y, Real(11.0))
        f22 = LE(y, Real(14.0))
        f31 = GE(z, Real(15.0))
        f32 = LE(z, Real(18.0))

        maxmin = MaxMinGoal([x, y, z])

        for oname in get_env().factory.all_optimizers(logic=QF_LRA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(f11)
                opt.add_assertion(f12)

                opt.add_assertion(f21)
                opt.add_assertion(f22)

                opt.add_assertion(f31)
                opt.add_assertion(f32)

                model, cost = opt.optimize(maxmin)
                self.assertEqual(model[maxmin.term()], Real(8.0))

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_minmax_basic_lra(self):
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)
        z = Symbol("z", REAL)

        f11 = GE(x, Real(5.0))
        f12 = LE(x, Real(8.0))
        f21 = GE(y, Real(11.0))
        f22 = LE(y, Real(14.0))
        f31 = GE(z, Real(15.0))
        f32 = LE(z, Real(18.0))

        minmax = MinMaxGoal([x, y, z])

        for oname in get_env().factory.all_optimizers(logic=QF_LRA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(f11)
                opt.add_assertion(f12)

                opt.add_assertion(f21)
                opt.add_assertion(f22)

                opt.add_assertion(f31)
                opt.add_assertion(f32)

                model, cost = opt.optimize(minmax)
                self.assertEqual(model[minmax.term()], Real(15.0))

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_pareto(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        obj1 = MinimizationGoal(Plus(x, y))
        obj2 = MinimizationGoal(Minus(x, y))
        formula = And(GE(x, Int(0)), GE(y, Int(0)), LE(x, Int(10)), LE(y, Int(10)))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(formula)
                models, costs = zip(*opt.pareto_optimize([obj1, obj2]))
                self.assertEqual(len(models), 11)
                self.assertTrue(all(m[x].constant_value() == 0 for m in models))
                self.assertTrue(all(x[0].constant_value() == -x[1].constant_value() for x in costs))

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_pareto_unsat(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        obj1 = MinimizationGoal(Plus(x, y))
        obj2 = MinimizationGoal(Minus(x, y))
        formula = And(GE(x, Int(0)), GE(y, Int(1)), LE(x, Int(10)), LE(y, Int(10)), LE(y, Int(0)))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(formula)
                for x in opt.pareto_optimize([obj1, obj2]):
                    self.assertTrue(False)

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_boxed(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        z = Symbol("z", INT)
        f1 = And(LE(Int(0), x), LE(Int(0), y), LE(Int(0), z))
        f2 = And(LE(x, Int(10)), LE(y, Int(10)), LE(z, Int(10)))
        obj1 = MinimizationGoal(Minus(x, y))
        obj2 = MinimizationGoal(Minus(y, x))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(f1)
                opt.add_assertion(f2)
                models = opt.boxed_optimize([obj1, obj2])
                self.assertEqual(len(models), 2)
                self.assertEqual(models[obj1][0].get_py_value(x), 0)
                self.assertEqual(models[obj1][0].get_py_value(y), 10)
                self.assertEqual(models[obj2][0].get_py_value(x), 10)
                self.assertEqual(models[obj2][0].get_py_value(y), 0)

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_boxed_unsat(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        z = Symbol("z", INT)
        f1 = And(LE(Int(0), x), LE(Int(0), y), LE(Int(1), z))
        f2 = And(LE(x, Int(10)), LE(y, Int(10)), LE(z, Int(10)), LE(z, Int(0)))
        obj1 = MinimizationGoal(Minus(x, y))
        obj2 = MinimizationGoal(Minus(y, x))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(f1)
                opt.add_assertion(f2)
                models = opt.boxed_optimize([obj1, obj2])
                self.assertTrue(models is None)

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_lex(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        z = Symbol("z", INT)
        t = Symbol("t", INT)
        u = Symbol("u", INT)
        f1 = And(LE(Int(0), x), LE(Int(0), y), LE(Int(0), z), LE(Int(0), u), LE(Int(0), t))
        f2 = And(LE(x, Int(5)), LE(y, Int(5)), LE(z, Int(5)), LE(u, Int(5)), LE(t, Int(5)))
        obj1 = MaximizationGoal(x)
        obj2 = MinimizationGoal(y)
        obj3 = MaximizationGoal(Plus(x, y, z))
        obj4 = MinimizationGoal(t)
        obj5 = MinimizationGoal(u)
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(f1)
                opt.add_assertion(f2)
                model, values = opt.lexicographic_optimize([obj1, obj2, obj3, obj4, obj5])
                self.assertEqual(values[0], Int(5))
                self.assertEqual(values[1], Int(0))
                self.assertEqual(values[2], Int(10))

    def test_lex_unsat(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        z = Symbol("z", INT)
        t = Symbol("t", INT)
        u = Symbol("u", INT)
        f1 = And(LE(Int(0), x), LE(Int(0), y), LE(Int(0), z), LE(Int(0), u), LE(Int(0), t), LE(t, Int(-1)))
        f2 = And(LE(x, Int(5)), LE(y, Int(5)), LE(z, Int(5)), LE(u, Int(5)), LE(t, Int(5)))
        obj1 = MaximizationGoal(x)
        obj2 = MinimizationGoal(y)
        obj3 = MaximizationGoal(Plus(x, y, z))
        obj4 = MinimizationGoal(t)
        obj5 = MinimizationGoal(u)
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(f1)
                opt.add_assertion(f2)
                res = opt.lexicographic_optimize([obj1, obj2, obj3, obj4, obj5])
                self.assertIsNone(res)

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_unsat(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        z = Symbol("z", INT)
        f1 = And(LE(Int(0), x), LE(Int(0), y), LE(Int(1), z))
        f2 = And(LE(x, Int(10)), LE(y, Int(10)), LE(z, Int(10)), LE(z, Int(0)))
        obj1 = MinimizationGoal(Minus(x, y))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                    opt.add_assertion(f1)
                    opt.add_assertion(f2)
                    rt = opt.optimize(obj1)
                    self.assertTrue(rt is None)

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_unbounded(self):
        x = Symbol("x", INT)
        formula = LE(x, Int(10))
        min = MinimizationGoal(x)
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                if opt.can_diverge_for_unbounded_cases():
                    continue
                opt.add_assertion(formula)
                with self.assertRaises(PysmtUnboundedOptimizationError):
                    opt.optimize(min)

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_can_diverge_for_unbounded_cases(self):
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                if not opt.can_diverge_for_unbounded_cases():
                    self.assertIn(oname, ["optimsat", "z3"])

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_infinitesimal(self):
        x = Symbol("x", REAL)
        formula = GT(x, Real(10))
        min = MinimizationGoal(x)
        for oname in get_env().factory.all_optimizers(logic=QF_LRA):
            with Optimizer(name=oname) as opt:
                if opt.can_diverge_for_unbounded_cases():
                    continue
                opt.add_assertion(formula)
                with self.assertRaises(PysmtUnboundedOptimizationError):
                    opt.optimize(min)

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_use_case_001(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)
        z = Symbol("z", INT)
        t = Symbol("t", INT)
        u = Symbol("u", INT)
        f1 = And(LE(Int(0), x), LE(Int(0), y), LE(Int(0), z), LE(Int(0), u), LE(Int(0), t))
        f2 = And(LE(x, Int(5)), LE(y, Int(5)), LE(z, Int(5)), LE(u, Int(5)), LE(t, Int(5)))
        obj1 = MaximizationGoal(x)
        obj2 = MinimizationGoal(y)
        obj3 = MaximizationGoal(Plus(x, y, z))
        obj4 = MinimizationGoal(t)
        obj5 = MinimizationGoal(u)
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(f1)
                opt.add_assertion(f2)
                model, values = opt.lexicographic_optimize([obj1, obj2, obj3, obj4, obj5])
                self.assertEqual(values[0], Int(5))
                self.assertEqual(values[1], Int(0))
                self.assertEqual(values[2], Int(10))

    def test_minimization_basic_BV(self):
        x = Symbol("x", BVType(32))
        min = MinimizationGoal(x)
        formula = BVSGT(x, BV(10, 32))
        for oname in get_env().factory.all_optimizers(logic=QF_BV):
            with Optimizer(name=oname, logic=QF_BV) as opt:
                opt.add_assertion(formula)
                model, cost = opt.optimize(min)
                self.assertEqual(model[x], BV(11, 32))

    def test_maximization_basic_BV(self):
        x = Symbol("x", BVType(32))
        max = MaximizationGoal(x, signed = True)
        formula = BVSLT(x, BV(10, 32))
        for oname in get_env().factory.all_optimizers(logic=QF_BV):
            with Optimizer(name=oname, logic=QF_BV) as opt:
                opt.add_assertion(formula)
                model, cost = opt.optimize(max)
                self.assertEqual(model[x], BV(9, 32))

    def test_maxmin_basic_BV(self):
        x = Symbol("x", BVType(32))
        y = Symbol("y", BVType(32))
        z = Symbol("z", BVType(32))

        f11 = BVSGE(x, BV(5,32))
        f12 = BVSLE(x, BV(8,32))
        f21 = BVSGE(y, BV(11,32))
        f22 = BVSLE(y, BV(14,32))
        f31 = BVSGE(z, BV(15,32))
        f32 = BVSLE(z, BV(18,32))

        maxmin = MaxMinGoal([x, y, z])

        for oname in get_env().factory.all_optimizers(logic=QF_BV):
            with Optimizer(name=oname, logic=QF_BV) as opt:
                opt.add_assertion(f11)
                opt.add_assertion(f12)

                opt.add_assertion(f21)
                opt.add_assertion(f22)

                opt.add_assertion(f31)
                opt.add_assertion(f32)

                model, cost = opt.optimize(maxmin)
                self.assertEqual(model[maxmin.term()], BV(8, 32))

    def test_minmax_basic_BV(self):
        x = Symbol("x", BVType(32))
        y = Symbol("y", BVType(32))
        z = Symbol("z", BVType(32))

        f11 = BVSGE(x, BV(5, 32))
        f12 = BVSLE(x, BV(8, 32))
        f21 = BVSGE(y, BV(11, 32))
        f22 = BVSLE(y, BV(14, 32))
        f31 = BVSGE(z, BV(15, 32))
        f32 = BVSLE(z, BV(18, 32))

        minmax = MinMaxGoal([x, y, z])

        for oname in get_env().factory.all_optimizers(logic=QF_BV):
            with Optimizer(name=oname, logic=QF_BV) as opt:
                opt.add_assertion(f11)
                opt.add_assertion(f12)

                opt.add_assertion(f21)
                opt.add_assertion(f22)

                opt.add_assertion(f31)
                opt.add_assertion(f32)

                model, cost = opt.optimize(minmax)
                self.assertEqual(model[minmax.term()], BV(15, 32))

    def test_maxsmt_basic(self):
        x = Symbol("x", INT)
        maxsmt = MaxSMTGoal()
        maxsmt.add_soft_clause(GE(x, Int(5)), 8)
        maxsmt.add_soft_clause(GE(x, Int(30)), 20)
        maxsmt.add_soft_clause(LE(x, Int(10)), 100)
        maxsmt.add_soft_clause(LE(x, Int(9)), 6)
        formula = GE(x, Int(9))
        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            with Optimizer(name=oname) as opt:
                opt.add_assertion(formula)
                model, cost = opt.optimize(maxsmt)
                self.assertEqual(model[x], Int(9))

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_box_volume(self):
        length = Symbol("length", REAL)
        width = Symbol("width", REAL)
        height = Symbol("height", REAL)
        volume = Symbol("volume", REAL)

        height_times_2 = Times(height, Real(2.0))

        length_value = Minus(Real(36.0), height_times_2)
        width_value = Minus(Real(24.0), height_times_2)
        # length_value = Real(36.0)
        # width_value = Real(24.0)
        # volume_value = Times(length, width, height)
        # switch to sum in order to have a linear problem
        volume_value = Plus(length, width, height)

        length_formula = Equals(length, length_value)
        width_formula = Equals(width, width_value)
        volume_formula = Equals(volume, volume_value)

        positive_length = GE(length, Real(0.0))
        positive_width = GE(width, Real(0.0))
        positive_height = GE(height, Real(0.0))

        # extra_ass = [GE(height, Real(1.0)), LE(height, Real(4.0))]
        # extra_ass = [Or(GE(height, Real(1.0)), LE(height, Real(2.0)), Equals(height, Real(1.0)), Equals(height, Real(3.5)), Equals(height, Real(10)))]
        # extra_ass = [Or(Equals(height, Real(2.0)), Equals(height, Real(1.0)), Equals(height, Real(3.5)), Equals(height, Real(10)))]

        assertions = [length_formula, width_formula, volume_formula, positive_length, positive_width, positive_height] # + extra_ass

        maximize_volume_goal = MaximizationGoal(volume)

        # for oname in get_env().factory.all_solvers(logic=QF_NRA):
        #     # test only z3 for now
        #     if oname != "z3":
        #         continue
        #     with Solver(name=oname) as opt:
        #         for assertion in assertions:
        #             opt.add_assertion(assertion)
        #         print(oname)
        #         retval = opt.solve()
        #         self.assertIsNotNone(retval)
        #         print(type(retval))
        #         print(retval)
        #         print(opt.get_model())

        # WORKING TEST
        # for oname in get_env().factory.all_optimizers(logic=QF_LRA):
        #     # if oname != "z3":
        #     #     continue
        #     with Optimizer(name=oname) as opt:
        #         for assertion in assertions:
        #             opt.add_assertion(assertion)
        #         print(oname)
        #         retval = opt.optimize(maximize_volume_goal)
        #         self.assertIsNotNone(retval)
        #         print(type(retval))
        #         print(retval)
        #         if retval is not None:
        #             model, cost = retval
        #             self.assertTrue(model[volume] in {Real(60.0), Int(60)})
        #             # print(type(cost))
        #             # self.assertEqual(model[volume], cost)

        # as a second objective, maximize y, with y inversely proportional to the volume
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)

        line_1_constraint = Equals(x, y)
        # Commented to make it linear, but this removes the connection between the first objective and the second one
        # line_2_constraint = Equals(y, Minus(Real(10.0), Div(x, volume)))
        line_2_constraint = Equals(y, Minus(Real(10.0), Div(x, Real(60.0))))

        multiple_objective_assertions = [line_1_constraint, line_2_constraint]

        maximize_y_goal = MaximizationGoal(y)

        for oname in get_env().factory.all_solvers(logic=QF_NRA):
            # test only z3 for now
            # if oname != "z3":
            #     continue
            with Solver(name=oname) as opt:
                for assertion in chain(assertions, multiple_objective_assertions):
                    opt.add_assertion(assertion)
                print(oname)
                retval = opt.solve()
                self.assertIsNotNone(retval)
                print(type(retval))
                print(retval)
                print(opt.get_model())

        for oname in get_env().factory.all_optimizers(logic=QF_LRA):
            if oname == "z3":
                continue
            with Optimizer(name=oname) as opt:
                for assertion in chain(assertions, multiple_objective_assertions):
                    opt.add_assertion(assertion)
                print(oname)
                retval = opt.lexicographic_optimize([maximize_volume_goal, maximize_y_goal])
                self.assertIsNotNone(retval)
                print(type(retval))
                print(retval)
                if retval is not None:
                    model, cost = retval
                    print(cost)
                    self.assertTrue(model[volume] in {Real(60.0), Int(60)})
                    self.assertEquals(model[y].constant_value(), Fraction(600, 61))
                    # self.assertEqual(model[y], Real(600/61))
                    # self.assertEqual(model[volume], cost)
                # model, cost = opt.optimize(goal)

        assert False

    @skipIfNoOptimizerForLogic(QF_NIA)
    def test_maximize_revenue(self):
        cost_per_rented_car = Symbol("cost_per_rented_car", INT)
        numbers_of_car_rented = Symbol("numbers_of_car_rented", INT)
        revenue = Symbol("renevue", INT)

        numbers_of_car_rented_value = Minus(Int(1000), Times(Int(5), cost_per_rented_car))
        revenue_value = Times(cost_per_rented_car, numbers_of_car_rented)

        cost_per_rented_car_boundaries = And(GE(cost_per_rented_car, Int(50)), LE(cost_per_rented_car, Int(200)))
        numbers_of_car_rented_formula = Equals(numbers_of_car_rented, numbers_of_car_rented_value)
        revenue_formula = Equals(revenue, revenue_value)

        maximize_revenue_goal = MaximizationGoal(revenue)

        assertions = [cost_per_rented_car_boundaries, numbers_of_car_rented_formula, revenue_formula]

        # for oname in get_env().factory.all_solvers(logic=QF_NRA):
        #     # test only z3 for now
        #     if oname != "z3":
        #         continue
        #     with Solver(name=oname) as opt:
        #         for assertion in assertions:
        #             opt.add_assertion(assertion)
        #         print(oname)
        #         retval = opt.solve()
        #         self.assertIsNotNone(retval)
        #         print(type(retval))
        #         print(retval)
        #         print(opt.get_model())

        # WORKING TEST
        # for oname in get_env().factory.all_optimizers(logic=QF_NIA):
        #     # if oname != "z3":
        #     #     continue
        #     with Optimizer(name=oname) as opt:
        #         for assertion in assertions:
        #             opt.add_assertion(assertion)
        #         retval = opt.optimize(maximize_revenue_goal)
        #         self.assertIsNotNone(retval)
        #         if retval is not None:
        #             model, cost = retval
        #             self.assertEqual(cost, Int(50000))

        # multiple objective optimization

        length = Symbol("length", INT)
        width = Symbol("width", INT)
        area = Symbol("area", INT)
        perimeter = Symbol("perimeter", INT)

        area_value = Times(length, width)
        perimeter_value = Times(Plus(length, width), Int(2))

        area_formula = Equals(area, area_value)
        perimeter_formula = Equals(perimeter, perimeter_value)

        perimeter_boundaries = LE(perimeter, cost_per_rented_car)

        set_cost_per_rented_car_to_100 = Equals(cost_per_rented_car, Int(100))
        multiple_objective_optimization_assertions = [area_formula, perimeter_formula, perimeter_boundaries]

        maximize_area_goal = MaximizationGoal(area)

        # test_part_2 of problem
        for oname in get_env().factory.all_optimizers(logic=QF_NIA):
            # if oname == "z3":
            #     continue
            with Optimizer(name=oname) as opt:
                print(oname)
                for assertion in chain([set_cost_per_rented_car_to_100], multiple_objective_optimization_assertions):
                    opt.add_assertion(assertion)
                retval = opt.optimize(maximize_area_goal)
                self.assertIsNotNone(retval)
                if retval is not None:
                    model, cost = retval
                    print(model)
                    print(cost)
                    self.assertEqual(cost, Int(50000))

        # currently commented for efficiency
        # lexicographic optimize
        # for oname in get_env().factory.all_optimizers(logic=QF_NIA):
        #     # if oname == "z3":
        #     #     continue
        #     with Optimizer(name=oname) as opt:
        #         print(oname)
        #         for assertion in chain(assertions, multiple_objective_optimization_assertions):
        #             opt.add_assertion(assertion)
        #         retval = opt.lexicographic_optimize([maximize_revenue_goal, maximize_area_goal])
        #         self.assertIsNotNone(retval)
        #         if retval is not None:
        #             model, cost = retval
        #             print(model)
        #             print(cost)
        #             self.assertEqual(cost, Int(50000))

        assert False

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_simple_multiple_optimization(self):
        x = Symbol("x", INT)
        y = Symbol("y", INT)

        int_0, int_3 = Int(0), Int(3)

        x_boundaries = And(GE(x, int_0), LE(x, int_3))
        y_boundaries = And(GE(y, int_0), LE(y, int_3))

        x_y_bound = Equals(Plus(x, y), int_3)

        assertions = [x_boundaries, y_boundaries, x_y_bound]

        maximize_x = MaximizationGoal(x)
        maximize_y = MaximizationGoal(y)

        for oname in get_env().factory.all_optimizers(logic=QF_LIA):
            # if oname != "z3":
            #     continue
            with Optimizer(name=oname) as opt:
                for assertion in assertions:
                    opt.add_assertion(assertion)
                retval = opt.lexicograpic_optimize([maximize_x, maximize_y])
                self.assertIsNotNone(retval)
                if retval is not None:
                    model, _ = retval
                    self.assertEqual(model[x]



if __name__ == '__main__':
    main()
