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

from __future__ import absolute_import

from fractions import Fraction
from warnings import warn

from pysmt.decorators import clear_pending_pop
from pysmt.solvers.z3 import Z3Solver, Z3Model

from pysmt.exceptions import PysmtInfinityError, \
    PysmtUnboundedOptimizationError, PysmtInfinitesimalError, \
    SolverAPINotFound, GoalNotSupportedError

from pysmt.optimization.optimizer import Optimizer, \
    SUAOptimizerMixin, IncrementalOptimizerMixin

try:
    import z3
except ImportError:
    raise SolverAPINotFound


class Z3NativeOptimizer(Optimizer, Z3Solver):
    # remove all theories that are not linear
    LOGICS = set(filter(lambda x: x.theory.linear, Z3Solver.LOGICS))

    def __init__(self, environment, logic, **options):
        Z3Solver.__init__(self, environment=environment,
                          logic=logic, **options)
        self.z3 = z3.Optimize()

    def _assert_z3_goal(self, goal, goal_id = None):
        h = None
        if goal.is_maxsmt_goal():
            assert goal_id is not None
            for soft, w in goal.soft:
                obj_soft = self.converter.convert(soft)
                w = w.constant_value()
                if isinstance(w, Fraction):
                    w = float(w)
                h = self.z3.add_soft(obj_soft, w, "__pysmt_" + str(goal_id))
        else:
            term = goal.term()
            ty = self.environment.stc.get_type(term)
            if goal.signed and ty.is_bv_type():
                width = ty.width
                term = self.mgr.BVAdd(term, self.mgr.BV(2**(width-1), width))
            obj = self.converter.convert(term)
            if goal.is_minimization_goal():
                h = self.z3.minimize(obj)
            elif goal.is_maximization_goal():
                h = self.z3.maximize(obj)
            else:
                raise GoalNotSupportedError(self, goal)
        return  h

    @clear_pending_pop
    def optimize(self, goal, **kwargs):
        self.push()
        try:
            h = self._assert_z3_goal(goal, 0)

            res = self.z3.check()
            if res == z3.sat:
                try:
                    if goal.is_maxsmt_goal():
                        model = Z3Model(self.environment, self.z3.model())
                        return model, self._compute_max_smt_cost(model, goal)
                    else:
                        opt_value = self.z3.lower(h)
                        self.converter.back(opt_value)
                        model = Z3Model(self.environment, self.z3.model())
                        return model, model.get_value(goal.term())
                except PysmtInfinityError:
                    raise PysmtUnboundedOptimizationError("The optimal value is unbounded")
                except PysmtInfinitesimalError:
                    raise PysmtInfinitesimalError("The optimal value is infinitesimal")
            else:
                return None
        finally:
            self.pop()

    @clear_pending_pop
    def pareto_optimize(self, goals):
        self._check_pareto_lexicographic_goals(goals, "pareto")
        self.push()
        try:
            self.z3.set(priority='pareto')
            for goal in goals:
                self._assert_z3_goal(goal)
            while self.z3.check() == z3.sat:
                model = Z3Model(self.environment, self.z3.model())
                yield model, [model.get_value(x.term()) for x in goals]
        finally:
            self.pop()

    def can_diverge_for_unbounded_cases(self):
        return False

    @clear_pending_pop
    def boxed_optimize(self, goals):
        # This implementation is a naive simulation of a box optimization,
        # but is needed to cope with an upstream Z3 issue:
        # https://github.com/Z3Prover/z3/issues/7240
        #
        # A properer implementation would be as follows.
        # '''python
        # self.z3.set(priority='box')
        # models = {}
        # for goal_id, goal in enumerate(goals):
        #     self._assert_z3_goal(goal, goal_id)
        # for goal in goals:
        #     if self.z3.check() == z3.sat:
        #         model = Z3Model(self.environment, self.z3.model())
        #         models[goal] = (model, model.get_value(goal.term()))
        #     else:
        #         return None
        # return models
        # '''
        warn("Boxed optimization is not working in Z3 (see https://github.com/Z3Prover/z3/issues/7240). "
             "PySMT will simulate the correct behavior, but the performance will be sub-optimal")
        models = {}
        for g in goals:
            r = self.optimize(g)
            if r is None:
                return None
            models[g] = r
        return models

    @clear_pending_pop
    def lexicographic_optimize(self, goals):
        self._check_pareto_lexicographic_goals(goals, "lexicographic")
        self.push()
        try:
            self.z3.set(priority='lex')
            for goal in goals:
                self._assert_z3_goal(goal)

            if self.z3.check() == z3.sat:
                model = Z3Model(self.environment, self.z3.model())
                costs = []
                for goal in goals:
                    if goal.is_maxsmt_goal():
                        costs.append(self._compute_max_smt_cost(model, goal))
                    else:
                        costs.append(model.get_value(goal.term()))
                return model, costs
            else:
                return None
        finally:
            self.pop()


class Z3SUAOptimizer(Z3Solver, SUAOptimizerMixin):
    def can_diverge_for_unbounded_cases(self):
        return True


class Z3IncrementalOptimizer(Z3Solver, IncrementalOptimizerMixin):
    def can_diverge_for_unbounded_cases(self):
        return True
