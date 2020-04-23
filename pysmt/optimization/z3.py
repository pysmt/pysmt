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

from pysmt.solvers.z3 import Z3Solver, Z3Model

from pysmt.exceptions import PysmtInfinityError, \
    PysmtUnboundedOptimizationError, PysmtInfinitesimalError, \
    SolverAPINotFound

from pysmt.optimization.optimizer import Optimizer, \
    SUAOptimizerMixin, IncrementalOptimizerMixin

try:
    import z3
except ImportError:
    raise SolverAPINotFound


class Z3NativeOptimizer(Optimizer, Z3Solver):
    LOGICS = Z3Solver.LOGICS

    def __init__(self, environment, logic, **options):
        Z3Solver.__init__(self, environment=environment,
                          logic=logic, **options)
        print(z3.__file__)
        self.z3 = z3.Optimize()

    def optimize(self, cost_function, **kwargs):
        obj = self.converter.convert(cost_function)
        h = self.z3.minimize(obj)
        res = self.z3.check()
        if res == z3.sat:
            opt_value = self.z3.lower(h)
            try:
                self.converter.back(opt_value)
                model = Z3Model(self.environment, self.z3.model())
                return model, model.get_value(cost_function)
            except PysmtInfinityError:
                raise PysmtUnboundedOptimizationError("The optimal value is unbounded")
            except PysmtInfinitesimalError:
                raise PysmtUnboundedOptimizationError("The optimal value is infinitesimal")
        else:
            return None

    def pareto_optimize(self, cost_functions):
        self.z3.set(priority='pareto')
        criteria = []
        for cf in cost_functions:
            obj = self.converter.convert(cf)
            criteria.append(self.z3.minimize(obj))

        while self.z3.check() == z3.sat:
            model = Z3Model(self.environment, self.z3.model())
            yield model, [model.get_value(x) for x in cost_functions]

    def can_diverge_for_unbounded_cases(self):
        return False

    def can_diverge_for_unbounded_cases(self):
        return False


class Z3SUAOptimizer(Z3Solver, SUAOptimizerMixin):
    LOGICS = Z3Solver.LOGICS


class Z3IncrementalOptimizer(Z3Solver, IncrementalOptimizerMixin):
    LOGICS = Z3Solver.LOGICS
