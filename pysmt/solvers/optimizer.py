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

from pysmt.solvers.solver import Solver
from pysmt.exceptions import PysmtValueError

class Optimizer(Solver):
    """
    Interface for the optimization
    """

    def optimize(self, cost_function):
        """Returns a model object that minimizes the value of `cost_function`
        while satisfying all the formulae asserted in the optimizer.

        `cost_function` must be a term with integer, real or
        bit-vector type whose value has to be minimized

        This function can raise a PysmtUnboundedOptimizationError if
        the solver detects that the optimum value is either positive
        or negative infinite or if there is no optimum value because
        one can move arbitrarily close to the optimum without reching
        it (e.g. "x > 5" has no minimum for x, only an infimum)
        """
        raise NotImplementedError


    def pareto_optimize(self, cost_functions):
        """This function is a generator returning *all* the pareto-optimal
        solutions for the problem of minimizing the `cost_functions`
        keeping the formulae asserted in this optimizer satisfied.

        `cost_functions` must be a list of terms with integer, real or
        bit-vector types whose values have to be minimized

        This function can raise a PysmtUnboundedOptimizationError if
        the solver detects that the optimum value is either positive
        or negative infinite or if there is no optimum value because
        one can move arbitrarily close to the optimum without reching
        it (e.g. "x > 5" has no minimum for x, only an infimum)

        """
        raise NotImplementedError

    def can_diverge_for_unbounded_cases(self):
        """This function returns True if the algorithm implemented in this
        optimizer can diverge (i.e. not terminate) if the objective is
        unbounded (infinite or infinitesimal).
        """
        raise NotImplementedError

    def _comparation_functions(self, objective_formula):
        """Internal utility function to get the proper LT and LE function for
        the given objective formula
        """
        otype = self.environment.stc.get_type(objective_formula)
        mgr = self.environment.formula_manager
        if otype.is_int_type() or otype.is_real_type():
            return mgr.LT, mgr.LE
        elif otype.is_bv_type():
            return mgr.BVULT, mgr.BVULE
        else:
            raise PysmtValueError("Invalid optimization function type: %s" % otype)



class SUAOptimizerMixin(Optimizer):
    """Optimizer mixin using solving under assumptions"""

    def optimize(self, cost_function):
        last_model = None
        optimum_found = True

        lt, _ = self._comparation_functions(cost_function)

        cost_so_far = None
        while optimum_found:
            if cost_so_far is not None:
                k = lt(cost_function, cost_so_far)
                optimum_found = self.solve(assumptions=[k])
            else:
                optimum_found = self.solve()

            if optimum_found:
                last_model = self.get_model()
                cost_so_far = self.get_value(cost_function)
        return last_model

    def pareto_optimize(self, cost_functions):
        mgr = self.environment.formula_manager

        lts, les = zip(*(self._comparation_functions(x) for x in cost_functions))

        eliminated = []
        terminated = False
        while not terminated:
            last_model = None
            optimum_found = True
            costs_so_far = None
            while optimum_found:
                if costs_so_far is not None:
                    k = [les[i](cost_functions[i], costs_so_far[i])
                         for i in range(len(cost_functions))]
                    k.append(mgr.Or(lts[i](cost_functions[i], costs_so_far[i])
                                    for i in range(len(cost_functions))))
                    optimum_found = self.solve(assumptions=eliminated + k)
                else:
                    optimum_found = self.solve(assumptions=eliminated)

                if optimum_found:
                    last_model = self.get_model()
                    costs_so_far = []
                    for i in range(len(cost_functions)):
                        costs_so_far.append(self.get_value(cost_functions[i]))
            if last_model is not None:
                yield last_model
                eliminated.append(mgr.Or(lts[i](cost_functions[i],
                                                  last_model[cost_functions[i]])
                                         for i in range(len(cost_functions))))
            else:
                terminated = True

    def can_diverge_for_unbounded_cases(self):
        return True



class IncrementalOptimizerMixin(Optimizer):
    """Optimizer mixin using the incremental interface"""

    def optimize(self, cost_function):
        last_model = None
        optimum_found = False

        self.push()

        lt, _ = self._comparation_functions(cost_function)

        cost_so_far = None
        while not optimum_found:
            if cost_so_far is not None:
                self.add_assertion(lt(cost_function, cost_so_far))
            optimum_found = not self.solve()

            if not optimum_found:
                last_model = self.get_model()
                cost_so_far = self.get_value(cost_function)
        self.pop()
        return last_model

    def pareto_optimize(self, cost_functions):
        mgr = self.environment.formula_manager

        lts, les = zip(*(self._comparation_functions(x) for x in cost_functions))

        terminated = False
        self.push()
        while not terminated:
            last_model = None
            optimum_found = False
            costs_so_far = None
            self.push()
            while not optimum_found:
                if costs_so_far is not None:
                    for i in range(len(cost_functions)):
                        self.add_assertion(les[i](cost_functions[i],
                                                  costs_so_far[i]))
                    self.add_assertion(mgr.Or(lts[i](cost_functions[i],
                                                     costs_so_far[i])
                                              for i in range(len(cost_functions))))
                optimum_found = not self.solve()

                if not optimum_found:
                    last_model = self.get_model()
                    costs_so_far = []
                    for i in range(len(cost_functions)):
                        costs_so_far.append(self.get_value(cost_functions[i]))

            self.pop()
            if last_model is not None:
                yield last_model
                self.add_assertion(mgr.Or(lts[i](cost_functions[i],
                                                   last_model[cost_functions[i]])
                                          for i in range(len(cost_functions))))
            else:
                terminated = True
        self.pop()

    def can_diverge_for_unbounded_cases(self):
        return True
