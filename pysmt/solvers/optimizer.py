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
# from pysmt.exceptions import PysmtValueError
# from pysmt.oracles import get_logic

class Optimizer(Solver):
    """
    Interface for the optimization
    """

    def optimize(self, cost_function, initial_cost=None, callback=None):
        """Returns a model object that minimizes the value of `cost_function`
        while satisfying all the formulae asserted in the optimizer.

        `cost_function` must be a term with integer, real or
        bit-vector type whose value type has to be minimized

        If `initial_cost` is specified, then all values of
        `cost_function` greater this value are discarded from the
        search.

        `callback` is a function taking in input a model object that
        may be called during the search communicating the current best
        model. If, when called, the function returns True the search
        is immediately stopped. This is useful to terminate the search
        in algorithms where termination is not guaranteed or to stop
        the search prematurely when a criterion is met.

        This function can raise a PysmtUnboundedOptimizationError if
        the solver detects that the optimum value is either positive
        or negative infinite or if there is no optimum value because
        one can move arbitrarily close to the optimum without reching
        it (e.g. "x > 5" has no minimum for x, only an infimum)
        """
        raise NotImplementedError


    def pareto_optimize(self, cost_functions, callback=None):
        """This function is a generator returning *all* the pareto-optimal
        solutions for the problem of minimizing the `cost_functions`
        keeping the formulae asserted in this optimizer satisfied.

        `cost_functions` must be a list of terms with integer, real or
        bit-vector types whose values type has to be minimized

        `callback` is a function taking in input a model object that
        may be called during the search communicating the current best
        model. If, when called, the function returns True the search
        is immediately stopped. This is useful to terminate the search
        in algorithms where termination is not guaranteed or to stop
        the search prematurely when a criterion is met.

        This function can raise a PysmtUnboundedOptimizationError if
        the solver detects that the optimum value is either positive
        or negative infinite or if there is no optimum value because
        one can move arbitrarily close to the optimum without reching
        it (e.g. "x > 5" has no minimum for x, only an infimum)

        """
        raise NotImplementedError



class SUAOptimizerMixin(Optimizer):
    """Optimizer mixin using solving under assumptions"""

    def _lt(self, x, y):
        otype = self.environment.stc.get_type(x)
        mgr = self.environment.formula_manager
        if otype.is_int_type() or otype.is_real_type():
            return mgr.LT(x, y)
        elif otype.is_bv_type():
            return mgr.BVULT(x, y)

    def _le(self, x, y):
        otype = self.environment.stc.get_type(x)
        mgr = self.environment.formula_manager
        if otype.is_int_type() or otype.is_real_type():
            return mgr.LE(x, y)
        elif otype.is_bv_type():
            return mgr.BVULE(x, y)

    def optimize(self, cost_function, initial_cost=None, callback=None):
        last_model = None
        keep = True

        initial_assumptions = []
        if initial_cost is not None:
            initial_assumptions.append(self._lt(cost_function, initial_cost))

        cost_so_far = None
        while keep:
            if cost_so_far is not None:
                k = self._lt(cost_function, cost_so_far)
                keep = self.solve(assumptions=[k])
            else:
                keep = self.solve(assumptions=initial_assumptions)

            if keep:
                last_model = self.get_model()
                cost_so_far = self.get_value(cost_function)
                if callback is not None:
                    exit_request = callback(last_model)
                    if exit_request is True:
                        break
        return last_model

    def pareto_optimize(self, cost_functions, callback=None):
        mgr = self.environment.formula_manager

        eliminated = []
        terminated = False
        while not terminated:
            last_model = None
            keep = True
            costs_so_far = None
            while keep:
                if costs_so_far is not None:
                    k = [self._le(cost_functions[i], costs_so_far[i])
                         for i in range(len(cost_functions))]
                    k.append(mgr.Or(self._lt(cost_functions[i], costs_so_far[i])
                                    for i in range(len(cost_functions))))
                    keep = self.solve(assumptions=eliminated + k)
                else:
                    keep = self.solve(assumptions=eliminated)

                if keep:
                    last_model = self.get_model()
                    costs_so_far = []
                    for i in range(len(cost_functions)):
                        costs_so_far.append(self.get_value(cost_functions[i]))
                    if callback is not None:
                        exit_request = callback(last_model)
                        if exit_request is True:
                            break
            if last_model is not None:
                yield last_model
                eliminated.append(mgr.Or(self._lt(cost_functions[i],
                                                  last_model[cost_functions[i]])
                                         for i in range(len(cost_functions))))
            else:
                terminated = True


class IncrementalOptimizerMixin(Optimizer):
    """Optimizer mixin using solving under assumptions"""

    def _lt(self, x, y):
        otype = self.environment.stc.get_type(x)
        mgr = self.environment.formula_manager
        if otype.is_int_type() or otype.is_real_type():
            return mgr.LT(x, y)
        elif otype.is_bv_type():
            return mgr.BVULT(x, y)

    def _le(self, x, y):
        otype = self.environment.stc.get_type(x)
        mgr = self.environment.formula_manager
        if otype.is_int_type() or otype.is_real_type():
            return mgr.LE(x, y)
        elif otype.is_bv_type():
            return mgr.BVULE(x, y)

    def optimize(self, cost_function, initial_cost=None, callback=None):
        last_model = None
        keep = True

        self.push()
        initial_assumptions = []
        if initial_cost is not None:
            self.add_assertion(self._lt(cost_function, initial_cost))

        cost_so_far = None
        while keep:
            if cost_so_far is not None:
                self.add_assertion(self._lt(cost_function, cost_so_far))
            keep = self.solve()

            if keep:
                last_model = self.get_model()
                cost_so_far = self.get_value(cost_function)
                if callback is not None:
                    exit_request = callback(last_model)
                    if exit_request is True:
                        break
        self.pop()
        return last_model

    def pareto_optimize(self, cost_functions, callback=None):
        mgr = self.environment.formula_manager

        terminated = False
        self.push()
        while not terminated:
            last_model = None
            keep = True
            costs_so_far = None
            self.push()
            while keep:
                if costs_so_far is not None:
                    for i in range(len(cost_functions)):
                        self.add_assertion(self._le(cost_functions[i],
                                                    costs_so_far[i]))
                    self.add_assertion(mgr.Or(self._lt(cost_functions[i],
                                                       costs_so_far[i])
                                              for i in range(len(cost_functions))))
                keep = self.solve()

                if keep:
                    last_model = self.get_model()
                    costs_so_far = []
                    for i in range(len(cost_functions)):
                        costs_so_far.append(self.get_value(cost_functions[i]))
                    if callback is not None:
                        exit_request = callback(last_model)
                        if exit_request is True:
                            break
            self.pop()
            if last_model is not None:
                yield last_model
                self.add_assertion(mgr.Or(self._lt(cost_functions[i],
                                                   last_model[cost_functions[i]])
                                          for i in range(len(cost_functions))))
            else:
                terminated = True
        self.pop()
