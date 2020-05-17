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
from pysmt.exceptions import PysmtValueError, GoalNotSupportedError
from pysmt.optimization.goal import MinimizationGoal, MaximizationGoal
from pysmt.shortcuts import Symbol, INT, REAL, BVType

class Optimizer(Solver):
    """
    Interface for the optimization
    """

    def optimize(self, goal, **kwargs):
        """Returns a pair `(model, cost)` where `model` is an object that
        minimizes the value of `cost_function` while satisfying all
        the formulae asserted in the optimizer, while `cost` is the
        objective function value for the model.

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

        The solutions are returned as pairs `(model, costs)` where
        model is the pareto-optimal assignment and costs is the list
        of costs, one for each optimization function in
        `cost_functions`.

        `cost_functions` must be a list of terms with integer, real or
        bit-vector types whose values have to be minimized

        This function can raise a PysmtUnboundedOptimizationError if
        the solver detects that the optimum value is either positive
        or negative infinite or if there is no optimum value because
        one can move arbitrarily close to the optimum without reching
        it (e.g. "x > 5" has no minimum for x, only an infimum)

        """
        raise NotImplementedError

    def _comparation_functions(self, objective_formula):
        """Internal utility function to get the proper cast, LT and LE
        function for the given objective formula
        """
        otype = self.environment.stc.get_type(objective_formula)
        mgr = self.environment.formula_manager
        if otype.is_int_type():
            return mgr.Int, mgr.LT, mgr.LE
        elif otype.is_real_type():
            return mgr.Real, mgr.LT, mgr.LE
        elif otype.is_bv_type():
            return (lambda x: mgr.BV(x, otype.width)), mgr.BVULT, mgr.BVULE
        else:
            raise PysmtValueError("Invalid optimization function type: %s" % otype)

    def can_diverge_for_unbounded_cases(self):
        """This function returns True if the algorithm implemented in this
        optimizer can diverge (i.e. not terminate) if the objective is
        unbounded (infinite or infinitesimal).
        """
        raise NotImplementedError


    def _get_symbol_type(self, objective_formula):
        otype = self.environment.stc.get_type(objective_formula)
        if otype.is_int_type():
            return INT
        elif otype.is_real_type():
            return REAL
        elif otype.is_bv_type():
            return BVType(otype.width)
        else:
            raise PysmtValueError("Invalid optimization function type: %s" % otype)

    def _get_or(self, objective_formula):
        otype = self.environment.stc.get_type(objective_formula)
        mgr = self.environment.formula_manager
        if otype.is_int_type():
            return mgr.Or
        elif otype.is_real_type():
            return mgr.Or
        elif otype.is_bv_type():
            return mgr.BVOr
        else:
            raise PysmtValueError("Invalid optimization function type: %s" % otype)


    def _get_le(self, objective_formula):
        otype = self.environment.stc.get_type(objective_formula)
        mgr = self.environment.formula_manager
        if otype.is_int_type():
            return mgr.LE
        elif otype.is_real_type():
            return mgr.LE
        elif otype.is_bv_type():
            return mgr.BVULE
        else:
            raise PysmtValueError("Invalid optimization function type: %s" % otype)


    def _get_lt(self, objective_formula):
        otype = self.environment.stc.get_type(objective_formula)
        mgr = self.environment.formula_manager
        if otype.is_int_type():
            return mgr.LT
        elif otype.is_real_type():
            return mgr.LT
        elif otype.is_bv_type():
            return mgr.BVULT
        else:
            raise PysmtValueError("Invalid optimization function type: %s" % otype)


class OptSearchInterval():

    def __init__(self, goal, comparation_functions):
        self._obj = goal
        self._lower = None #-INF where i found this costant?
        self._upper = None #+INF
        self._pivot = None
        self._comparation_functions = comparation_functions

    def _make_better_than(self, goal, x, strategy):
        cast, lt, le = self._comparation_functions(goal.term())
        op = le if strategy == "binary" else lt
        if goal.is_minimization_goal():
            t1 = goal.term()
            t2 = x
        else:
            t1 = x
            t2 = goal.term()
        return op(t1, t2)

    def linear_search_cut(self, size_step):
        """must be called always"""
        if self._obj.is_minimization_goal():
            bound = self._upper - size_step
        else:
            bound = self._lower + size_step

        return self._make_better_than(self._obj, bound, "linear")

    def _compute_pivot(self):
        if self._lower is None and self._upper is None:
            return 0
        l,u = self._lower, self._upper
        if self._lower is None and self._upper is not None:
            l = self._upper - (abs(self._upper) + 1)
        elif self._lower is not None and self._upper is None:
            u = self._lower + abs(self._lower) + 1
        return (l + u + 1) // 2

    def binary_search_cut(self):
        """may be skipped"""
        self._pivot = self._compute_pivot()
        return self._make_better_than(self._obj, self._pivot, "binary")


    def empty(self):
        """True: remove this unit from optimization search"""
        if self._upper == None or self._lower == None:
            return False
        return self._upper <= self._lower


    def search_is_sat(self, model):
        self._pivot = None
        model_value = model.get_value(self._obj.term()).constant_value()
        if self._obj.is_minimization_goal():
            if self._upper is None:
                self._upper = model_value
            elif self._upper > model_value:
                self._upper = model_value
        elif self._obj.is_maximization_goal():
            if self._lower is None:
                self._lower = model_value
            elif self._lower < model_value:
                self._lower = model_value
        else:
            pass  # this may happen in boxed multi-independent optimization


    def search_is_unsat(self):
        if self._pivot is not None:
            if self._obj.is_minimization_goal():
                self._lower = self._pivot
            else:
                self._upper = self._pivot
        else:
            if self._obj.is_minimization_goal():
                self._lower = self._upper
            else:
                self._upper = self._lower


class ExternalOptimizerMixin(Optimizer):
    """An optimizer that uses an SMT-Solver externally"""

    def _setup(self):
        raise NotImplementedError

    def _cleanup(self, client_data):
        raise NotImplementedError

    def _pareto_setup(self, client_data):
        raise NotImplementedError

    def _pareto_cleanup(self, client_data):
        raise NotImplementedError

    def _pareto_check_progress(self, client_data, cost_functions,
                               costs_so_far, lts, les):
        raise NotImplementedError

    def _pareto_block_model(self, client_data, cost_functions, last_model, lts, les):
        raise NotImplementedError

    def _optimization_check_progress(self, client_data, cost_function,
                                     cost_so_far, lt, le, strategy):
        raise NotImplementedError

    def _binary_bound(self, lb, ub):
        if lb is None and ub is None:
            return None
        l,u = lb,ub
        if lb is None and ub is not None:
            l = ub - (abs(ub) + 1)
        elif lb is not None and ub is None:
            u = lb + abs(lb) + 1
        return (l + u + 1) // 2

    def _bound(self, lb, ub, strategy, goal):
        if strategy == 'binary':
            return self._binary_bound(lb, ub)
        if strategy == 'linear':
            return ub if goal.is_minimization_goal() else lb
        else:
            raise PysmtValueError("Unknown optimization strategy '%s'" % strategy)

    def optimize(self, goal, strategy='linear',
                 feasible_solution_callback=None,
                 step_size=1, **kwargs):
        """This function performs the optimization as described in
        `Optimizer.optimize()`. However. two additional parameters are
        available:

        `strategy` can be either 'binary' or 'linear'. 'binary' performs a
        binary search to find the optimum, while 'ub' searches among
        the satisfiable models.

        `feasible_solution_callback` is a function with a single
        argument or None. If specified, the function will be called
        each time the algorithm finds a feasible solution. Each call
        is guaranteed to have a better solution quality than the
        previous.

        `step_size` the minimum reolution for finding a solution. The
        optimum will be found in the proximity of `step_size`
        """
        rt = None, None
        if goal.is_maximization_goal() or goal.is_minimization_goal():
            rt = self._optimize(goal, strategy,
                             feasible_solution_callback,
                             step_size, **kwargs)
        else:
            raise GoalNotSupportedError("ExternalOptimizerMixin", goal)
        return rt


    def _optimize(self, goal, strategy,
                 feasible_solution_callback,
                 step_size, **kwargs):

        current = OptSearchInterval(goal, self._comparation_functions)
        first_step = True
        while not current.empty():
            if not first_step:
                if strategy == "linear":
                    lin_assertions = current.linear_search_cut(step_size)
                elif strategy == "binary":
                    lin_assertions = current.binary_search_cut()
                else:
                    raise PysmtValueError("Unknown optimization strategy '%s'" % strategy)
                status = self.solve(assumptions=[lin_assertions])
            else:
                status = self.solve()
                first_step = False
            if status:
                model = self.get_model()
                current.search_is_sat(model)
            else:
                current.search_is_unsat()



    def _optimize_max_min(self, goal, strategy,
                 feasible_solution_callback,
                 step_size, **kwargs):

        last_model = None

        cast, lt, le = self._comparation_functions(goal.term())

        lb, ub = None, None
        client_data = self._setup()

        terminate = False

        while (lb is None or ub is None or (ub - lb) > step_size) and not terminate:
            bound = self._bound(lb, ub, strategy, goal)
            if bound is None:
                # Just check satisfiability
                check_result = self.solve()
            else:
                parameters = None
                if goal.is_minimization_goal():
                    parameters = (client_data, goal.term(), cast(bound), lt, le, strategy)
                else:
                    # Suppose is a MaximizationGoal
                    parameters = (client_data, cast(bound), goal.term(), lt, le, strategy)
                # Check if there is a model >/>= bound
                check_result = self._optimization_check_progress(*parameters)


            if check_result:
                last_model = self.get_model()
                if feasible_solution_callback:
                    feasible_solution_callback(last_model)
                t = self.get_value(goal.term()).constant_value()
                if goal.is_minimization_goal():
                    ub  = t
                else:
                    lb = t
            else:
                if strategy == 'linear':
                    terminate = True
                elif strategy == 'binary':
                    if lb is None and ub is None:
                        self._cleanup(client_data)
                        return None
                    else:
                        if goal.is_minimization_goal():
                            lb = bound
                        else:
                            ub = bound
                else:
                    raise PysmtValueError("Unknown optimization strategy '%s'" % strategy)
        self._cleanup(client_data)
        if goal.is_minimization_goal():
            t = ub
        else:
            t = lb
        return last_model, cast(t)


class SUAOptimizerMixin(ExternalOptimizerMixin):
    """Optimizer mixin using solving under assumptions"""

    def _setup(self):
        pass

    def _cleanup(self):
        pass

    def _check_improve(self, cost_function, cost_so_far, lt):
        k = lt(cost_function, cost_so_far)
        return not self.solve(assumptions=[k])

    def pareto_optimize(self, cost_functions):
        _, lts, les = zip(*(self._comparation_functions(x) for x in cost_functions))
        terminated = False
        client_data = self._setup()
        while not terminated:
            last_model = None
            optimum_found = False
            costs_so_far = None
            self._pareto_setup(client_data)
            while not optimum_found:
                optimum_found = self._pareto_check_progress(client_data,
                                                            cost_functions,
                                                            costs_so_far,
                                                            lts, les)
                if not optimum_found:
                    last_model = self.get_model()
                    costs_so_far = []
                    for i in range(len(cost_functions)):
                        costs_so_far.append(self.get_value(cost_functions[i]))
            self._pareto_cleanup(client_data)
            if last_model is not None:
                yield last_model, costs_so_far
                self._pareto_block_model(client_data, cost_functions,
                                         last_model, lts, les)
            else:
                terminated = True
        self._cleanup(client_data)

    def can_diverge_for_unbounded_cases(self):
        return True

class SUAOptimizerMixin(ExternalOptimizerMixin):
    """Optimizer mixin using solving under assumptions"""

    def _setup(self):
        return []

    def _cleanup(self, client_data):
        pass

    def _optimization_check_progress(self, client_data, cost_function,
                                     cost_so_far, lt, le, strategy):
        op = le if strategy == 'binary' else lt
        k = op(cost_function, cost_so_far)
        return self.solve(assumptions=[k])

    def _pareto_setup(self, client_data):
        pass

    def _pareto_cleanup(self, client_data):
        pass

    def _pareto_check_progress(self, client_data, cost_functions,
                               costs_so_far, lts, les):
        mgr = self.environment.formula_manager
        k = []
        if costs_so_far is not None:
            k = [les[i](cost_functions[i], costs_so_far[i])
                 for i in range(len(cost_functions))]
            k.append(mgr.Or(lts[i](cost_functions[i], costs_so_far[i])
                            for i in range(len(cost_functions))))
        return not self.solve(assumptions=client_data + k)

    def _pareto_block_model(self, client_data, cost_functions, last_model, lts, les):
        mgr = self.environment.formula_manager
        client_data.append(mgr.Or(lts[i](cost_functions[i],
                                         last_model[cost_functions[i]])
                                  for i in range(len(cost_functions))))

    def can_diverge_for_unbounded_cases(self):
        return True


class IncrementalOptimizerMixin(ExternalOptimizerMixin):
    """Optimizer mixin using the incremental interface"""

    def _setup(self):
        self.push()
        return None

    def _cleanup(self, client_data):
        self.pop()

    def _optimization_check_progress(self, client_data, cost_function,
                                     cost_so_far, lt, le, strategy):
        if strategy == 'linear':
            self.add_assertion(lt(cost_function, cost_so_far))
            return self.solve()
        elif strategy == 'binary':
            self.push()
            self.add_assertion(le(cost_function, cost_so_far))
            res = self.solve()
            self.pop()
            return res

    def _pareto_setup(self, client_data):
        self.push()

    def _pareto_cleanup(self, client_data):
        self.pop()

    def _pareto_check_progress(self, client_data, cost_functions,
                               costs_so_far, lts, les):
        mgr = self.environment.formula_manager
        if costs_so_far is not None:
            for i in range(len(cost_functions)):
                self.add_assertion(les[i](cost_functions[i],
                                          costs_so_far[i]))
            self.add_assertion(mgr.Or(lts[i](cost_functions[i],
                                             costs_so_far[i])
                                      for i in range(len(cost_functions))))
        return not self.solve()

    def _pareto_block_model(self, client_data, cost_functions, last_model, lts, les):
        mgr = self.environment.formula_manager
        self.add_assertion(mgr.Or(lts[i](cost_functions[i],
                                         last_model[cost_functions[i]])
                                  for i in range(len(cost_functions))))

    def can_diverge_for_unbounded_cases(self):
        return True