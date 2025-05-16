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
import warnings

from pysmt.solvers.solver import Solver
from pysmt.exceptions import PysmtValueError, GoalNotSupportedError
from pysmt.optimization.goal import MinimizationGoal, MaximizationGoal
from pysmt.shortcuts import INT, REAL, BVType, Equals, Ite, Int, Plus, Real
from pysmt.logics import LIA, LRA, BV, QF_LIRA


class Optimizer(Solver):
    """
    Interface for the optimization
    """

    def optimize(self, goal, **kwargs):
        """Returns a pair `(model, cost)` where `model` is an object
        obtained according to `goal` while satisfying all
        the formulae asserted in the optimizer, while `cost` is the
        objective function value for the model.

        `goal` must have a term with integer, real or
        bit-vector type whose value has to be minimized
        This function can raise a PysmtUnboundedOptimizationError if
        the solver detects that the optimum value is either positive
        or negative infinite or if there is no optimum value because
        one can move arbitrarily close to the optimum without reching
        it (e.g. "x > 5" has no minimum for x, only an infimum)

        """
        raise NotImplementedError

    def pareto_optimize(self, goals):
        """This function is a generator returning *all* the pareto-optimal
        solutions for the problem of minimizing the `goals`
        keeping the formulae asserted in this optimizer satisfied.

        The solutions are returned as pairs `(model, costs)` where
        model is the pareto-optimal assignment and costs is the list
        of costs, one for each optimization function in
        `goals`.

        `goals` must be a list of terms with integer, real or
        bit-vector types whose values have to be minimized

        This function can raise a PysmtUnboundedOptimizationError if
        the solver detects that the optimum value is either positive
        or negative infinite or if there is no optimum value because
        one can move arbitrarily close to the optimum without reching
        it (e.g. "x > 5" has no minimum for x, only an infimum)

        """
        raise NotImplementedError

    def lexicographic_optimize(self, goals):
        """
        This function returns a pair of (model, values) where 'values' is a list containing the optimal values
        (as pysmt constants) for each goal in 'goals'.
        If there is no solution the function returns a pair (None,None)

        The parameter 'goals' must be a list of 'Goals'(see file goal.py).

        The lexicographic method consists of solving a sequence of single-objective optimization problems. The order of
        problems are important because the result of previous goals become a costraint for subsequent goals

        For some implemented examples see file pysmt/test/test_optimization.py
        """
        raise NotImplementedError

    def boxed_optimize(self, goals):
        """
        This function returns dictionary where the keys are the goals of optimization. Each goal is mapped to a pair
        (model, value) of the current goal (key).
        If there is no solution the function returns None

        The parameter 'goals' must be a list of 'Goals'(see file goal.py).

        The boxed method consists of solving a list of single-objective optimization problems independently of
        each other. The order of problems isn't important because the result of previous goals don't change
        any costraint of other goals

        For some implemented examples see file pysmt/test/test_optimization.py
        """
        raise NotImplementedError

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

    def _compute_max_smt_cost(self, model, goal):
        assert goal.is_maxsmt_goal()
        max_smt_weight = 0
        for soft_goal, weight in goal.soft:
            soft_goal_value = model.get_value(soft_goal)
            assert soft_goal_value.is_bool_constant()
            if soft_goal_value.constant_value():
                max_smt_weight += weight.constant_value()
        if goal.real_weights():
            return self.mgr.Real(max_smt_weight)
        return self.mgr.Int(max_smt_weight)

    def _check_pareto_lexicographic_goals(self, goals, mode):
        for goal in goals:
            if goal.is_maxsmt_goal():
                raise GoalNotSupportedError(self, goal, mode)


class OptComparationFunctions:

    def _comparation_functions(self, goal):
        """Internal utility function to get the proper cast, LT and LE
        function for the given objective formula
        """
        mgr = self.environment.formula_manager
        cast_bv = None
        if goal.get_logic() is BV:
            otype = self.environment.stc.get_type(goal.term())
            if goal.signed:
                cast_bv = lambda x: mgr.SBV(x, otype.width)
            else:
                cast_bv = lambda x: mgr.BV(x, otype.width)

        options = {
            LIA: {
                MinimizationGoal: {
                    True: (mgr.Int, mgr.LT, mgr.LE),
                    False: (mgr.Int, mgr.LT, mgr.LE),
                },
                MaximizationGoal: {
                    True: (mgr.Int, mgr.GT, mgr.GE),
                    False: (mgr.Int, mgr.GT, mgr.GE),
                },
            },
            LRA: {
                MinimizationGoal: {
                    True: (mgr.Real, mgr.LT, mgr.LE),
                    False: (mgr.Real, mgr.LT, mgr.LE),
                },
                MaximizationGoal: {
                    True: (mgr.Real, mgr.GT, mgr.GE),
                    False: (mgr.Real, mgr.GT, mgr.GE),
                },
            },
            BV: {
                MinimizationGoal: {
                    False: (cast_bv, mgr.BVULT, mgr.BVULE),
                    True: (cast_bv, mgr.BVSLT, mgr.BVSLE),
                },
                MaximizationGoal: {
                    False: (cast_bv, mgr.BVUGT, mgr.BVUGE),
                    True: (cast_bv, mgr.BVSGT, mgr.BVSGE),
                },
            },
        }
        options[QF_LIRA] = options[LRA]
        return options[goal.get_logic()][goal.opt()][goal.signed]


class OptSearchInterval(OptComparationFunctions):
    """
    Represents a search interval for optimization problems.

    This class is used to manage the bounds and constraints during the optimization
    process. It supports both linear and binary search strategies to refine the
    search space and determine the optimal value for a given goal.

    When using binary search the optimal value is found by iteratively
    narrowing down the search interval based on the results of the optimization.

    The search interval is defined by the lower and upper bounds.
    When minimizing (maximizing) the lower bound (upper bound) is always included
    in the search interval, while the upper bound (lower bound) is excluded.

    Attributes:
        _obj: The optimization goal (e.g., minimization or maximization).
        _lower: The lower bound of the search interval.
        _upper: The upper bound of the search interval.
        _pivot: The current pivot value used in binary search.
        environment: The solver environment.
        client_data: Additional data used during the optimization process.
    """

    def __init__(self, goal, environment, client_data):

        lower, upper = None, None
        if not goal.is_maxsmt_goal():
            term_type = goal.term().get_type()
            # For bit-vectors, start lower and upper bounds to their width limit
            if term_type.is_bv_type():
                if goal.signed:
                    lower = -(2**(term_type.width-1))
                    upper = (2**(term_type.width-1)) - 1
                else:
                    lower = 0
                    upper = (2**term_type.width)
                # add 1 top upper bound because it is excluded when minimizing
                # or remove 1 from lower bound because it is excluded when maximizing
                if goal.is_minimization_goal():
                    upper += 1
                else:
                    lower -= 1

        self._obj = goal
        self._lower = lower
        self._upper = upper
        self._pivot = None
        self.environment = environment
        self._cast, self.op_strict, self.op_ns = self._comparation_functions(goal)
        self.client_data = client_data

    def linear_search_cut(self):
        """
        Generates a constraint for linear search.

        This method creates a constraint to refine the search space by
        cutting off part of the interval based on the current bounds.

        Returns:
            A constraint to refine the search space.
        """
        if self._obj.is_minimization_goal():
            bound = self._upper
        else:
            bound = self._lower

        return self.op_strict(self._obj.term(), self._cast(bound))

    def _compute_pivot(self):
        """
        Computes the pivot value for binary search.

        The pivot is calculated as the midpoint of the current bounds.

        Returns:
            The pivot value.
        """
        if self._lower is None and self._upper is None:
            return 0
        l, u = self._lower, self._upper
        if self._lower is None and self._upper is not None:
            l = self._upper - (abs(self._upper) + 1)
        elif self._lower is not None and self._upper is None:
            u = self._lower + abs(self._lower) + 1
        term_type = self._obj.term().get_type()
        if term_type.is_int_type() or term_type.is_bv_type():
            pivot = (l + u) // 2
            if self._obj.is_minimization_goal():
                return pivot + 1
            else:
                return pivot
        assert term_type.is_real_type()
        return (l + u) / 2

    def binary_search_cut(self):
        """
        Generates a constraint for binary search.

        This method creates a constraint to refine the search space by
        using the pivot value.

        Returns:
            A constraint to refine the search space.
        """
        self._pivot = self._compute_pivot()
        return self.op_strict(self._obj.term(), self._cast(self._pivot))

    def empty(self):
        """
        Checks if the search interval is empty.

        Returns:
            True if the interval is empty, False otherwise.
        """
        if self._upper is None or self._lower is None:
            return False
        return self._upper <= self._lower

    def search_is_sat(self, model):
        """
        Updates the bounds based on a satisfiable model.

        This method refines the bounds of the search interval using the
        value of the optimization goal in the given model.

        Parameters:
            model: The satisfiable model.
        """
        self._pivot = None
        obj_value = model.get_value(self._obj.term())
        if obj_value.is_bv_constant() and self._obj.signed:
            model_value = obj_value.bv_signed_value()
        else:
            model_value = obj_value.constant_value()
        if self._obj.is_minimization_goal():
            if self._upper is None or self._upper > model_value:
                self._upper = model_value
        elif self._obj.is_maximization_goal():
            if self._lower is None or self._lower < model_value:
                self._lower = model_value

    def search_is_unsat(self):
        """
        Updates the bounds based on an unsatisfiable result.

        This method refines the bounds of the search interval when the
        current constraints are unsatisfiable.
        """
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


class OptPareto(OptComparationFunctions):

    def __init__(self, goal, environment):
        self.environment = environment
        self.goal = goal
        self._cast, self.op_strict, self.op_ns = self._comparation_functions(goal)
        self.val = None

    def get_constraint(self, strict):
        if self.val is not None:
            assert self.val.is_constant(), "Value %s is not a constant" % str(self.val)
            correct_operator = self.op_ns
            if strict:
                correct_operator = self.op_strict
            return correct_operator(self.goal.term(), self.val)
        else:
            return None


def _warn_diverge_real_goal(goal):
    if (goal.is_maximization_goal() or goal.is_minimization_goal()) and goal.term().get_type().is_real_type():
        warnings.warn("Algorithm might diverge on Real minimization/maximization objectives.")


class ExternalOptimizerMixin(Optimizer):
    """
    This class is a mixin that can be included by a solver to also implement
    the functionalities of an `Optimizer`.

    Two strategies of optimization are available: `linear` and `binary`.

    The `linear` strategy is the default one, refining the search space by
    checking if there are models that strictly improve the current solution.

    The `binary` strategy is a more aggressive approach, using binary search
    to find the optimal solution.

    Both strategies can diverge for unbounded cases, meaning that they may not
    terminate if the objective is unbounded while they can't terminate
    on an infinitesimal objective.
    """

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
        if goal.is_maximization_goal() or goal.is_minimization_goal() or goal.is_maxsmt_goal():
            rt = self._optimize(goal, strategy)
        else:
            raise GoalNotSupportedError(self, goal)
        return rt

    def boxed_optimize(self, goals, strategy='linear'):
        rt = {}
        for goal in goals:
            if goal.is_maximization_goal() or goal.is_minimization_goal() or goal.is_maxsmt_goal():
                t = self.optimize(goal = goal,strategy = strategy)
                if t is not None:
                    rt[goal] = t
                else:
                    return None
            else:
                raise GoalNotSupportedError(self, goal)
        return rt

    def lexicographic_optimize(self, goals, strategy='linear'):
        self._check_pareto_lexicographic_goals(goals, "lexicographic")
        rt = []
        client_data = self._setup()
        for goal in goals:
            temp = self._lexicographic_opt(client_data, goal, strategy)
            if temp is None:
                self._cleanup(client_data)
                return None
            else:
                model, val = temp
            rt.append(val)

        return model, rt

    def _optimize(self, goal, strategy, extra_assumption = None):
        """
        Core algorithm for the optimization process.
        Based on the strategy, it will either perform a linear or binary search"""
        _warn_diverge_real_goal(goal)
        if goal.is_maxsmt_goal():
            goal = MaximizationGoal(goal.term())
        model = None
        client_data = self._setup()

        current = OptSearchInterval(goal, self.environment, client_data)
        first_step = True
        while not current.empty():
            if not first_step:
                if strategy == "linear":
                    lin_assertions = current.linear_search_cut()
                elif strategy == "binary":
                    lin_assertions = current.binary_search_cut()
                else:
                    raise PysmtValueError("Unknown optimization strategy '%s'" % strategy)
            else:
                lin_assertions = None
            temp_model = self._optimization_check_progress(client_data, lin_assertions, strategy, extra_assumption)
            if temp_model is not None:
                model = temp_model
                current.search_is_sat(model)
            else:
                if first_step:
                    self._cleanup(client_data)
                    return None
                current.search_is_unsat()
            first_step = False

        self._cleanup(client_data)

        if model:
            return model, model.get_value(goal.term())
        return None

    def pareto_optimize(self, goals):
        self._check_pareto_lexicographic_goals(goals, "pareto")
        objs = [OptPareto(goal, self.environment) for goal in goals]

        for g in goals:
            _warn_diverge_real_goal(g)

        terminated = False
        client_data = self._setup()
        while not terminated:
            last_model = None
            optimum_found = False
            for obj in objs:
                 obj.val = None
            self._pareto_setup()
            while not optimum_found:
                optimum_found = self._pareto_check_progress(client_data, objs)
                if not optimum_found:
                    last_model = self.get_model()
                    for obj in objs:
                        obj.val = self.get_value(obj.goal.term())
            self._pareto_cleanup()
            if last_model is not None:
                yield last_model, [obj.val for obj in objs]
                self._pareto_block_model(client_data, objs)
            else:
                terminated = True
        self._cleanup(client_data)

    def _setup(self):
        self.push()
        return []

    def _cleanup(self, client_data):
        self.pop()

    def _pareto_setup(self):
        self.push()

    def _pareto_cleanup(self):
        self.pop()

    def can_diverge_for_unbounded_cases(self):
        return True

    def _optimization_check_progress(self, client_data, formula, strategy, extra_assumption = None):
        """This function is called to check the progress of the optimization.
        It should return the model if the check returned SAT, None if the check
        returned UNSAT.
        """
        raise NotImplementedError()

    def _lexicographic_opt(self, client_data, current_goal, strategy):
        """
        Performs a single step in the lexicographic optimization process for the given goal.

        This method optimizes the current goal while respecting the constraints imposed
        by previously optimized goals. It ensures that the current goal's value is fixed
        for subsequent goals in the lexicographic sequence.

        Parameters:
            client_data (list): A list of constraints accumulated from previously optimized goals.
            current_goal (Goal): The goal to be optimized in this step.
            strategy (str): The optimization strategy to use ('linear' or 'binary').

        Returns:
            tuple: A pair (model, value) where:
                - model: The model representing the solution for the current goal.
                - value: The optimal value for the current goal.
            None: If no solution is found.

        Raises:
            NotImplementedError: If the method is not implemented in the subclass.
        """
        raise NotImplementedError()

    def _pareto_check_progress(self, client_data, objs):
        """
        Checks whether progress can still be made in the Pareto optimization process.

        This method constructs constraints for the current objectives to ensure that
        a new Pareto-optimal solution can be found. It uses the solver to check whether
        these constraints are satisfiable.

        Parameters:
            client_data (list): A list of constraints accumulated during the optimization process.
            objs (list): A list of `OptPareto` objects representing the current optimization objectives.

        Returns:
            bool: True if progress can still be made (i.e., constraints are satisfiable),
                  False otherwise.

        Raises:
            NotImplementedError: If the method is not implemented in the subclass.
        """
        raise NotImplementedError()

    def _pareto_block_model(self, client_data, objs):
        """
        Blocks the current model in the Pareto optimization process.

        This method constructs a disjunction of constraints to block the current model,
        ensuring that the solver does not return the same solution in subsequent iterations.

        Parameters:
            client_data (list): A list of constraints accumulated during the optimization process.
            objs (list): A list of `OptPareto` objects representing the current optimization objectives.

        Returns:
            None

        Raises:
            NotImplementedError: If the method is not implemented in the subclass.
        """
        raise NotImplementedError()


class SUAOptimizerMixin(ExternalOptimizerMixin):
    """Optimizer mixin using solving under assumptions"""

    def _optimization_check_progress(self, client_data, formula, strategy, extra_assumption = None):
        assum = extra_assumption if extra_assumption is not None else []
        if formula is not None:
            assum = assum + [formula]
        is_sat = self.solve(assumptions = assum)
        model = self.get_model() if is_sat else None
        return model

    def _lexicographic_opt(self, client_data, current_goal, strategy):
        temp = self._optimize(current_goal, strategy, extra_assumption = client_data)
        if temp is not None:
            model, val = temp
        else:
            return None

        client_data.append(Equals(current_goal.term(), val))
        return model, val

    def _pareto_check_progress(self, client_data, objs):
        mgr = self.environment.formula_manager
        k = []
        if objs[0].val is not None:
            k = [obj.get_constraint(False) for obj in objs]
            k.append(mgr.Or(obj.get_constraint(True) for obj in objs ))
        return not self.solve(assumptions=client_data + k)

    def _pareto_block_model(self, client_data, objs):
        mgr = self.environment.formula_manager
        client_data.append(mgr.Or(obj.get_constraint(True) for obj in objs))


class IncrementalOptimizerMixin(ExternalOptimizerMixin):
    """Optimizer mixin using the incremental capabilites of the solver"""

    def _optimization_check_progress(self, client_data, formula, strategy, extra_assumption = None):
        if strategy == 'linear':
            if formula is not None:
                self.add_assertion(formula)
            is_sat = self.solve()
            model = self.get_model() if is_sat else None
        elif strategy == 'binary':
            self.push()
            if formula is not None:
                self.add_assertion(formula)
            is_sat = self.solve()
            model = self.get_model() if is_sat else None
            self.pop()
        else:
            raise PysmtValueError("Unknown optimization strategy '%s'" % strategy)
        return model

    def _lexicographic_opt(self, client_data, current_goal, strategy):
        self.push()
        for t in client_data:
            self.add_assertion(t)
        temp = self.optimize(current_goal, strategy)
        self.pop()
        if temp is not None:
            model, val = temp
        else:
            return None
        client_data.append(Equals(current_goal.term(), val))
        return model, val

    def _pareto_check_progress(self, client_data, objs):
        mgr = self.environment.formula_manager
        if objs[0].val is not None:
            for obj in objs:
                self.add_assertion(obj.get_constraint(False))
            self.add_assertion(mgr.Or((obj.get_constraint(True) for obj in objs)))
        return not self.solve()

    def _pareto_block_model(self, client_data, objs):
        mgr = self.environment.formula_manager
        self.add_assertion(mgr.Or((obj.get_constraint(True) for obj in objs)))
