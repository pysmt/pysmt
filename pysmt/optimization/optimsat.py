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

from pysmt.decorators import clear_pending_pop
from pysmt.logics import LRA, LIA


from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              PysmtUnboundedOptimizationError,
                              GoalNotSupportedError,
                              PysmtInfinitesimalError)
from pysmt.optimization.optimizer import Optimizer

from pysmt.solvers.msat import MSatEnv, MathSAT5Model, MathSATOptions
from pysmt.solvers.msat import MathSAT5Solver, MSatConverter, MSatQuantifierEliminator
from pysmt.solvers.msat import MSatInterpolator, MSatBoolUFRewriter


class OptiMSATEnv(MSatEnv):
    __lib_name__ = "optimathsat"

    def __init__(self, msat_config=None):
        MSatEnv.__init__(self, msat_config=msat_config)

    def _do_create_env(self, msat_config=None, msat_env=None):
        return self._msat_lib.msat_create_opt_env(msat_config, msat_env)


class OptiMSATModel(MathSAT5Model):
    __lib_name__ = "optimathsat"

    def __init__(self, environment, msat_env):
        MathSAT5Model.__init__(self, environment=environment,
                               msat_env=msat_env)


class OptiMSATOptions(MathSATOptions):
    __lib_name__ = "optimathsat"

    def __init__(self, **base_options):
        MathSATOptions.__init__(self, **base_options)
        # enables the dump of the interaction with optimathsat on the file
        # useful for debugging
        # self.solver_options['debug.api_call_trace_filename'] = "/tmp/omt.smt2"


class OptiMSATSolver(MathSAT5Solver, Optimizer):
    __lib_name__ = "optimathsat"

    LOGICS = MathSAT5Solver.LOGICS

    OptionsClass = OptiMSATOptions

    def __init__(self, environment, logic, **options):
        MathSAT5Solver.__init__(self, environment=environment,
                                logic=logic, **options)
        self._objectives_to_destroy = []

    def _assert_msat_goal(self, goal, goal_id = None):

        if goal.is_maxsmt_goal():
            assert goal_id is not None
            for tcons, weight in goal.soft:
                obj_tcons = self.converter.convert(tcons)
                obj_weight = self._msat_lib.msat_make_number(self.msat_env(), str(weight.constant_value()))
                self._msat_lib.msat_assert_soft_formula(self.msat_env(), obj_tcons, obj_weight, "__pysmt_" + str(goal_id))
            obj_fun = self._msat_lib.msat_from_string(self.msat_env(), "__pysmt_" + str(goal_id))
            make_fun = self._msat_lib.msat_make_minimize

        elif goal.is_minmax_goal() or goal.is_maxmin_goal():
            if goal.is_minmax_goal():
                make_fun = self._msat_lib.msat_make_minmax
            else:
                make_fun = self._msat_lib.msat_make_maxmin

            obj_fun = []
            for f in goal.terms:
                obj_fun.append(self.converter.convert(f))

        elif goal.is_minimization_goal() or goal.is_maximization_goal():
            if goal.is_minimization_goal():
                make_fun = self._msat_lib.msat_make_minimize
            else:
                make_fun = self._msat_lib.msat_make_maximize

            cost_function = goal.term()
            obj_fun = self.converter.convert(cost_function)

        else:
            raise GoalNotSupportedError(self, goal)

        msat_obj = make_fun(self.msat_env(), obj_fun, signed = goal.signed)
        self._msat_lib.msat_assert_objective(self.msat_env(), msat_obj)
        self._objectives_to_destroy.append(msat_obj)
        return msat_obj

    def _get_goal_value(self, msat_obj, goal):
        if not self._check_unsat_unbound_infinitesimal(msat_obj):
            return None
        model = self.get_model()
        if goal.is_maxsmt_goal():
            return model, self._compute_max_smt_cost(model, goal)
        return model, model.get_value(goal.term())

    @clear_pending_pop
    def optimize(self, goal, **kwargs):
        self.push()

        msat_obj = self._assert_msat_goal(goal, 0)

        self.solve()
        # set after the solve because the solve method has the clear_pending_pop decorator
        self.pending_pop = True
        return self._get_goal_value(msat_obj, goal)

    @clear_pending_pop
    def pareto_optimize(self, goals):
        self.push()
        self._check_pareto_lexicographic_goals(goals, "pareto")
        self._msat_lib.msat_set_opt_priority(self.msat_env(), "par")

        msat_objs = {
            g: self._assert_msat_goal(g) for g in goals
        }

        while self.solve():
            if all(self._check_unsat_unbound_infinitesimal(mo) for mo in msat_objs.values()):
                model = self.get_model()
                yield model, [model.get_value(goal.term()) for goal in goals]
            else:
                break
        # set after the solve because the solve method has the clear_pending_pop decorator
        self.pending_pop = True

    @clear_pending_pop
    def lexicographic_optimize(self, goals):
        self.push()
        self._check_pareto_lexicographic_goals(goals, "lexicographic")
        self._msat_lib.msat_set_opt_priority(self.msat_env(), "lex")

        msat_objs = {
            g: self._assert_msat_goal(g) for g in goals
        }

        rt = self.solve()
        # set after the solve because the solve method has the clear_pending_pop decorator
        self.pending_pop = True

        if rt and all(self._check_unsat_unbound_infinitesimal(mo) for mo in msat_objs.values()):
            model = self.get_model()
            return model, [model.get_value(x.term()) for x in goals]
        else:
            return None

    @clear_pending_pop
    def boxed_optimize(self, goals):
        self.push()
        self._msat_lib.msat_set_opt_priority(self.msat_env(), "box")
        msat_objs = []

        for goal_id, g in enumerate(goals):
            msat_objs.append(self._assert_msat_goal(g, goal_id))

        check = self.solve()
        # set after the solve because the solve method has the clear_pending_pop decorator
        self.pending_pop = True
        if not check:
            return None

        rt = {}

        for msat_obj, goal in zip(msat_objs, goals):
            model_value = self._get_goal_value(msat_obj, goal)
            if model_value is None:
                return None
            rt[goal] = model_value

        return rt

    def get_model(self):
        return OptiMSATModel(self.environment, self.msat_env)

    def can_diverge_for_unbounded_cases(self):
        return False

    def _check_unsat_unbound_infinitesimal(self, msat_obj):
        optres = self._msat_lib.msat_objective_result(self.msat_env(), msat_obj)
        if optres == self._msat_lib.MSAT_OPT_UNKNOWN:
            raise SolverReturnedUnknownResultError()
        elif optres == self._msat_lib.MSAT_OPT_UNSAT:
            return False
        else:
            unbounded = self._msat_lib.msat_objective_value_is_unbounded(
                self.msat_env(),
                msat_obj,
                self._msat_lib.MSAT_OPTIMUM
            )
            if unbounded > 0:
                raise PysmtUnboundedOptimizationError("The optimal value is unbounded")

            is_strict = self._msat_lib.msat_objective_value_is_strict(
                self.msat_env(),
                msat_obj,
                self._msat_lib.MSAT_OPTIMUM
            )
            if is_strict:
                raise PysmtInfinitesimalError("The optimal value is infinitesimal")

            check = self._msat_lib.msat_load_objective_model(self.msat_env(), msat_obj)
            if check != 0:
                raise ValueError()

            return True


class OptiMSATConverter(MSatConverter):
    __lib_name__ = "optimathsat"

    def __init__(self, environment, msat_env):
        MSatConverter.__init__(self, environment=environment,
                               msat_env=msat_env)

    def _get_bool_uf_rewriter(self, environment):
        return OptiMSATBoolUFRewriter(environment=environment)


class OptiMSATQuantifierEliminator(MSatQuantifierEliminator):
    __lib_name__ = "optimathsat"

    LOGICS = MSatQuantifierEliminator.LOGICS

    def __init__(self, environment, logic=None, algorithm='lw'):
        MSatQuantifierEliminator.__init__(self, environment=environment,
                                          logic=logic, algorithm=algorithm)


class OptiMSATFMQuantifierEliminator(OptiMSATQuantifierEliminator):
    LOGICS = [LRA]

    def __init__(self, environment, logic=None):
        OptiMSATQuantifierEliminator.__init__(self, environment,
                                              logic=logic, algorithm='fm')


class OptiMSATLWQuantifierEliminator(OptiMSATQuantifierEliminator):
    LOGICS = [LRA, LIA]

    def __init__(self, environment, logic=None):
        OptiMSATQuantifierEliminator.__init__(self, environment,
                                              logic=logic, algorithm='lw')


class OptiMSATInterpolator(MSatInterpolator):
    __lib_name__ = "optimathsat"
    LOGICS = MSatInterpolator.LOGICS

    def __init__(self, environment, logic=None):
        MSatInterpolator.__init__(self, environment=environment,
                                  logic=logic)

    def _do_create_env(self, msat_config=None, msat_env=None):
        return self._msat_lib.msat_create_opt_env(msat_config, msat_env)

    def _do_create_env(self, msat_config=None, msat_env=None):
        return self._msat_lib.msat_create_opt_env(msat_config, msat_env)


class OptiMSATBoolUFRewriter(MSatBoolUFRewriter):
    __lib_name__ = "optimathsat"

    def __init__(self, environment):
        MSatBoolUFRewriter.__init__(self, environment=environment)
