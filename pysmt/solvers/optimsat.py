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

from pysmt.solvers.msat import *

try:
    import optimathsat
except ImportError:
    raise SolverAPINotFound

from pysmt.solvers.dynmsat import OptiMSATWrapper


class OptiMSATEnv(OptiMSATWrapper, MSatEnv):

    def __init__(self, *args, **kwargs):
        super(OptiMSATEnv, self).__init__(*args, **kwargs)

    def __del__(self):
        super(OptiMSATEnv, self).__del__()


class OptiMSATModel(OptiMSATWrapper, MathSAT5Model):

    def __init__(self, *args, **kwargs):
        super(OptiMSATModel, self).__init__(*args, **kwargs)

    def __del__(self):
        super(OptiMSATModel, self).__del__()


class OptiMSATOptions(OptiMSATWrapper, MathSATOptions):

    def __init__(self, *args, **kwargs):
        super(OptiMSATMOptions, self).__init__(*args, **kwargs)

    def __del__(self):
        super(OptiMSATOptions, self).__del__()


class OptiMSATSolver(OptiMSATWrapper, MathSAT5Solver, Optimizer):
    # TODO: LOGICS, OptionsClass

    def __init__(self, *args, **kwargs):
        super(OptiMSATSolver, self).__init__(*args, **kwargs)
#            MathSAT5Solver.__init__(self, environment=environment,
#                                    logic=logic, **options)

    def __del__(self):
        super(OptiMSATSolver, self).__del__()

    def _le(self, x, y):
        # TODO: support FP?
        otype = self.environment.stc.get_type(x)
        mgr = self.environment.formula_manager
        if otype.is_int_type() or otype.is_real_type():
            return mgr.LE(x, y)
        elif otype.is_bv_type():
            return mgr.BVULE(x, y)

    def optimize(self, cost_function, **kwargs):
        obj_fun = self.converter.convert(cost_function)
        msat_obj = self._msat_wrapper.msat_make_minimize(self.msat_env(), obj_fun, None,
                                              None, False)
        self._msat_wrapper.msat_assert_objective(self.msat_env(), msat_obj)
        self.solve()
        optres = self._msat_wrapper.msat_objective_result(self.msat_env(), msat_obj)
        if optres == self._msat_wrapper.MSAT_OPT_UNKNOWN:
            raise SolverReturnedUnknownResultError()
        elif optres == self._msat_wrapper.MSAT_OPT_UNSAT:
            return None
        else:
            unbounded = self._msat_wrapper.msat_objective_value_is_unbounded(self.msat_env(),
                                                                  msat_obj,
                                                                  self._msat_wrapper.MSAT_OPTIMUM)
            if unbounded > 0:
                raise PysmtUnboundedOptimizationError("The optimal value is unbounded")
            else:
                c = self._msat_wrapper.msat_objective_value_repr(self.msat_env(),
                                                      msat_obj,
                                                      self._msat_wrapper.MSAT_OPTIMUM)
                # This is a hack because msat_objective_value_is_strict
                # is not wrapped in Python (it takes a c++ reference)
                if c[0] == ">" or c[0] == "<":
                    raise PysmtUnboundedOptimizationError("The optimal value is infinitesimal")
                check = self._msat_wrapper.msat_set_model(self.msat_env(), msat_obj)
                if check != 0:
                    raise ValueError()
                model = self.get_model()
                return model, model.get_value(cost_function)


        def pareto_optimize(self, cost_functions):
            # The pareto generation is currently not wrapped
            # (It is impossible to specify a callback)
            raise NotImplementedError

        def can_diverge_for_unbounded_cases(self):
            return False











class OptiMSATConverter(OptiMSATWrapper, MSatConverter):

    def __init__(self, *args, **kwargs):
        super(OptiMSATConverter, self).__init__(*args, **kwargs)

    def __del__(self):
        super(OptiMSATConverter, self).__del__()


# Check if we are working on a version MathSAT supporting quantifier elimination
if hasattr(OptiMSATWrapper().get_lib(), "MSAT_EXIST_ELIM_ALLSMT_FM"):
    class OptiMSATQuantifierEliminator(OptiMSATWrapper, MSatQuantifierEliminator):
        # TODO: LOGICS

        def __init__(self, *args, **kwargs):
            super(OptiMSATQuantifierEliminator, self).__init__(*args, **kwargs)

        def __del__(self):
            super(OptiMSATQuantifierEliminator, self).__del__()


    class OptiMSATFMQuantifierEliminator(OptiMSATQuantifierEliminator):
        # TODO: LOGICS

        def __init__(self, *args, **kwargs):
            super(OptiMSATFMQuantifierEliminator, self).__init__(*args, **kwargs)

        def __del__(self):
            super(OptiMSATFMQuantifierEliminator, self).__del__()


    class OptiMSATLWQuantifierEliminator(OptiMSATQuantifierEliminator):
        # TODO: LOGICS

        def __init__(self, *args, **kwargs):
            super(OptiMSATLWQuantifierEliminator, self).__init__(*args, **kwargs)

        def __del__(self):
            super(OptiMSATLWQuantifierEliminator, self).__del__()


class OptiMSATInterpolator(OptiMSATWrapper, MSatInterpolator):
    # TODO: LOGICS

    def __init__(self, *args, **kwargs):
        super(OptiMSATInterpolator, self).__init__(*args, **kwargs)

    def __del__(self):
        super(OptiMSATInterpolator, self).__del__()


class OptiMSATBoolUFRewriter(OptiMSATWrapper, MSatBoolUFRewriter):

    def __init__(self, *args, **kwargs):
        super(OptiMSATBoolUFRewriter, self).__init__(*args, **kwargs)

    def __del__(self):
        super(OptiMSATBoolUFRewriter, self).__del__()

class OptiMSATSUAOptimizer(SUAOptimizerMixin, OptiMSATSolver):
    # TODO: LOGICS
    pass

class OptiMSATIncrementalOptimizer(IncrementalOptimizerMixin, OptiMSATSolver):
    LOGICS = MathSAT5Solver.LOGICS


