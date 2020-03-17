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
from warnings import warn
from six.moves import xrange

from pysmt.exceptions import SolverAPINotFound
from pysmt.constants import Fraction, is_pysmt_fraction, is_pysmt_integer

from pysmt.solvers.dynmsat import MSATLibLoader

from pysmt.logics import LRA, LIA, QF_UFLIA, QF_UFLRA, QF_BV, PYSMT_QF_LOGICS
from pysmt.oracles import get_logic

import pysmt.operators as op
from pysmt import typing as types
from pysmt.solvers.solver import (IncrementalTrackingSolver, UnsatCoreSolver,
                                  Model, Converter, SolverOptions)
from pysmt.solvers.smtlib import SmtLibBasicSolver, SmtLibIgnoreMixin
from pysmt.walkers import DagWalker
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              SolverNotConfiguredForUnsatCoresError,
                              SolverStatusError,
                              InternalSolverError,
                              NonLinearError, PysmtValueError, PysmtTypeError,
                              ConvertExpressionError, PysmtUnboundedOptimizationError)
from pysmt.decorators import clear_pending_pop, catch_conversion_error
from pysmt.solvers.qelim import QuantifierEliminator
from pysmt.solvers.interpolation import Interpolator
from pysmt.walkers.identitydag import IdentityDagWalker
from pysmt.solvers.optimizer import SUAOptimizerMixin, IncrementalOptimizerMixin
from pysmt.solvers.optimizer import Optimizer

from pysmt.solvers.msat import MSatEnv, MathSAT5Model, MathSATOptions
from pysmt.solvers.msat import MathSAT5Solver, MSatConverter, MSatQuantifierEliminator
from pysmt.solvers.msat import MSatInterpolator, MSatBoolUFRewriter

# TODO:
# - check msat does not instantiate any MSAT class directly (use virtual override)
# - is it possible to reintroduce file-level try-except for library import?
# - the "Not in Python's Path" message is wrong for MathSAT when only OptiMAthSAT
#   is installed.. the current implementation must be revised.

class OptiMSATEnv(MSatEnv):
    __lib_name__ = "optimathsat"

    def __init__(self, *args, **kwargs):
        MSatEnv.__init__(self, *args, **kwargs)

    def _do_create_env(self, msat_config=None, msat_env=None):
        return self._msat_lib.msat_create_opt_env(msat_config, msat_env)


class OptiMSATModel(MathSAT5Model):
    __lib_name__ = "optimathsat"

    def __init__(self, *args, **kwargs):
        MathSAT5Model.__init__(self, *args, **kwargs)


class OptiMSATOptions(MathSATOptions):
    __lib_name__ = "optimathsat"

    def __init__(self, *args, **kwargs):
        MathSATOptions.__init__(self, *args, **kwargs)


class OptiMSATSolver(MathSAT5Solver, Optimizer):
    __lib_name__ = "optimathsat"
    OptionsClass = OptiMSATOptions
    # TODO: LOGICS, OptionsClass

    def __init__(self, environment, logic, **options):
        MathSAT5Solver.__init__(self, environment=environment,
                                logic=logic, **options)

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
        msat_obj = self._msat_lib.msat_make_minimize(self.msat_env(), obj_fun, None, None, False)
        self._msat_lib.msat_assert_objective(self.msat_env(), msat_obj)
        self.solve()
        optres = self._msat_lib.msat_objective_result(self.msat_env(), msat_obj)
        if optres == self._msat_lib.MSAT_OPT_UNKNOWN:
            raise SolverReturnedUnknownResultError()
        elif optres == self._msat_lib.MSAT_OPT_UNSAT:
            return None
        else:
            unbounded = self._msat_lib.msat_objective_value_is_unbounded(self.msat_env(),
                                                                  msat_obj,
                                                                  self._msat_lib.MSAT_OPTIMUM)
            if unbounded > 0:
                raise PysmtUnboundedOptimizationError("The optimal value is unbounded")

            is_strict = self._msat_lib.msat_objective_value_is_strict(self.msat_env(),
                                                                      msat_obj,
                                                                      self._msat_lib.MSAT_OPTIMUM)
            if is_strict:
                raise PysmtUnboundedOptimizationError("The optimal value is infinitesimal")

            check = self._msat_lib.msat_load_objective_model(self.msat_env(), msat_obj)
            if check != 0:
                raise ValueError()

            model = self.get_model()
            return model, model.get_value(cost_function)

    def get_model(self):
        return OptiMSATModel(self.environment, self.msat_env)

    def pareto_optimize(self, cost_functions):
        # The pareto generation is currently not wrapped
        # (It is impossible to specify a callback)
        raise NotImplementedError

    def can_diverge_for_unbounded_cases(self):
        return False


class OptiMSATConverter(MSatConverter):
    __lib_name__ = "optimathsat"

    def __init__(self, *args, **kwargs):
        MSatConverter.__init__(self, *args, **kwargs)


class OptiMSATQuantifierEliminator(MSatQuantifierEliminator):
    __lib_name__ = "optimathsat"
    # TODO: LOGICS

    def __init__(self, *args, **kwargs):
        MSatQuantifierEliminator.__init__(self, *args, **kwargs)


class OptiMSATFMQuantifierEliminator(OptiMSATQuantifierEliminator):
    # TODO: LOGICS

    def __init__(self, *args, **kwargs):
        OptiMSATQuantifierEliminator.__init__(self, algorithm='fm', *args, **kwargs)


class OptiMSATLWQuantifierEliminator(OptiMSATQuantifierEliminator):
    # TODO: LOGICS

    def __init__(self, *args, **kwargs):
        OptiMSATQuantifierEliminator.__init__(self, algorithm='lw', *args, **kwargs)


class OptiMSATInterpolator(MSatInterpolator):
    __lib_name__ = "optimathsat"
    # TODO: LOGICS

    def __init__(self, *args, **kwargs):
        MSatInterpolator.__init__(self, *args, **kwargs)

    def _do_create_env(self, msat_config=None, msat_env=None):
        return self._msat_lib.msat_create_opt_env(msat_config, msat_env)


class OptiMSATBoolUFRewriter(MSatBoolUFRewriter):
    __lib_name__ = "optimathsat"

    def __init__(self, *args, **kwargs):
        MsatBoolUFRewriter.__init__(self, *args, **kwargs)


class OptiMSATSUAOptimizer(SUAOptimizerMixin, OptiMSATSolver):
    # TODO: LOGICS
    pass

class OptiMSATIncrementalOptimizer(IncrementalOptimizerMixin, OptiMSATSolver):
    LOGICS = MathSAT5Solver.LOGICS


