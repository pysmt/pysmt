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
        raise NotImplementedError


    def pareto_optimize(self, cost_functions, callback=None):
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

    def optimize(self, cost_function, initial_cost=None, callback=None):
        # logic = get_logic(cost_function, env=self.environment)
        # if logic.theory.real_arithmetic or logic.theory.real_difference or \
        #    logic.theory.uninterpreted:
        #     raise PysmtValueError("Logic %s is not supported by SUA Optimizers" % logic)

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
                    if exit_request:
                        break
        return last_model


    def pareto_optimize(self, cost_functions, callback=None):
        raise NotImplementedError
