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
from pysmt.solvers.solver import Model
from pysmt.environment import get_env
from pysmt.exceptions import PysmtTypeError


class EagerModel(Model):
    """A model that does not require the existence of a solver instance.

    This is useful when we want to change the state of the solver but
    maintain a version of the previously found model. An EagerModel
    can also be constructed manually, and provides a simple way to
    define a model.
    """

    def __init__(self, assignment, environment=None):
        if environment is None:
            environment = get_env()
        Model.__init__(self, environment)
        self.environment = environment
        self.assignment = dict(assignment)
        # Create a copy of the assignments to memoize completions
        self.completed_assignment = dict(self.assignment)

    def get_value(self, formula, model_completion=True):
        if model_completion:
            syms = formula.get_free_variables()
            self._complete_model(syms)
            r = formula.substitute(self.completed_assignment)
        else:
            r = formula.substitute(self.assignment)

        res = r.simplify()
        if not res.is_constant():
            raise PysmtTypeError("Was expecting a constant but got %s" % res)
        return res

    def _complete_model(self, symbols):
        undefined_symbols = (s for s in symbols
                             if s not in self.completed_assignment)
        mgr = self.environment.formula_manager

        for s in undefined_symbols:
            if not s.is_symbol():
                raise PysmtTypeError("Was expecting a symbol but got %s" %s)

            if s.symbol_type().is_bool_type():
                value = mgr.Bool(False)
            elif s.symbol_type().is_real_type():
                value = mgr.Real(0)
            elif s.symbol_type().is_int_type():
                value = mgr.Int(0)
            elif s.symbol_type().is_bv_type():
                value = mgr.BVZero(s.bv_width())
            else:
                raise PysmtTypeError("Unhandled type for %s: %s" %
                                     (s, s.symbol_type()))

            self.completed_assignment[s] = value


    def iterator_over(self, language):
        for x in language:
            yield x, self.get_value(x, model_completion=True)

    def __iter__(self):
        """Overloading of iterator from Model.  We iterate only on the
        variables defined in the assignment.
        """
        return iter(self.assignment.items())

    def __contains__(self, x):
        """Returns whether the model contains a value for 'x'."""
        return x in self.assignment
