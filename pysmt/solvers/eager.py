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
from pysmt.shortcuts import get_env, Real, Bool, Int
from pysmt.typing import REAL, BOOL, INT

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
        self.assignment = assignment

    def get_value(self, formula):
        r = formula.substitute(self.assignment)
        res = r.simplify()
        if not res.is_constant():
            raise TypeError("Was expecting a constant but got %s" % res)
        return res

    def complete_model(self, symbols):
        undefined_symbols = (s for s in symbols if s not in self.assignment)

        for s in undefined_symbols:
            if not s.is_symbol():
                raise TypeError("Was expecting a symbol but got %s" %s)

            if s.is_symbol(BOOL):
                value = Bool(False)
            elif s.is_symbol(REAL):
                value = Real(0)
            elif s.is_symbol(INT):
                value = Int(0)
            else:
                raise TypeError("Unhandled type for %s: %s" %
                                (s, s.symbol_type()))

            self.assignment[s] = value
