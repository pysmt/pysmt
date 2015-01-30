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
from functools import partial

import pysmt.operators as op


class Walker(object):

    def __init__(self, env=None):
        if env is None:
            import pysmt.shortcuts
            env = pysmt.shortcuts.get_env()
        self.env = env

        self.functions = {}
        self.functions[op.FORALL] = self.walk_forall
        self.functions[op.EXISTS] = self.walk_exists
        self.functions[op.AND] = self.walk_and
        self.functions[op.OR] = self.walk_or
        self.functions[op.NOT] = self.walk_not
        self.functions[op.IMPLIES] = self.walk_implies
        self.functions[op.IFF] = self.walk_iff
        self.functions[op.SYMBOL] = self.walk_symbol
        self.functions[op.FUNCTION] = self.walk_function
        self.functions[op.REAL_CONSTANT] = self.walk_real_constant
        self.functions[op.BOOL_CONSTANT] = self.walk_bool_constant
        self.functions[op.INT_CONSTANT] = self.walk_int_constant
        self.functions[op.PLUS] = self.walk_plus
        self.functions[op.MINUS] = self.walk_minus
        self.functions[op.TIMES] = self.walk_times
        self.functions[op.EQUALS] = self.walk_equals
        self.functions[op.LE] = self.walk_le
        self.functions[op.LT] = self.walk_lt
        self.functions[op.ITE] = self.walk_ite
        self.functions[op.TOREAL] = self.walk_toreal

        assert self.is_complete()

        return

    def walk_error(self, formula, **kwargs):
        """ Default function for a node that is not handled by the Walker, by
        raising a NotImplementedError.
        """
        node_type = formula.node_type()
        if node_type in self.env.dwf:
            dwf = self.env.dwf[node_type]
            walker_class = type(self)
            if type(self) in dwf:
                self.functions[node_type] = partial(dwf[walker_class], self)
                return self.functions[node_type](formula, **kwargs)

        raise NotImplementedError("Was not expecting a node of type %d" %
                                  formula.node_type())


    def is_complete(self, verbose=False):
        """ Returns whether a behaviour has been specified for each FNode. """

        complete = True
        for n in op.ALL_TYPES:
            if n not in self.functions:
                complete = False
                if verbose: print("Node", n,"is missing")
        return complete

    # Methods to be overwritten:
    # Formula will be provided in the key-word formula
    # Additional arguments are passed in the kwargs
    def walk_forall(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_exists(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_and(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_or(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_not(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_implies(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_iff(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_symbol(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_function(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_real_constant(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_bool_constant(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_int_constant(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_plus(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_minus(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_times(self, formula,  **kwargs):
        return self.walk_error(formula,  **kwargs)

    def walk_equals(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_le(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_lt(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_ite(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)

    def walk_toreal(self, formula, **kwargs):
        return self.walk_error(formula, **kwargs)
