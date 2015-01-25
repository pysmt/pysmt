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
from pysmt.decorators import deprecated
from pysmt.shortcuts import get_type
from pysmt.typing import BOOL

class Solver(object):
    """ Represents a generic SMT Solver. """

    # Define the supported logics for the Solver
    LOGICS = []

    def __init__(self, environment, logic, options=None):
        self.environment = environment
        self.pending_pop = False
        assert logic is not None
        assert options is None, "Options are not supported, yet."
        return

    def is_sat(self, formula):
        assert formula in self.environment.formula_manager, \
               "Formula does not belong to the current Formula Manager"

        self.push()
        self.add_assertion(formula)
        res = self.solve()
        self.pending_pop = True
        return res

    def is_valid(self, formula):
        Not = self.environment.formula_manager.Not
        return not self.is_sat(Not(formula))

    def is_unsat(self, formula):
        return not self.is_sat(formula)


    def get_values(self, exprs):
        """ Returns the value of the expressions if a model was found.

        Restrictions: Requires option :produce-models to be set to true and can
                      be called only after check-sat returned sat or unknown,
                      if no change to the assertion set occurred.

        :type exprs: List of FNodes
        :returns: A dictionary associating to each expr a value
        :rtype: dict
        """
        res = {}
        for f in exprs:
            v = self.get_value(f)
            res[f] = v
        return res


    def push(self, levels=1):
        """ Push the current context of the given number of levels."""
        raise NotImplementedError


    def pop(self, levels=1):
        """ Pop the context of the given number of levels."""
        raise NotImplementedError


    def exit(self):
        """Destroys the solver."""
        raise NotImplementedError


    def reset_assertions(self):
        """ Removes all defined assertions. """
        raise NotImplementedError


    def declare_variable(self, var):
        """ Declare a variable in the solver. """
        raise NotImplementedError


    def add_assertion(self, formula, named=None):
        """ Add assertion to the solver.

        This is a wrapper to :py:func:`assert_`, for better naming.
        """
        raise NotImplementedError


    def solve(self, assumptions=None):
        """Returns the satisfiability value of the asserted
           formulas. Assumptions is a list of Boolean variables or
           negations of boolean variables. If assumptions is
           specified, the satisfiability result is computed assuming
           that all the specified literals are True.

        A call to solve([a1, ..., an]) is functionally equivalent to:

        push()
        add_assertion(And(a1, ..., an))
        res = solve()
        pop()
        return res

        but is in general more efficient.

        """
        raise NotImplementedError


    def print_model(self, name_filter=None):
        """ Prints the model (if one exists).

        An optional function can be passed, that will be called on each symbol
        to decide whether to print it.
        """
        raise NotImplementedError


    def get_value(self, formula):
        """ Returns the value of formula in the current model (if one exists).

        This is a simplified version of the SMT-LIB funtion get_values ."""
        raise NotImplementedError


    def get_py_value(self, formula):
        """ Returns the value of formula as a python type.

        E.g., Bool(True) is translated into True.
        This simplifies writing code that branches on values in the model.
        """
        res = self.get_value(formula)
        assert res.is_constant()
        return res.constant_value()

    def get_py_values(self, formulae):
        """Evaluates the values of the formulae as python types in the current
           model returning a dictionary.
        """
        res = {}
        for f in formulae:
            v = self.get_py_value(f)
            res[f] = v
        return res


    def get_model(self):
        """ Returns an instance of Model that survives the solver instance """
        raise NotImplementedError


    def set_options(self, options):
        """ Sets multiple options at once.

        :param options: Options to be set
        :type options: Dictionary
        """
        raise NotImplementedError


    def __del__(self):
        """ Implicitely call distructor upon garbage collection. """
        self.exit()


    def __enter__(self):
        """ Manage entering a Context (i.e., with statement) """
        return self


    def __exit__(self, exc_type, exc_val, exc_tb):
        """ Manage exiting from Context (i.e., with statement)

        The default behaviour is to explicitely destroy the solver to free
        the associated resources.
        """
        del self

    def _assert_no_function_type(self, item):
        """Enforces that argument 'item' cannot be a FunctionType.

        Raises TypeError.
        """
        if item.is_symbol() and item.symbol_type().is_function_type():
            raise TypeError("Cannot call get_value() on a FunctionType")

    def _assert_is_boolean(self, formula):
        """Enforces that argument 'formula' is of type Boolean.

        Raises TypeError.
        """
        t = get_type(formula)
        if t != BOOL:
            raise TypeError("Argument must be boolean.")




class Model(object):
    """An abstract Model for a Solver.

    This class provides basic services to operate on a model returned
    by a solver. This class is used as superclass for more specific
    Models, that are solver dependent or by the EagerModel class.
    """

    def __init__(self, environment):
        self.environment = environment

    def get_value(self, formula):
        """ Returns the value of formula in the current model (if one exists).

        This is a simplified version of the SMT-LIB funtion get_values .
        """
        raise NotImplementedError

    def get_values(self, formulae):
        """Evaluates the values of the formulae in the current model returning
           a dictionary.
        """
        res = {}
        for f in formulae:
            v = self.get_value(f)
            res[f] = v
        return res


    def get_py_value(self, formula):
        """ Returns the value of formula as a python type.

        E.g., Bool(True) is translated into True.
        This simplifies writing code that branches on values in the model.
        """
        res = self.get_value(formula)
        assert res.is_constant()
        return res.constant_value()


    def get_py_values(self, formulae):
        """Evaluates the values of the formulae as python types in the current
           model returning a dictionary.
        """

        res = {}
        for f in formulae:
            v = self.get_py_value(f)
            res[f] = v
        return res

    def __getitem__(self, idx):
        return self.get_value(idx)


    def __iter__(self):
        for var in self.environment.formula_manager.get_all_symbols():
            yield var, self.get_value(var)

    def __str__(self):
        return "\n".join([ "%s := %s" % (var, value) for (var, value) in self])
