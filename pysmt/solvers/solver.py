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
from pysmt.typing import BOOL
from pysmt.solvers.options import SolverOptions
from pysmt.decorators import clear_pending_pop
from pysmt.exceptions import (SolverReturnedUnknownResultError, PysmtValueError,
                              SolverNotConfiguredForUnsatCoresError,
                              PysmtTypeError, SolverStatusError)


class Solver(object):
    """Represents a generic SMT Solver."""

    # Define the supported logics for the Solver
    LOGICS = []

    # Class defining options for the Solver
    OptionsClass = SolverOptions

    def __init__(self, environment, logic, **options):
        if logic is None:
            raise PysmtValueError("Cannot provide 'None' as logic")

        self.environment = environment
        self.pending_pop = False
        self.logic = logic
        self.options = self.OptionsClass(**options)
        self._destroyed = False
        return

    def solve(self, assumptions=None):
        """Returns the satisfiability value of the asserted formulas.

        Assumptions is a list of Boolean variables or negations of
        boolean variables. If assumptions is specified, the
        satisfiability result is computed assuming that all the
        specified literals are True.

        A call to solve([a1, ..., an]) is functionally equivalent to::

          push()
          add_assertion(And(a1, ..., an))
          res = solve()
          pop()
          return res

        but is in general more efficient.

        Other convenience methods (is_sat, is_unsat, is_valid) are
        wrappers around this function.

        :returns: Whether the assertion stack is satisfiable
                  w.r.t. the given assumptions (if given)
        :rtype: bool
        """
        raise NotImplementedError

    def get_model(self):
        """Returns an instance of Model that survives the solver instance.

        Restrictions: Requires option generate_models to be set to
                      true (default) and can be called only after
                      :py:func:`solve` (or one of the derived methods)
                      returned sat or unknown, if no change to the
                      assertion set occurred.

        """
        raise NotImplementedError


    def is_sat(self, formula):
        """Checks satisfiability of the formula w.r.t. the current state of
        the solver.

        Previous assertions are taken into account.

        :type formula: FNode
        :returns: Whether formula is satisfiable
        :rtype: bool
        """
        assert formula in self.environment.formula_manager, \
               "Formula does not belong to the current Formula Manager"

        if not self.options.incremental:
            # If not incremental, we only need to assert and solve.
            self.add_assertion(formula)
            # We do not allow two calls to solve()
            def solve_error(*args, **kwargs):
                raise SolverStatusError("Cannot call is_sat twice when incrementality is disable")
            res = self.solve()
            self.solve = solve_error
            self.is_sat = solve_error
            return res

        # Try to be incremental using push/pop but fallback to
        # solving under assumption if push/pop is not implemented
        use_solving_under_assumption = False
        try:
            self.push()
        except NotImplementedError:
            use_solving_under_assumption = True

        if use_solving_under_assumption:
            res = self.solve([formula])
        else:
            self.add_assertion(formula)
            res = self.solve()
            self.pending_pop = True

        return res

    def is_valid(self, formula):
        """Checks validity of the formula w.r.t. the current state of the
        solver.

        Previous assertions are taken into account. See :py:func:`is_sat`

        :type formula: FNode
        :returns: Whether formula is valid
        :rtype: bool
        """
        Not = self.environment.formula_manager.Not
        return not self.is_sat(Not(formula))

    def is_unsat(self, formula):
        """Checks unsatisfiability of the formula w.r.t. the current state of
        the solver.

        Previous assertions are taken into account. See :py:func:`is_sat`

        :type formula: FNode
        :returns: Whether formula is unsatisfiable
        :rtype: bool
        """
        return not self.is_sat(formula)

    def get_values(self, formulae):
        """Returns the value of the expressions if a model was found.

        Requires option generate_models to be set to true (default)
        and can be called only after :py:func:`solve` (or to one of
        the derived methods) returned sat or unknown, if no change to
        the assertion set occurred.

        :type formulae: Iterable of FNodes
        :returns: A dictionary associating to each expr a value
        :rtype: dict

        """
        res = {}
        for f in formulae:
            v = self.get_value(f)
            res[f] = v
        return res

    def push(self, levels=1):
        """Push the current context of the given number of levels.

        :type levels: int
        """
        raise NotImplementedError

    def pop(self, levels=1):
        """Pop the context of the given number of levels.

        :type levels: int
        """
        raise NotImplementedError

    def exit(self):
        """Exits from the solver and closes associated resources."""
        if not self._destroyed:
            self._exit()
            self._destroyed = True

    def _exit(self):
        """Exits from the solver and closes associated resources."""
        raise NotImplementedError

    def reset_assertions(self):
        """Removes all defined assertions."""
        raise NotImplementedError

    def add_assertion(self, formula, named=None):
        """Add assertion to the solver."""
        raise NotImplementedError

    def add_assertions(self, formulae):
        for formula in formulae:
            self.add_assertion(formula)

    def print_model(self, name_filter=None):
        """Prints the model (if one exists).

        An optional function can be passed, that will be called on each symbol
        to decide whether to print it.
        """
        raise NotImplementedError

    def get_value(self, formula):
        """Returns the value of formula in the current model (if one exists).

        This is a simplified version of the SMT-LIB function get_values
        """
        raise NotImplementedError

    def get_py_value(self, formula):
        """Returns the value of formula as a python type.

        E.g., Bool(True) is translated into True.
        This simplifies writing code that branches on values in the model.
        """
        res = self.get_value(formula)
        assert res.is_constant()
        return res.constant_value()

    def get_py_values(self, formulae):
        """Returns the values of the formulae as python types.

        Returns a dictionary mapping each formula to its python value.
        """
        res = {}
        for f in formulae:
            v = self.get_py_value(f)
            res[f] = v
        return res

    def __enter__(self):
        """Manages entering a Context (i.e., with statement)"""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Manages exiting from Context (i.e., with statement)

        The default behaviour is "close" the solver by calling the
        py:func:`exit` method.
        """
        self.exit()

    def _assert_no_function_type(self, item):
        """Enforces that argument 'item' cannot be a FunctionType.

        Raises TypeError.
        """
        if item.is_symbol() and item.symbol_type().is_function_type():
            raise PysmtTypeError("Cannot call get_value() on a FunctionType")

    def _assert_is_boolean(self, formula):
        """Enforces that argument 'formula' is of type Boolean.

        Raises TypeError.
        """
        if formula.get_type() != BOOL:
            raise PysmtTypeError("Argument must be boolean.")


class IncrementalTrackingSolver(Solver):
    """A solver that keeps track of the asserted formulae

    This class provides tracking of the assertions that are stored
    inside the solver, the last executed command and the last solving
    result.

    It requires the extending class to implement the following proxy
    methods:

    * _reset_assertions
    * _add_assertion
    * _solve
    * _push
    * _pop

    The semantics of each function is the same as the non-proxy
    version except for _add_assertion that is supposed to return a
    result (of any type) that will constitute the elements of the
    self.assertions list.
    """

    def __init__(self, environment, logic, **options):
        """See py:func:`Solver.__init__()`."""
        Solver.__init__(self, environment, logic, **options)

        self._last_result = None
        self._last_command = None

        self._assertion_stack = []
        self._backtrack_points = []

    @property
    def last_command(self):
        """Returns the name of the last executed command"""
        return self._last_command

    @property
    def last_result(self):
        """Returns the result of the last call to solve().

        Returns True, False or "unknown": the last result of the last
        call to solve(). If solve has never been called, None is
        returned
        """
        return self._last_result

    @property
    @clear_pending_pop
    def assertions(self):
        """Returns the list of assertions that are still in the solver.

        Returns the list of results of calls to _add_assertion() that
        are still asserted in the solver
        """
        return self._assertion_stack

    def _reset_assertions(self):
        raise NotImplementedError

    def reset_assertions(self):
        self._reset_assertions()
        self._assertion_stack = []
        self._last_command = "reset_assertions"

    def _add_assertion(self, formula, named=None):
        """Assert the formula in the solver.

        This must return the asserted formula (as an FNode) exactly as
        it was asserted in the solver, thus accounting for rewritings,
        simplifications, etc.

        :returns: The asserted formula
        :rtype: :py:class:
        """
        raise NotImplementedError

    def add_assertion(self, formula, named=None):
        tracked = self._add_assertion(formula, named=named)
        self._assertion_stack.append(tracked)
        self._last_command = "assert"

    def _solve(self, assumptions=None):
        raise NotImplementedError

    def solve(self, assumptions=None):
        try:
            res = self._solve(assumptions=assumptions)
            self._last_result = res
            return res
        except SolverReturnedUnknownResultError:
            self._last_result = "unknown"
            raise

        finally:
            self._last_command = "solve"

    def _push(self, levels=1):
        raise NotImplementedError

    def push(self, levels=1):
        self._push(levels=levels)
        point = len(self._assertion_stack)
        for _ in range(levels):
            self._backtrack_points.append(point)
        self._last_command = "push"

    def _pop(self, levels=1):
        raise NotImplementedError

    def pop(self, levels=1):
        self._pop(levels=levels)
        for _ in range(levels):
            point = self._backtrack_points.pop()
            self._assertion_stack = self._assertion_stack[0:point]
        self._last_command = "pop"


class UnsatCoreSolver(object):
    """A solver supporting unsat core extraction"""

    UNSAT_CORE_SUPPORT = True

    def _check_unsat_core_config(self):
        if self.options.unsat_cores_mode is None:
            raise SolverNotConfiguredForUnsatCoresError

        if self.last_result is None or self.last_result:
            raise SolverStatusError("The last call to solve() was not" \
                                    " unsatisfiable")

        if self.last_command != "solve":
            raise SolverStatusError("The solver status has been modified by a" \
                                    " '%s' command after the last call to" \
                                    " solve()" % self.last_command)

    def get_unsat_core(self):
        """Returns the unsat core as a set of formulae.

        After a call to solve() yielding UNSAT, returns the unsat core
        as a set of formulae
        """
        raise NotImplementedError


    def get_named_unsat_core(self):
        """Returns the unsat core as a dict of names to formulae.

        After a call to solve() yielding UNSAT, returns the unsat core as a
        dict of names to formulae
        """
        raise NotImplementedError


class Model(object):
    """An abstract Model for a Solver.

    This class provides basic services to operate on a model returned
    by a solver. This class is used as superclass for more specific
    Models, that are solver dependent or by the EagerModel class.
    """

    def __init__(self, environment):
        self.environment = environment
        self._converter = None

    def get_value(self, formula, model_completion=True):
        """Returns the value of formula in the current model (if one exists).

        If model_completion is True, then variables not appearing in the
        assignment are given a default value, otherwise an error is generated.

        This is a simplified version of the SMT-LIB function get_values .
        """
        raise NotImplementedError

    def get_values(self, formulae, model_completion=True):
        """Evaluates the values of the formulae in the current model.

        Evaluates the values of the formulae in the current model
        returning a dictionary.
        """
        res = {}
        for f in formulae:
            v = self.get_value(f, model_completion=model_completion)
            res[f] = v
        return res

    def get_py_value(self, formula, model_completion=True):
        """Returns the value of formula as a python type.

        E.g., Bool(True) is translated into True.
        This simplifies writing code that branches on values in the model.
        """
        res = self.get_value(formula, model_completion=model_completion)
        assert res.is_constant()
        return res.constant_value()

    def get_py_values(self, formulae, model_completion=True):
        """Returns the values of the formulae as python types.

        Returns the values of the formulae as python types. in the
        current model returning a dictionary.
        """
        res = {}
        for f in formulae:
            v = self.get_py_value(f, model_completion=model_completion)
            res[f] = v
        return res

    def satisfies(self, formula, solver=None):
        """Checks whether the model satisfies the formula.

        The optional solver argument is used to complete partial
        models.
        """

        subs = self.get_values(formula.get_free_variables())
        simp = formula.substitute(subs).simplify()
        if simp.is_true():
            return True
        if simp.is_false():
            return False

        free_vars = simp.get_free_variables()
        if  len(free_vars) > 0:
            # Partial model
            return False

        if self.environment.enable_div_by_0 and solver is not None:
            # Models might not be simplified to a constant value
            # if there is a division by zero. We find the
            # division(s) and ask the solver for a replacement
            # expression.
            stack = [simp]
            div_0 = []
            while stack:
                x = stack.pop()
                if x.is_constant():
                    pass
                elif x.is_div() and x.arg(1).is_zero():
                    div_0.append(x)
                stack += x.args()

            subs = self.get_values(div_0)
            simp = simp.substitute(subs).simplify()
            return simp.is_true()
        return False

    @property
    def converter(self):
        """Get the Converter associated with the Solver."""
        return self._converter

    @converter.setter
    def converter(self, value):
        self._converter = value

    def __getitem__(self, idx):
        return self.get_value(idx, model_completion=True)

    def __str__(self):
        return "\n".join([ "%s := %s" % (var, value) for (var, value) in self])


class Converter(object):
    """A Converter implements functionalities to convert expressions.

    There are two key methods: convert() and back().
    The first performs the forward conversion (pySMT -> Solver API),
    the second performs the backwards conversion (Solver API -> pySMT)
    """

    def convert(self, formula):
        """Convert a PySMT formula into a Solver term."""
        raise NotImplementedError

    def back(self, expr):
        """Convert an expression of the Solver into a PySMT term."""
        raise NotImplementedError
