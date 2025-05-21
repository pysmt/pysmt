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

from pysmt.environment import get_env
from pysmt.exceptions import PysmtValueError
from pysmt.oracles import get_logic
from pysmt.logics import LIA, LRA, BV
from pysmt.fnode import FNode


class Goal(object):
    """
    This class defines goals for solvers.
    Warning: this class is not instantiable

    Examples:

        example of minimization:
        ```
        with Optimizer(name = "z3") as opt:
            x = Symbol("x", INT)
            min = MinimizationGoal(x)
            formula = GE(y, Int(5))
            opt.add_assertion(formula)
            model, cost = opt.optimize(min)
        ```

        example of maximization:
        ```
        with Optimizer(name = "z3") as opt:
            max = MaximizationGoal(x)
            formula = LE(y, Int(5))
            opt.add_assertion(formula)
            model, cost = opt.optimize(max)
        ```
    """

    def is_maximization_goal(self):
        return False

    def is_minimization_goal(self):
        return False

    def is_minmax_goal(self):
        return False

    def is_maxmin_goal(self):
        return False

    def is_maxsmt_goal(self):
        return False

    def get_logic(self):
        logic = get_logic(self.formula)
        if logic <= LIA:
            return LIA
        elif logic <= LRA:
            return LRA
        elif logic <= BV:
            return BV
        else:
            return logic

    @property
    def signed(self):
        return self._bv_signed

    @signed.setter
    def signed(self, value):
        self._bv_signed = value


class MaximizationGoal(Goal):
    """
    Maximization goal common to all solvers.
    The object can be passed as an argument to the optimize method of any Optimizer
    Warning: some Optimizer may not support this goal
    """

    def __init__(self, formula, signed = False):
        """
        :param formula: The target formula
        :type  formula: FNode
        """
        self.formula = formula
        self._bv_signed = signed

    def opt(self):
        return MaximizationGoal

    def term(self):
        return self.formula

    def is_maximization_goal(self):
        return True

    def __repr__(self):
        return "Maximize{%s}" % self.formula.serialize()


class MinimizationGoal(Goal):
    """
    Minimization goal common to all solvers.
    The object can be passed as an argument to the optimize method of any Optimizer
    Warning: some Optimizer may not support this goal
    """

    def __init__(self, formula, sign = False):
        """
        :param formula: The target formula
        :type  formula: FNode
        """
        self.formula = formula
        self._bv_signed = sign

    def opt(self):
        return MinimizationGoal

    def term(self):
        return self.formula

    def is_minimization_goal(self):
        return True

    def __repr__(self):
        return "Minimize{%s}" % self.formula.serialize()


class MinMaxGoal(MinimizationGoal):
    """
    Minimize the maximum expression within 'terms'
    This goal is common to all solvers.
    The object can be passed as an argument to the optimize method of any Optimizer
    Warning: some Optimizer may not support this goal
    """

    def __init__(self, terms, sign = False):
        """
        :param terms: List of FNode
        """
        if len(terms) == 0:
            raise PysmtValueError("MinMaxGoal requires at least one term")
        elif terms[0].get_type().is_bv_type():
            formula = get_env().formula_manager.MaxBV(sign, terms)
        else:
            formula = get_env().formula_manager.Max(terms)
        MinimizationGoal.__init__(self, formula)
        self.terms = terms
        self._bv_signed = sign

    def is_minmax_goal(self):
        return True

    def __repr__(self):
        return "Minimize{Max{%s}}" % (", ".join(x.serialize() for x in self.terms))


class MaxMinGoal(MaximizationGoal):
    """
    Maximize the minimum expression within 'terms'
    This goal is common to all solvers.
    The object can be passed as an argument to the optimize method of any Optimizer
    Warning: some Optimizer may not support this goal
    """

    def __init__(self, terms, sign = False):
        """
        :param terms: List of FNode
        """
        if len(terms) == 0:
            raise PysmtValueError("MaxMinGoal requires at least one term")
        elif terms[0].get_type().is_bv_type():
            formula = get_env().formula_manager.MinBV(sign, terms)
        else:
            formula = get_env().formula_manager.Min(terms)
        MaximizationGoal.__init__(self, formula)
        self.terms = terms
        self._bv_signed = sign

    def is_maxmin_goal(self):
        return True

    def __repr__(self):
        return "Maximize{Min{%s}}" % (", ".join(x.serialize() for x in self.terms))


class MaxSMTGoal(Goal):
    """
    MaxSMT goal common to all solvers.
    """

    def __init__(self, real_weights=True):
        """Accepts soft clauses and the relative weights"""
        self.soft = []
        self._bv_signed = False
        self._real_weights = real_weights

    def add_soft_clause(self, clause, weight):
        """Accepts soft clauses and the relative weights"""
        mgr = get_env().formula_manager
        if not clause.get_type().is_bool_type():
            raise PysmtValueError(
                "Clause '%s' has to be a boolean formula; given type is: '%s'" %
                (str(clause), str(clause.get_type()))
            )
        if isinstance(weight, FNode):
            if not weight.is_constant():
                raise PysmtValueError(
                    "Weight '%s' has to be a constant; given type is: '%s'" %
                    (str(weight), str(weight.get_type()))
                )
            weight_type = weight.get_type()
            if not weight_type.is_real_type() and not weight_type.is_int_type():
                raise PysmtValueError(
                    "Weight '%s' has to be a real or integer type; given type is: '%s'" %
                    (str(weight), str(weight_type))
                )
            if weight_type.is_real_type() and not self._real_weights:
                raise PysmtValueError(
                    "Weight '%s' has to be an integer because the flag 'real_weights' is set to 'False'; given type is: '%s'" %
                    (str(weight), str(weight.get_type()))
                )
            if weight_type.is_int_type() and self._real_weights:
                weight = mgr.Real(weight.constant_value())
            self.soft.append((clause, weight))
        else:
            WeightFnodeClass = mgr.Real if self.real_weights() else mgr.Int
            self.soft.append((clause, WeightFnodeClass(weight)))

    def is_maxsmt_goal(self):
        return True

    def is_maximization_goal(self):
        return True

    def real_weights(self):
        return self._real_weights

    def term(self):
        formula = None
        mgr = get_env().formula_manager
        zero = mgr.Real(0) if self.real_weights() else mgr.Int(0)
        for (c, w) in self.soft:
            if formula is not None:
                formula = mgr.Plus(formula, mgr.Ite(c, w, zero))
            else:
                formula = mgr.Ite(c, w, zero)
        assert formula is not None, "Empty MaxSMT goal passed"
        return formula

    def __repr__(self):
        return "MaxSMT{%s}" % (", ".join(("%s: %s" % (x.serialize(), w.serialize()) for x, w in self.soft)))
