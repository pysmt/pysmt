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

from fractions import Fraction
from pysmt.environment import get_env
from pysmt.exceptions import PysmtValueError
from pysmt.oracles import get_logic
from pysmt.logics import LIA, LRA, BV

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
        if len(terms) > 0 and get_env().stc.get_type(terms[0]).is_bv_type():
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
        if len(terms) > 0 and get_env().stc.get_type(terms[0]).is_bv_type():
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

    _instance_id = 0

    def __init__(self, allow_real_weights=True):
        """Accepts soft clauses and the relative weights"""
        self.id = MaxSMTGoal._instance_id
        MaxSMTGoal._instance_id = MaxSMTGoal._instance_id + 1
        self.soft = []
        self._bv_signed = False
        self._allow_real_weights = allow_real_weights

    def add_soft_clause(self, clause, weight):
        """Accepts soft clauses and the relative weights"""
        if not isinstance(weight, (int, float, Fraction)):
            raise PysmtValueError("Weight %s has to be an int, a float or a Fraction; given value has type: %s" % (str(weight), str(type(weight))))
        if not self._allow_real_weights and isinstance(weight, (float, Fraction)):
            raise PysmtValueError("Weight %s has to be an int because the flag 'allow_real_weights' is set to 'False'; given value has type: %s" % (str(weight), str(type(weight))))
        self.soft.append((clause, weight))

    def is_maxsmt_goal(self):
        return True

    def allow_real_weights(self):
        return self._allow_real_weights

    def __repr__(self):
        return "MaxSMT{%s}" % (", ".join(("%s: %s" % (x.serialize(), str(w)) for x, w in self.soft)))
