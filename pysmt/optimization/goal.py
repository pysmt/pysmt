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

from pysmt.shortcuts import Times, Int
from pysmt.environment import get_env

class Goal(object):
    """
    This class defines goals for solvers.
    Attention: this class is not instantiable

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
        return isinstance(self, MaximizationGoal)

    def is_minimization_goal(self):
        return isinstance(self, MinimizationGoal)

    def is_minmax_goal(self):
        return isinstance(self, MinMaxGoal)

    def is_maxmin_goal(self):
        return isinstance(self, MaxMinGoal)

    def is_maxsmt_goal(self):
        return isinstance(self, MaxSMTGoal)



class MaximizationGoal(Goal):
    """
    Maximization goal common to all solvers.
    The object can be passed as an argument to the optimize method of any Optimizer
    Attention: some Optimizer may not support this goal
    """

    def __init__(self, formula):
        """
        :param formula: The target formula
        :type  formula: FNode
        """
        self.formula = formula

    def term(self):
        return self.formula



class MinimizationGoal(Goal):
    """
    Minimization goal common to all solvers.
    The object can be passed as an argument to the optimize method of any Optimizer
    Attention: some Optimizer may not support this goal
    """

    def __init__(self, formula):
        """
        :param formula: The target formula
        :type  formula: FNode
        """
        self.formula = formula

    def term(self):
        return self.formula


class MinMaxGoal(MinimizationGoal):

    def __init__(self, terms):
        MinimizationGoal.__init__(get_env().formula_manager.Max(terms))
        self.terms = terms

class MaxMinGoal(MaximizationGoal):

    def __init__(self, terms):
        MaximizationGoal.__init__(get_env().formula_manager.Min(terms))
        self.terms = terms


class MaxSMTGoal(Goal):
    """
    MaxSMT goal common to all solvers.
    Attention: some solvers may not support this goal
    """

    def __init__(self, clause, weight):
        """Accepts soft clauses and the relative weights"""
        self.soft =  zip(clause, weight)

    def add_soft_clause(self, clause, weight):
        """Accepts soft clauses and the relative weights"""
        self.soft.append((clause, weight))
