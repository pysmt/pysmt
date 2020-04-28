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

class Goal(object):

    def is_maximization_goal(self):
        return isinstance(self, MaximizationGoal)

    def is_minimization_goal(self):
        return isinstance(self, MinimizationGoal)

    def is_maxSMT_goal(self):
        return isinstance(self, MaxSMT)


class MaximizationGoal(Goal):
    """
    Maximization goal common to all solvers.
    The object can be passed as an argument to the optimize method of any Optimizer
    Attention: some Optimizer may not support this goal
    """

    def __init__(self, formula):
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
        self.formula = formula

    def term(self):
        return self.formula


class MaxSMT(Goal):
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
