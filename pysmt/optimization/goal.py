from pysmt.shortcuts import Times, Int

"""
Abstract class for goals
"""
class Goal:
    pass

"""
Maximization goal common to all solvers.
Attention: some solvers may not support this goal
"""
class MaximizationGoal(Goal):
    def __init__(self, formula):
        self.formula = formula

    def term(self):
        return self.formula

    def minimize_term(self):
        return Times(Int(-1), self.formula)

"""
Minimization goal common to all solvers.
Attention: some solvers may not support this goal
"""
class MinimizationGoal(Goal):
    def __init__(self, formula):
        self.formula = formula

    def term(self):
        return self.formula

    def minimize_term(self):
        return self.formula

"""
MaxSMT goal common to all solvers.
Attention: some solvers may not support this goal
"""
class MaxSMT(Goal):

    """Accepts soft clauses and the relative weights"""
    def __init__(self, clause, weight):
        self.soft = []
        for x in range(min(len(clause), len(weight))):
            self.soft.append((clause.pop(0), weight.pop(0)))

    """Accepts soft clauses and the relative weights"""
    def add_soft_clause(self, clause, weight):
        self.soft.append((clause.pop(0), weight.pop(0)))
