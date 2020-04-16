from pysmt.optimization.goals.goal import Goal
class MaximizationGoal(Goal):

    def __init__(self, clause, weight):
        self.clause = clause
        self.soft = []

    def add_soft_clause(self, soft, weight):
        self.soft.append((soft, weight))
