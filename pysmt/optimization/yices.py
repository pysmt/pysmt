"""
from pysmt.solvers.yices import YicesSolver
from pysmt.optimization.optimizer import SUAOptimizerMixin, IncrementalOptimizerMixin

class YicesSUAOptimizer(YicesSolver, SUAOptimizerMixin):
    LOGICS = YicesSolver.LOGICS

class YicesIncrementalOptimizer(YicesSolver, IncrementalOptimizerMixin):
    LOGICS = YicesSolver.LOGICS
"""