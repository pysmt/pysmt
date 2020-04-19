from pysmt.solvers.msat import MathSAT5Solver
from pysmt.optimization.optimizer import SUAOptimizerMixin, IncrementalOptimizerMixin

class MSatSUAOptimizer(MathSAT5Solver, SUAOptimizerMixin):
    LOGICS = MathSAT5Solver.LOGICS

class MSatIncrementalOptimizer(MathSAT5Solver, IncrementalOptimizerMixin):
    LOGICS = MathSAT5Solver.LOGICS
