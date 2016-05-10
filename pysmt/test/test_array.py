from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.logics import QF_ALIA, QF_IDL
from pysmt.typing import ARRAY_INT, INT, ARRAY_REAL
from pysmt.shortcuts import Symbol, Solver, Select, Store, Not, Equals, Int, And, get_type, Real

class TestArray(TestCase):

    @skipIfNoSolverForLogic(QF_IDL)
    def test_array(self):
     
        solver = Solver(name="cvc4", logic=QF_IDL)
        a = Symbol("a", ARRAY_REAL)
        i = Symbol("i", INT)
        v = Symbol("v", INT)
        #formula = Equals(Select(Store(a,Int(10),Int(100)),Int(10)),Int(100))
        #res = solver.is_sat(formula)
        formula = Equals(Select(Store(a,Int(10),Real(100)),Int(10)),Real(100))
        res = solver.is_sat(formula)
        return

if __name__ == "__main__":
    main()