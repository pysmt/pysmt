#
# This file is part of pySMT.
#
#   Copyright 2015 Andrea Micheli and Marco Gario
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
from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.logics import QF_SLIA
from pysmt.shortcuts import get_env,get_type,Length,String,Int,Solver,Equals,Symbol,get_model,Not
from pysmt.printers import  HRPrinter
from pysmt.typing import INT,STRING

class TestSTRING(TestCase):

    @skipIfNoSolverForLogic(QF_SLIA)
    def test_string(self):
        s1 = Symbol("s1",STRING)
        s2 = Symbol("s2",STRING)
        cvc4SMTSolver = Solver(name="cvc4", logic=QF_SLIA)
        cvc4SMTSolver.add_assertion(Not(Equals(s1,s2)))
        cvc4SMTSolver.add_assertion(Equals(Length(s2), Length(s1)))
        res = cvc4SMTSolver.solve()
        cvc4SMTSolver.print_model()
        assert res, "Was expecting  TRUE" 
        return
if __name__ == "__main__":
    main()
