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
import unittest

from pysmt.test import TestCase
from pysmt.shortcuts import get_env, Not, Symbol, UnsatCoreSolver
from pysmt.logics import QF_BOOL

class TestUnsatCores(TestCase):

    @unittest.skipIf(len(get_env().factory.all_unsat_core_solvers()) == 0,
                     "No Solver supporting Unsat Cores is available.")
    def test_basic(self):
        x = Symbol("x")
        with UnsatCoreSolver(logic=QF_BOOL) as s:
            s.add_assertion(x)
            s.add_assertion(Not(x))
            r = s.solve()
            self.assertFalse(r)
            core = s.get_unsat_core()
            self.assertEqual(len(core), 2)
            self.assertIn(x, core)
            self.assertIn(Not(x), core)



if __name__ == '__main__':
    unittest.main()
