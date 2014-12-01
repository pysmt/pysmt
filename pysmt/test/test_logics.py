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

import pysmt.logics
from pysmt.logics import get_logic_by_name, get_logic, most_generic_logic
from pysmt.logics import PYSMT_LOGICS
from pysmt.exceptions import UndefinedLogicError, NoSolverAvailableError
from pysmt.shortcuts import Solver, get_env


class TestLogic(unittest.TestCase):

    def test_get_logic_by_name(self):
        for l in pysmt.logics.LOGICS:
            l_out = get_logic_by_name(l.name)
            self.assertEquals(l_out, l,
                              "Expecting %s, got %s instead" % \
                              (l, l_out))

    def test_get_logic_by_name_error(self):
        with self.assertRaises(UndefinedLogicError):
            get_logic_by_name("SuperLogic")

    def test_get_logic(self):
        for l in pysmt.logics.LOGICS:
            l_out = get_logic(quantifier_free=l.quantifier_free,
                              arrays=l.arrays,
                              bit_vectors=l.bit_vectors,
                              floating_point=l.floating_point,
                              integer_arithmetic=l.integer_arithmetic,
                              real_arithmetic=l.real_arithmetic,
                              integer_difference=l.integer_difference,
                              real_difference=l.real_difference,
                              linear=l.linear,
                              non_linear=l.non_linear,
                              uninterpreted=l.uninterpreted)
            self.assertEquals(l_out, l,
                              "Expected %s, got %s instead" % \
                              (l, l_out))

    def test_get_logics_min(self):
        tests = [
            (pysmt.logics.AUFLIA, get_logic(arrays=True,
                                            uninterpreted=True,
                                            linear=True,
                                            integer_arithmetic=True)),
            (pysmt.logics.AUFLIRA, get_logic(arrays=True,
                                             uninterpreted=True,
                                             linear=True,
                                             integer_arithmetic=True,
                                             real_arithmetic=True)),
            (pysmt.logics.AUFNIRA, get_logic(arrays=True,
                                             uninterpreted=True,
                                             non_linear=True,
                                             integer_arithmetic=True,
                                             real_arithmetic=True)),
            (pysmt.logics.LRA, get_logic(linear=True,
                                         real_arithmetic=True)),
            (pysmt.logics.QF_ABV, get_logic(quantifier_free=True,
                                            arrays=True,
                                            bit_vectors=True)),
            (pysmt.logics.QF_AUFBV, get_logic(quantifier_free=True,
                                              arrays=True,
                                              uninterpreted=True,
                                              bit_vectors=True)),
            (pysmt.logics.QF_AUFLIA, get_logic(quantifier_free=True,
                                               arrays=True,
                                               uninterpreted=True,
                                               linear=True,
                                               integer_arithmetic=True)),
            (pysmt.logics.QF_UFLRA, get_logic(quantifier_free=True,
                                              uninterpreted=True,
                                              linear=True,
                                              real_arithmetic=True)),
            (pysmt.logics.QF_RDL, get_logic(quantifier_free=True,
                                            real_arithmetic=True,
                                            real_difference=True)),
            (pysmt.logics.QF_UFIDL, get_logic(quantifier_free=True,
                                              uninterpreted=True,
                                              integer_arithmetic=True,
                                              integer_difference=True)),
        ]

        for t in tests:
            self.assertEquals(t[0], t[1],
                              "Expected %s, got %s instead" % \
                              (t[0].name, t[1].name))


    def test_get_solver_by_logic(self):
        if len(get_env().factory.all_solvers()) > 0:
            s = Solver(logic=pysmt.logics.UFLIRA)
            self.assertIsNotNone(s)
        else:
            with self.assertRaises(NoSolverAvailableError):
                Solver(logic=pysmt.logics.UFLIRA)

        with self.assertRaises(NoSolverAvailableError):
            Solver(logic="p")

        with self.assertRaises(NoSolverAvailableError):
            Solver(name='msat', logic=pysmt.logics.QF_BV)


    def test_most_generic(self):
        from pysmt.logics import QF_LIA, LIA, UFLIRA, LRA
        self.assertTrue(QF_LIA < LIA)
        self.assertTrue(LIA < UFLIRA)
        self.assertTrue(UFLIRA > QF_LIA)
        self.assertTrue(UFLIRA >= UFLIRA)
        self.assertFalse(LRA >= LIA)
        self.assertFalse(LRA <= LIA)
        mgl = most_generic_logic([QF_LIA, LIA, LRA, UFLIRA])
        self.assertEquals(mgl, UFLIRA)
        mgl = most_generic_logic(PYSMT_LOGICS)
        self.assertEquals(mgl, UFLIRA)

if __name__ == "__main__":
    unittest.main()
