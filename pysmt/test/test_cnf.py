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
import os
import pytest

from pysmt.shortcuts import Implies, is_sat, reset_env, Symbol, Iff, Select, ArrayType, INT, BOOL, And, get_env
from pysmt.rewritings import CNFizer
from pysmt.logics import QF_BOOL, QF_LRA, QF_LIA, QF_UFLIRA, QF_UFLRA, QF_ALIA
from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.test.examples import get_example_formulae
from pysmt.test.smtlib.parser_utils import SMTLIB_TEST_FILES, SMTLIB_DIR
from pysmt.smtlib.parser import get_formula_fname

class TestCnf(TestCase):

    def do_examples(self, logic):
        conv = CNFizer()
        for example in get_example_formulae():
            if example.logic != logic:
                continue
            cnf = conv.convert_as_formula(example.expr)

            self.assertValid(Implies(cnf, example.expr), logic=logic)

            res = is_sat(cnf, logic=logic)
            self.assertEqual(res, example.is_sat)


    @skipIfNoSolverForLogic(QF_BOOL)
    def test_examples_solving_bool(self):
        self.do_examples(QF_BOOL)

    @skipIfNoSolverForLogic(QF_LRA)
    def test_examples_solving_lra(self):
        self.do_examples(QF_LRA)

    @skipIfNoSolverForLogic(QF_LIA)
    def test_examples_solving_lia(self):
        self.do_examples(QF_LIA)

    @skipIfNoSolverForLogic(QF_UFLRA)
    def test_examples_solving_lia(self):
        self.do_examples(QF_UFLRA)

    @pytest.mark.slow
    @skipIfNoSolverForLogic(QF_LIA)
    def test_smtlib_cnf_small(self):
        cnt = 0
        max_cnt = 3
        for (logic, f, expected_result) in SMTLIB_TEST_FILES:
            if logic != QF_LIA:
                continue
            self._smtlib_cnf(f, logic, expected_result)
            cnt += 1
            if cnt == max_cnt:
                break

    @pytest.mark.slow
    @skipIfNoSolverForLogic(QF_UFLIRA)
    def test_smtlib_cnf(self):
        for (logic, f, expected_result) in SMTLIB_TEST_FILES:
            if logic != QF_UFLIRA:
                continue
            self._smtlib_cnf(f, logic, expected_result)

    def _smtlib_cnf(self, filename, logic, res_is_sat):
        reset_env()
        conv = CNFizer()
        smtfile = os.path.join(SMTLIB_DIR, filename)
        assert os.path.exists(smtfile)

        expr = get_formula_fname(smtfile)
        if not logic.quantifier_free:
            with self.assertRaises(NotImplementedError):
                conv.convert_as_formula(expr)
            return

        cnf = conv.convert_as_formula(expr)
        self.assertValid(Implies(cnf, expr), logic=logic)

        res = is_sat(cnf, logic=logic)
        self.assertEqual(res, res_is_sat)

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_implies(self):
        a,b,c,d = (Symbol(x) for x in "abcd")
        f = Implies(Iff(a, b), Iff(c, d))

        conv = CNFizer()
        cnf = conv.convert_as_formula(f)

        self.assertValid(Implies(cnf, f), logic=QF_BOOL)

    @skipIfNoSolverForLogic(QF_ALIA)
    def test_CNFizer_bool_theory(self):
        test_logic = QF_ALIA
        # (and (select boolean_array idx0) (select boolean_array idx1))
        boolean_array = Symbol("boolean_array", ArrayType(INT, BOOL))
        idx_0, idx_1 = Symbol("idx0", INT), Symbol("idx1", INT)
        f = And(
            Select(boolean_array, idx_0),
            Select(boolean_array, idx_1)
        )
        conv = CNFizer()
        cnf = conv.convert_as_formula(f)

        factory = get_env().factory
        for solver_name in factory.all_solvers(test_logic):
            # msat needs to be skipped. Check issue #807
            if solver_name in ("msat", "optimsat"):
                continue
            self.assertValid(
                Implies(cnf, f),
                solver_name=solver_name,
                logic=test_logic
            )

if __name__ == '__main__':
    main()
