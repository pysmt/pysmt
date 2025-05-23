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
import pytest
from io import StringIO

from pysmt.shortcuts import get_env
from pysmt.logics import QF_LIA, QF_LRA
from pysmt.test import TestCase, skipIfNoOptimizerForLogic, skipIfNoSolverForLogic
from pysmt.test import main
from pysmt.test.optimization_utils import generate_examples_with_solvers, solve_given_example, OptimizationTypes, get_non_diverging_optimizers
from pysmt.test.smtlib.parser_utils import omt_test_cases_from_smtlib_test_set
from pysmt.cmd.shell import PysmtShell


class TestOmtLibSolver(TestCase):
    @skipIfNoSolverForLogic(QF_LRA)
    def test_base(self):
        txt = """(declare-fun x () Real)
        (assert (> x 0))
        (check-sat)"""
        f_in = StringIO(txt)
        f_out = StringIO()
        args = ["-l", "QF_LRA"]
        pysmtshell = PysmtShell(args)
        pysmtshell.smtlib_solver(f_in, f_out)
        self.assertEqual(f_out.getvalue(), "sat\n")

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_omt_minimize(self):
        txt = """(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (and
        (<= x 10)
        (<= 0 x)
        (<= y 10)
        (<= 4 y)
))
(minimize x)
(check-sat)
(get-objectives)"""
        for oname in get_non_diverging_optimizers(logic=QF_LRA):
                f_in = StringIO(txt)
                f_out = StringIO()
                args = ["-o", oname]
                pysmtshell = PysmtShell(args)
                pysmtshell.smtlib_solver(f_in, f_out)
                self.assertIn(
                f_out.getvalue(),
                ["""sat
(objectives
  (x 0.0)
)
""", """sat
(objectives
  (x 0)
)
"""]
        )

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_omt_minmax(self):
        txt = """(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (and
        (<= x 10)
        (<= 0 x)
        (<= y 11)
        (<= 4 y)
))
(minmax x y)
(check-sat)
(get-objectives)"""
        f_in = StringIO(txt)
        f_out = StringIO()
        for oname in get_non_diverging_optimizers(logic=QF_LRA):
                args = ["-o", oname, "-l", "QF_LRA"]
                pysmtshell = PysmtShell(args)
                pysmtshell.smtlib_solver(f_in, f_out)
                self.assertIn(
                f_out.getvalue(),
                ["""sat
(objectives
  (((x <= y) ? y : x) 4.0)
)
""", """sat
(objectives
  (((x <= y) ? y : x) 4)
)
"""]
        )

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_omt_box(self):
        txt = """(set-option :opt.priority box)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (and
        (<= x 10)
        (<= 0 x)
        (<= y 10)
        (<= 0 y)
        (<= z 10)
        (<= 0 z)
))
(minimize (- x y))
(minimize (- y x))
(check-sat)
(get-objectives)"""
        f_in = StringIO(txt)
        f_out = StringIO()
        args = ["-o", "auto"]
        pysmtshell = PysmtShell(args)
        pysmtshell.smtlib_solver(f_in, f_out)
        self.assertEqual(
            f_out.getvalue(),
            """sat
(objectives
  ((x - y) -10)
  ((y - x) -10)
)
""",
        )

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_omt_box_unsat(self):
        txt = """(set-option :opt.priority box)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (and
        (<= x 10)
        (<= 11 x)
        (<= y 10)
        (<= 0 y)
        (<= z 10)
        (<= 0 z)
))
(minimize (- x y))
(minimize (- y x))
(check-sat)
(get-objectives)"""
        f_in = StringIO(txt)
        f_out = StringIO()
        args = ["-o", "auto"]
        pysmtshell = PysmtShell(args)
        pysmtshell.smtlib_solver(f_in, f_out)
        self.assertEqual(
            f_out.getvalue(),
            """unsat
(objectives
)
""",
        )

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_omt_lex(self):
        txt = """(set-option :opt.priority lex)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (and
        (<= x 10)
        (<= 0 x)
        (<= y 10)
        (<= 0 y)
        (<= z 10)
        (<= 0 z)
))
(minimize (- x y))
(minimize (- y x))
(check-sat)
(get-objectives)"""
        f_in = StringIO(txt)
        f_out = StringIO()
        args = ["-o", "auto"]
        pysmtshell = PysmtShell(args)
        pysmtshell.smtlib_solver(f_in, f_out)
        self.assertEqual(
            f_out.getvalue(),
            """sat
(objectives
  ((x - y) -10)
  ((y - x) 10)
)
""",
        )

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_omt_int_01(self):
        txt = """(set-option :opt.priority lex)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (and
        (<= x 10)
        (<= 0 x)
        (<= y 10)
        (<= 0 y)
        (<= z 10)
        (<= 0 z)
))
(minimize (- x y))
(minimize (- y x))
(check-sat)
(get-objectives)
(set-option :opt.priority box)
(check-sat)
(get-objectives)
(maxmin x y)
(check-sat)
(get-objectives)"""
        f_in = StringIO(txt)
        f_out = StringIO()
        args = ["-o", "auto"]
        pysmtshell = PysmtShell(args)
        pysmtshell.smtlib_solver(f_in, f_out)
        self.assertEqual(
            f_out.getvalue(),
            """sat
(objectives
  ((x - y) -10)
  ((y - x) 10)
)
sat
(objectives
  ((x - y) -10)
  ((y - x) -10)
)
sat
(objectives
  ((x - y) -10)
  ((y - x) -10)
  (((x <= y) ? x : y) 10)
)
""",
        )

    @skipIfNoOptimizerForLogic(QF_LRA)
    def test_omt_real_01(self):
        txt = """(set-option :opt.priority lex)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
(assert (and
        (<= x 10.0)
        (<= 0.0 x)
        (<= y 10.0)
        (<= 0.0 y)
        (<= z 10.0)
        (<= 0.0 z)
))
(minimize (- x y))
(minimize (- y x))
(check-sat)
(get-objectives)
(set-option :opt.priority box)
(check-sat)
(get-objectives)
(maxmin x y)
(check-sat)
(get-objectives)"""
        f_in = StringIO(txt)
        f_out = StringIO()
        for oname in get_non_diverging_optimizers(logic=QF_LRA):
                args = ["-o", oname, '-l', 'QF_LRA']
                factory = get_env().factory
                factory.all_optimizers()
                pysmtshell = PysmtShell(args)
                pysmtshell.smtlib_solver(f_in, f_out)
                self.assertEqual(
                        f_out.getvalue(),
                        """sat
(objectives
  ((x - y) -10.0)
  ((y - x) 10.0)
)
sat
(objectives
  ((x - y) -10.0)
  ((y - x) -10.0)
)
sat
(objectives
  ((x - y) -10.0)
  ((y - x) -10.0)
  (((x <= y) ? x : y) 10.0)
)
""",
                )

    @skipIfNoOptimizerForLogic(QF_LIA)
    def test_omt_lex_unsat(self):
        txt = """(set-option :opt.priority lex)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (and
        (<= x 10)
        (<= 11 x)
        (<= y 10)
        (<= 0 y)
        (<= z 10)
        (<= 0 z)
))
(minimize (- x y))
(minimize (- y x))
(check-sat)
(get-objectives)"""
        f_in = StringIO(txt)
        f_out = StringIO()
        args = ["-o", "auto"]
        pysmtshell = PysmtShell(args)
        pysmtshell.smtlib_solver(f_in, f_out)
        self.assertEqual(
            f_out.getvalue(),
            """unsat
(objectives
)
""",
        )


test_to_skip = {
        ("QF_LRA - smtlib2_boxed.smt2", OptimizationTypes.LEXICOGRAPHIC, "optimsat"), # error return wrong maximization of z (should be 24, returns 0); seems like a bug in optimsat; have to try optimsat alone; with integers instead of reals it works
        ("QF_LIA - smtlib2_allsat.smt2", OptimizationTypes.PARETO, "optimsat"), # error that happens only if test_optimizing is done before this test
        ("QF_LIA - smtlib2_load_objective_model.smt2", OptimizationTypes.PARETO, "optimsat"), # error that happens only if test_optimizing is done before this test
}
@pytest.mark.parametrize(
    "optimization_example, solver_name",
    generate_examples_with_solvers(omt_test_cases_from_smtlib_test_set()),
)
def test_parsed_examples(optimization_example, solver_name):
    solve_given_example(
        optimization_example,
        solver_name,
        test_to_skip,
    )


if __name__ == "__main__":
    main()
