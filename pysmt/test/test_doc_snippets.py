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
import runpy
import unittest

from pysmt.test import (TestCase, skipIfSolverNotAvailable,
                        skipIfNoSolverForLogic,
                        skipIfNoUnsatCoreSolverForLogic, main)
from pysmt.logics import QF_LIA


SNIPPETS_DIR = os.path.join(os.path.dirname(__file__),
                            "..", "..", "docs", "code_snippets")


# The docs are not shipped with the package, so skip when run from an install.
@unittest.skipIf(not os.path.isdir(SNIPPETS_DIR), "docs/ not available")
class TestDocSnippets(TestCase):

    def setUp(self):
        super().setUp()
        # Match the default environment a reader gets from pysmt.shortcuts.
        self.env.enable_infix_notation = True

    def run_snippets(self, *names):
        for name in names:
            with self.subTest(snippet=name):
                runpy.run_path(os.path.join(SNIPPETS_DIR, name + ".py"),
                               run_name="__main__")

    def test_no_solver(self):
        self.run_snippets("hello_world_opening", "hello_world_infix")

    @skipIfNoSolverForLogic(QF_LIA)
    def test_qf_lia(self):
        self.run_snippets("hello_world_is_sat", "hello_world_get_model",
                          "hello_world_qf_lia")

    @skipIfSolverNotAvailable("z3")
    def test_z3(self):
        self.run_snippets("hello_world")

    @skipIfNoUnsatCoreSolverForLogic(QF_LIA)
    def test_unsat_cores(self):
        self.run_snippets("unsat_core", "unsat_core_named",
                          "unsat_core_assumptions")

    def test_all_snippets_are_tested(self):
        tested = {"hello_world_opening", "hello_world_infix",
                  "hello_world_is_sat", "hello_world_get_model",
                  "hello_world_qf_lia", "hello_world", "unsat_core",
                  "unsat_core_named", "unsat_core_assumptions"}
        found = {f[:-3] for f in os.listdir(SNIPPETS_DIR) if f.endswith(".py")}
        self.assertEqual(found, tested,
                         "Add new docs/code_snippets files to this test")


if __name__ == '__main__':
    main()
