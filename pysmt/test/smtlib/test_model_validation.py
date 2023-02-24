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

from io import StringIO

from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.utils import SmtLibModelValidationSimplifier
from pysmt.shortcuts import get_env
from pysmt.typing import FunctionType
from pysmt.test import TestCase, main

class TestModelValidation(TestCase):

    def setUp(self):
        super(TestModelValidation, self).setUp()
        self.env = get_env()
        self.tm = self.env.type_manager
        self.fm = self.env.formula_manager


    def test_basic(self):
        model_source ="""\
(model
  ;; universe for U:
  ;;   (as @val1 U) (as @val0 U)
  (define-fun b () U
    (as @val0 U))
  (define-fun a () U
    (as @val1 U))
  (define-fun f ((x!0 U)) U
    (ite (= x!0 (as @val1 U)) (as @val0 U)
      (as @val1 U)))
)
"""
        model_buf = StringIO(model_source)

        parser = SmtLibParser()
        simplifier = SmtLibModelValidationSimplifier(self.env)

        U = self.tm.Type('U', 0)

        a = self.fm.Symbol('a', U)
        b = self.fm.Symbol('b', U)
        f = self.fm.Symbol('f', FunctionType(U, [U]))
        formula = self.fm.And(self.fm.Not(self.fm.Equals(a, b)),
                              self.fm.Equals(self.fm.Function(f, [a]), b))

        model, interpretations = parser.parse_model(model_buf)
        simp = simplifier.simplify(formula.substitute(model, interpretations))
        self.assertEqual(simp, self.fm.TRUE())

    def test_basic2(self):
        model_source ="""\
(model
  ;; universe for U:
  ;;   (as @val1 U) (as @val0 U)
  (define-fun b () U
    (as @val0 U))
  (define-fun a () U
    (as @val1 U))
  (define-fun f ((x!0 U)) U
    (ite (= x!0 (as @val1 U)) (as @val0 U)
      (as @val1 U)))
)
"""
        model_buf = StringIO(model_source)

        parser = SmtLibParser()
        simplifier = SmtLibModelValidationSimplifier(self.env)

        U = self.tm.Type('U', 0)

        # We construct the model even befor symbols are constructed in pysmt
        model, interpretations = parser.parse_model(model_buf)

        a = self.fm.Symbol('a', U)
        b = self.fm.Symbol('b', U)
        f = self.fm.Symbol('f', FunctionType(U, [U]))
        formula = self.fm.And(self.fm.Not(self.fm.Equals(a, b)),
                              self.fm.Equals(self.fm.Function(f, [a]), b))

        simp = simplifier.simplify(formula.substitute(model, interpretations))
        self.assertEqual(simp, self.fm.TRUE())



if __name__ == '__main__':
    main()
