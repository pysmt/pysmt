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
from pysmt.test import TestCase
from pysmt.shortcuts import And, Or, FALSE, TRUE, FreshSymbol, get_env
from pysmt.solvers.eager import EagerModel
from pysmt.typing import REAL, INT

class TestEagerModel(TestCase):

    def test_construction(self):
        """Build an eager model out of a dictionary"""

        x, y = FreshSymbol(), FreshSymbol()

        d = {x: TRUE(), y: FALSE()}

        model = EagerModel(assignment=d,
                           environment=get_env())

        self.assertEquals(model.get_value(x), TRUE())
        self.assertEquals(model.get_value(y), FALSE())
        self.assertEquals(model.get_value(And(x,y)), FALSE())

    def test_env_default_arguments(self):
        """Test use global env"""
        x = FreshSymbol()
        d = {x: TRUE()}

        model = EagerModel(d)
        self.assertEquals(model.get_value(x), TRUE())

    def test_result_is_const(self):
        """The result of get_value is a constant"""

        x, y = FreshSymbol(), FreshSymbol()
        d = {x:TRUE()}

        model = EagerModel(assignment=d)
        with self.assertRaises(TypeError):
            model.get_value(And(x,y))

        d2 = {x:TRUE(), y:x}
        model = EagerModel(assignment=d2)
        with self.assertRaises(TypeError):
            model.get_value(And(x,y))

    def test_complete_model(self):
        """Given a partial assignment, we can make a total model."""
        x, y = FreshSymbol(), FreshSymbol()
        r = FreshSymbol(REAL)
        p = FreshSymbol(INT)
        d = {x:TRUE()}

        model = EagerModel(assignment=d)
        model.complete_model([x,y,r,p])

        self.assertEquals(model.get_value(x), TRUE())
        self.assertEquals(model.get_value(Or(x,y)), TRUE())
        self.assertTrue(model.get_value(p).is_constant(INT))
        self.assertTrue(model.get_value(r).is_constant(REAL))


if __name__ == '__main__':
    import unittest
    unittest.main()
