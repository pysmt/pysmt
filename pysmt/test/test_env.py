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
from pysmt.shortcuts import Symbol
import pysmt.factory
from pysmt.test import TestCase, main
from pysmt.typing import REAL
from pysmt.environment import Environment, pop_env, push_env, get_env
from pysmt.exceptions import NoSolverAvailableError
from pysmt import logics


class TestEnvironment(TestCase):

    def test_global_env_is_unique(self):
        env1 = get_env()
        env2 = get_env()
        self.assertEqual(env1, env2, "Global environment is not unique.")

    def test_stack_env(self):
        env1 = get_env()
        push_env()
        push_env(env1)

        self.assertEqual(env1, pop_env(), "Pushed environment was ignored.")
        env2  = get_env()
        self.assertIsNotNone(env2)
        self.assertNotEqual(env1, pop_env(), "New environment was not created.")


    def test_with_env(self):
        env1 = get_env()
        a1 = Symbol("A", REAL)
        with Environment():
            env2 = get_env()
            self.assertIsNotNone(env2, "Context should create an environment")
            self.assertNotEqual(env1, env2, "Context should create a new environment")
            a2 = Symbol("A", REAL)
            self.assertNotEqual(a1, a2, "Symbols in different context should differ")

        a3 = Symbol("A", REAL)
        self.assertEqual(a1, a3, "Exiting a context should restore the previous environment")


    def test_cannot_replace_global_walkers(self):
        env = get_env()

        # Check that environment contains standard walkers
        self.assertIsNotNone(env.formula_manager)
        self.assertIsNotNone(env.substituter)
        self.assertIsNotNone(env.simplifier)
        self.assertIsNotNone(env.serializer)
        self.assertIsNotNone(env.stc)

        # Cannot modify these elements
        with self.assertRaises(AttributeError):
            env.formula_manager = None

        with self.assertRaises(AttributeError):
            env.substituter = None

        with self.assertRaises(AttributeError):
            env.simplifier = None

        with self.assertRaises(AttributeError):
            env.serializer = None

        with self.assertRaises(AttributeError):
            env.stc = None

    def test_solver_factory_preferences(self):
        env = get_env()

        factory = env.factory
        self.assertEqual(factory.solver_preference_list,
                          pysmt.factory.DEFAULT_SOLVER_PREFERENCE_LIST)

        for solver_name in factory.all_solvers(logic=logics.QF_UFLIRA):
            factory.set_solver_preference_list([solver_name])
            self.assertEqual(factory.solver_preference_list, [solver_name])
            solver = factory.get_solver(logic=logics.QF_UFLIRA)
            self.assertTrue(isinstance(solver, factory.all_solvers()[solver_name]))

        factory.set_solver_preference_list(['nosolver'])
        with self.assertRaises(NoSolverAvailableError):
            factory.get_solver()

        for qelim_name in factory.all_quantifier_eliminators():
            factory.set_qelim_preference_list([qelim_name])
            self.assertEqual(factory.qelim_preference_list, [qelim_name])
            qelim = factory.get_quantifier_eliminator(logic=logics.BOOL)
            self.assertTrue(isinstance(qelim, factory.all_quantifier_eliminators()[qelim_name]))

        factory.set_qelim_preference_list(['nosolver'])
        with self.assertRaises(NoSolverAvailableError):
            factory.get_quantifier_eliminator()


if __name__ == '__main__':
    main()
