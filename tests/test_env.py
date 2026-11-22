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

from pysmt.shortcuts import Symbol
import pysmt.factory
from pysmt.optimization.goal import (MaxMinGoal, MaximizationGoal,
                                     MaxSMTGoal, MinimizationGoal,
                                     MinMaxGoal)
from pysmt.rewritings import CNFizer, NNFizer, PrenexNormalizer
from pysmt.smtlib.printers import to_smtlib
from pysmt.smtlib.script import smtlibscript_from_formula
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

    @staticmethod
    def _local_env_formula():
        """A BV formula built in a fresh, non-global environment."""
        env = Environment()
        mgr = env.formula_manager
        # width 7 is not one of the globally pre-registered BV types, so
        # each environment holds its own instance of it.
        bv7 = env.type_manager.BVType(7)
        x = mgr.Symbol("x", bv7)
        y = mgr.Symbol("y", bv7)
        f = mgr.And(mgr.BVULT(x, y), mgr.Not(mgr.Equals(x, y)))
        return env, x, y, f

    def test_no_global_env_pollution(self):
        """Walkers must not build nodes in the global environment.

        Library internals used to reach for the global environment via
        FNode.simplify/substitute/get_free_variables/get_type, creating
        nodes owned by the wrong formula manager.
        """
        global_env = get_env()
        env, x, y, f = self._local_env_formula()
        self.assertNotEqual(global_env, env)
        mgr = env.formula_manager
        qf = mgr.Exists([x], f)

        global_size = len(global_env.formula_manager.formulae)
        for res in (env.simplifier.simplify(f),
                    env.simplifier.simplify(qf),
                    env.substituter.substitute(f, {x: mgr.BV(1, 7)}),
                    CNFizer(env).convert_as_formula(f),
                    NNFizer(env).convert(f),
                    PrenexNormalizer(env).normalize(qf)):
            self.assertIn(res, mgr)
        self.assertEqual(len(global_env.formula_manager.formulae), global_size,
                         "the global environment was polluted")

    def test_types_come_from_given_env(self):
        """Derived types must be built by the environment's type manager."""
        env, x, y, _ = self._local_env_formula()
        mgr = env.formula_manager
        self.assertIs(env.stc.get_type(mgr.BVConcat(x, y)),
                      env.type_manager.BVType(14))
        arr = mgr.Array(env.type_manager.BVType(7), mgr.BV(0, 7))
        self.assertIs(env.stc.get_type(arr),
                      env.type_manager.ArrayType(env.type_manager.BVType(7),
                                                 env.type_manager.BVType(7)))

    def test_smtlib_printers_accept_env(self):
        """SMT-LIB serialization must not need the global environment."""
        global_env = get_env()
        env, _, _, f = self._local_env_formula()
        global_size = len(global_env.formula_manager.formulae)

        to_smtlib(f, env=env)
        to_smtlib(f, daggify=False, env=env)
        buf = StringIO()
        smtlibscript_from_formula(f, env=env).serialize(buf, env=env)
        self.assertIn("bvult", buf.getvalue())

        self.assertEqual(len(global_env.formula_manager.formulae), global_size,
                         "the global environment was polluted")

    def test_goals_use_given_env(self):
        """Optimization goals must build their terms in the given env."""
        global_env = get_env()
        env, x, y, _ = self._local_env_formula()
        mgr = env.formula_manager
        global_size = len(global_env.formula_manager.formulae)

        maxsmt = MaxSMTGoal(real_weights=False, env=env)
        maxsmt.add_soft_clause(mgr.BVULT(x, y), mgr.Int(1))

        goals = [MaximizationGoal(x, env=env),
                 MinimizationGoal(x, env=env),
                 MinMaxGoal([x, y], env=env),
                 MaxMinGoal([x, y], env=env),
                 maxsmt]
        for goal in goals:
            self.assertIs(goal.env, env)
            self.assertIn(goal.term(), mgr)
            goal.get_logic()

        self.assertEqual(len(global_env.formula_manager.formulae), global_size,
                         "the global environment was polluted")

    def test_solver_factory_preferences(self):
        env = get_env()

        factory = env.factory
        self.assertEqual(factory.preferences, pysmt.factory.DEFAULT_PREFERENCES)

        for solver_name in factory.all_solvers(logic=logics.QF_UFLIRA):
            factory.set_solver_preference_list([solver_name])
            self.assertEqual(factory.preferences['Solver'], [solver_name])
            solver = factory.get_solver(logic=logics.QF_UFLIRA)
            self.assertTrue(isinstance(solver, factory.all_solvers()[solver_name]))

        factory.set_solver_preference_list(['nosolver'])
        with self.assertRaises(NoSolverAvailableError):
            factory.get_solver()

        for qelim_name in factory.all_quantifier_eliminators():
            factory.set_qelim_preference_list([qelim_name])
            self.assertEqual(factory.preferences['Quantifier Eliminator'], [qelim_name])
            qelim = factory.get_quantifier_eliminator(logic=logics.BOOL)
            self.assertTrue(isinstance(qelim, factory.all_quantifier_eliminators()[qelim_name]))

        factory.set_qelim_preference_list(['nosolver'])
        with self.assertRaises(NoSolverAvailableError):
            factory.get_quantifier_eliminator()


    def test_nonlinear_demotes_mathsat(self):
        # The MathSAT family is the last resort on nonlinear logics, but still
        # picked when it is the only capable solver.
        pick = get_env().factory._pick_favorite
        available = {'msat': 'MSAT', 'z3': 'Z3'}
        prefs = ['msat', 'z3']
        self.assertEqual(pick(prefs, available, available, logics.QF_NRA), 'Z3')
        self.assertEqual(pick(prefs, available, available, logics.QF_LRA), 'MSAT')
        only_msat = {'msat': 'MSAT'}
        self.assertEqual(pick(prefs, only_msat, only_msat, logics.QF_NRA), 'MSAT')


if __name__ == '__main__':
    main()
