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
from pysmt.shortcuts import get_env, get_free_variables
from pysmt.shortcuts import Symbol, Implies, And, Not
from pysmt.test.examples import get_example_formulae
from pysmt.test import TestCase, main
from pysmt.oracles import get_logic
from pysmt.typing import BOOL, Type, INT, FunctionType


class TestOracles(TestCase):

    def test_quantifier_oracle(self):
        oracle = get_env().qfo
        for (f, _, _, logic) in get_example_formulae():
            is_qf = oracle.is_qf(f)
            self.assertEqual(is_qf, logic.quantifier_free, f)

    def test_get_logic(self):
        for example in get_example_formulae():
            target_logic = example.logic
            res = get_logic(example.expr)
            self.assertEqual(res, target_logic, "%s - %s != %s" % \
                              (example.expr, target_logic, res))

    def test_get_free_vars(self):
        x, y = Symbol("x"), Symbol("y")
        f = Implies(x, And(y, Not(x)))

        s = get_free_variables(f)
        self.assertEqual(set([x,y]), s)

    def test_atoms_oracle(self):
        oracle = get_env().ao
        stc = get_env().stc
        for (f, _, _, _) in get_example_formulae():
            atoms = oracle.get_atoms(f)
            if ( atoms is not None):
                if len(f.get_free_variables()) > 0:
                    self.assertTrue(len(atoms) > 0)
            for a in atoms:
                ty = stc.get_type(a)
                self.assertEqual(ty, BOOL)
                self.assertFalse(a.is_and())
                self.assertFalse(a.is_or())
                self.assertFalse(a.is_not())
                self.assertFalse(a.is_iff())
                self.assertFalse(a.is_quantifier())

    def test_types_oracle_examples(self):
        oracle = get_env().typeso
        for (f, _, _, _) in get_example_formulae():
            types_all = oracle.get_types(f)
            types_custom = oracle.get_types(f, custom_only=True)
            # Custom types are a subset of all types
            s1 = set(types_all)
            s2 = set(types_custom)
            self.assertTrue(s1.issuperset(s2))

            # Compare logics with types
            theory = self.env.theoryo.get_theory(f)
            if len(f.get_free_variables()) == 0:
                continue
            if theory.arrays:
                self.assertTrue(any(x.is_array_type() for x in types_all),
                                (f, types_all))
            if theory.bit_vectors:
                self.assertTrue(any(x.is_bv_type() for x in types_all),
                                (f, types_all))
            if theory.integer_arithmetic:
                self.assertTrue(any(x.is_int_type() for x in types_all),
                                (f, types_all))
            if theory.real_arithmetic:
                self.assertTrue(any(x.is_real_type() for x in types_all),
                                (f, types_all))

    def test_types_oracle(self):
        get_env().enable_infix_notation = True

        S = Type("S")
        U = Type("U", 1)
        B = Type("B", 2)
        csort = B(U(S),
                  B(BOOL, S))
        v = Symbol("v", csort)
        types_all = self.env.typeso.get_types(v)
        types_custom = self.env.typeso.get_types(v, custom_only=True)
        self.assertIsNotNone(types_all)
        # Only BOOL does not appear in types_custom
        self.assertTrue(len(types_all) == 5)
        self.assertTrue(len(types_custom) == 4)

        # Types are in partial order: simpler is earlier
        idx_S = types_custom.index(S)
        idx_US = types_custom.index(U(S))
        idx_BBS = types_custom.index(B(BOOL, S))
        idx_BUSBBS = types_custom.index(B(U(S), B(BOOL, S)))

        self.assertIsNotNone(idx_S)
        self.assertIsNotNone(idx_US)
        self.assertIsNotNone(idx_BBS)
        self.assertIsNotNone(idx_BUSBBS)

        self.assertEqual(types_custom[0], S)
        self.assertTrue(idx_S < idx_US)
        self.assertTrue(idx_US < idx_BUSBBS)
        self.assertTrue(idx_BBS < idx_BUSBBS)

    def test_type_oracles_constants(self):
        mgr = self.env.formula_manager
        f = mgr.Plus(mgr.Int(5), mgr.Int(6))
        types_all = self.env.typeso.get_types(f)
        self.assertEqual(types_all, [INT])

    def test_theory_oracle_on_functions(self):
        from pysmt.logics import QF_UFIDL

        mgr = self.env.formula_manager
        ftype = FunctionType(INT, (BOOL,))
        f = mgr.Symbol("f", ftype)
        f_1 = mgr.Function(f, (mgr.TRUE(),))
        theory = self.env.theoryo.get_theory(f_1)
        self.assertEqual(theory, QF_UFIDL.theory)



if __name__ == '__main__':
    main()
