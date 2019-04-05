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
from six.moves import xrange
from six import PY2

import pysmt.operators as op
from pysmt.shortcuts import Symbol, FreshSymbol, And, Not, GT, Function, Plus
from pysmt.shortcuts import Bool, TRUE, Real, LE, FALSE, Or, Equals, Implies
from pysmt.shortcuts import Solver
from pysmt.shortcuts import get_env, get_model, is_valid, is_sat, get_implicant
from pysmt.typing import BOOL, REAL, FunctionType
from pysmt.test import TestCase, skipIfSolverNotAvailable, skipIfNoSolverForLogic
from pysmt.test import main
from pysmt.test.examples import get_example_formulae
from pysmt.exceptions import (SolverReturnedUnknownResultError,
                              InternalSolverError, NoSolverAvailableError,
                              ConvertExpressionError, UndefinedLogicError,
                              PysmtTypeError, PysmtValueError)
from pysmt.logics import QF_UFLIRA, QF_BOOL, QF_LRA, AUTO, QF_BV
from pysmt.logics import convert_logic_from_string


class TestBasic(TestCase):

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_create_and_solve(self):
        solver = Solver(logic=QF_BOOL)

        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))

        g = f.substitute({varB:varA})
        solver.add_assertion(g)
        res = solver.solve()
        self.assertFalse(res, "Formula was expected to be UNSAT")

        h = And(g, Bool(False))
        simp_h = h.simplify()
        self.assertEqual(simp_h, Bool(False))

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_is_sat(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        g = f.substitute({varB:varA})

        self.assertUnsat(g, logic=QF_BOOL,
                         msg="Formula was expected to be UNSAT")

        for solver in get_env().factory.all_solvers():
            self.assertUnsat(g, solver_name=solver,
                             msg="Formula was expected to be UNSAT")

    # This test works only if is_sat requests QF_BOOL as logic, since
    # that is the only logic handled by BDDs
    @skipIfSolverNotAvailable("bdd")
    def test_get_logic_in_is_sat(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        self.assertSat(f, logic=AUTO)

    @skipIfSolverNotAvailable("bdd")
    def test_default_logic_in_is_sat(self):
        factory = get_env().factory
        factory.default_logic = QF_BOOL

        self.assertEqual(factory.default_logic, QF_BOOL)
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        self.assertSat(f)

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_get_model_unsat(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)
        f = And(varA, Not(varB))
        g = f.substitute({varB:varA})

        res = get_model(g, logic=QF_BOOL)
        self.assertIsNone(res, "Formula was expected to be UNSAT")

        for solver in get_env().factory.all_solvers(logic=QF_BOOL):
            res = get_model(g, solver_name=solver)
            self.assertIsNone(res, "Formula was expected to be UNSAT")

    @skipIfNoSolverForLogic(QF_LRA)
    def test_get_model_sat(self):
        varA = Symbol("A", BOOL)
        varX = Symbol("X", REAL)
        f = And(varA, Equals(varX, Real(8)))

        res = get_model(f, logic=QF_LRA)
        self.assertIsNotNone(res, "Formula was expected to be SAT")
        self.assertTrue(res.get_value(varA) == TRUE())
        self.assertTrue(res.get_value(varX) == Real(8))

        for solver in get_env().factory.all_solvers(logic=QF_LRA):
            res = get_model(f, solver_name=solver)
            self.assertIsNotNone(res, "Formula was expected to be SAT")
            self.assertTrue(res.get_value(varA) == TRUE())
            self.assertTrue(res.get_value(varX) == Real(8))

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_get_implicant_unsat(self):
        varA = Symbol("A", BOOL)
        varB = Symbol("B", BOOL)

        f = And(varA, Not(varB))
        g = f.substitute({varB:varA})

        for solver in get_env().factory.all_solvers(logic=QF_BOOL):
            res = get_implicant(g, solver_name=solver)
            self.assertIsNone(res, "Formula was expected to be UNSAT")

    @skipIfNoSolverForLogic(QF_LRA)
    def test_get_implicant_sat(self):
        varA = Symbol("A", BOOL)
        varX = Symbol("X", REAL)
        f = And(varA, Equals(varX, Real(8)))

        for solver in get_env().factory.all_solvers(logic=QF_LRA):
            res = get_implicant(f, solver_name=solver)
            self.assertIsNotNone(res, "Formula was expected to be SAT")
            self.assertValid(Implies(res, f), logic=QF_LRA)

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_get_py_value(self):
        varA = Symbol("A", BOOL)

        with Solver(logic=QF_BOOL) as s:
            s.add_assertion(varA)
            s.solve()
            self.assertTrue(s.get_py_value(varA))

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_incremental(self):
        a = Symbol('a', BOOL)
        b = Symbol('b', BOOL)
        c = Symbol('c', BOOL)

        for name in get_env().factory.all_solvers(logic=QF_BOOL):
            with Solver(name) as solver:
                solver.add_assertion(Or(a, b))
                solver.add_assertion(Or(Not(b), c))
                self.assertTrue(solver.solve())
                try:
                    solver.push(1)
                except NotImplementedError:
                    # if push not implemented, pop shouldn't be either
                    self.assertRaises(NotImplementedError, solver.pop)
                    continue

                solver.add_assertion(And(Not(a), Not(c)))
                self.assertFalse(solver.solve())
                solver.pop(1)
                self.assertTrue(solver.solve())
                solver.add_assertion(FALSE())
                self.assertFalse(solver.solve())
                solver.reset_assertions()
                solver.add_assertion(a)
                self.assertTrue(solver.solve())

    @skipIfSolverNotAvailable("msat")
    def test_examples_msat(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if not logic.quantifier_free: continue
            if not logic.theory.linear: continue
            if logic.theory.strings: continue

            v = is_valid(f, solver_name='msat', logic=logic)
            s = is_sat(f, solver_name='msat', logic=logic)
            self.assertEqual(validity, v, f)
            self.assertEqual(satisfiability, s, f)

    @skipIfSolverNotAvailable("cvc4")
    def test_examples_cvc4(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if not logic.theory.linear: continue
            if logic.theory.arrays_const: continue
            try:
                v = is_valid(f, solver_name='cvc4', logic=logic)
                s = is_sat(f, solver_name='cvc4', logic=logic)
                self.assertEqual(validity, v, f)
                self.assertEqual(satisfiability, s, f)
            except SolverReturnedUnknownResultError:
                # CVC4 does not handle quantifiers in a complete way
                self.assertFalse(logic.quantifier_free)
            except NoSolverAvailableError:
                # Logic is not supported by CVC4
                pass

    @skipIfSolverNotAvailable("yices")
    def test_examples_yices(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if not logic.quantifier_free: continue
            if not logic.theory.linear: continue
            if logic.theory.strings: continue
            if logic.theory.arrays: continue

            v = is_valid(f, solver_name='yices', logic=logic)
            s = is_sat(f, solver_name='yices', logic=logic)
            self.assertEqual(validity, v, f)
            self.assertEqual(satisfiability, s, f)

    @skipIfSolverNotAvailable("btor")
    def test_examples_btor(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if not logic.quantifier_free: continue
            if logic.theory.strings: continue
            if logic.theory.integer_arithmetic: continue
            if logic.theory.real_arithmetic: continue
            if logic.theory.custom_type: continue

            v = is_valid(f, solver_name='btor', logic=logic)
            s = is_sat(f, solver_name='btor', logic=logic)
            self.assertEqual(validity, v, f)
            self.assertEqual(satisfiability, s, f)

    def do_model(self, solver_name):
        for (f, _, satisfiability, logic) in get_example_formulae():
            if satisfiability and not logic.theory.uninterpreted and logic.quantifier_free:
                try:
                    with Solver(name=solver_name, logic=logic) as s:
                        s.add_assertion(f)

                        check = s.solve()
                        self.assertTrue(check)

                        # Ask single values to the solver
                        subs = {}
                        for d in f.get_free_variables():
                            m = s.get_value(d)
                            subs[d] = m

                        simp = f.substitute(subs).simplify()
                        self.assertEqual(simp, TRUE(), "%s -- %s :> %s" % (f, subs, simp))

                        # Ask the eager model
                        subs = {}
                        model = s.get_model()
                        for d in f.get_free_variables():
                            m = model.get_value(d)
                            subs[d] = m

                        simp = f.substitute(subs).simplify()
                        self.assertEqual(simp, TRUE())
                except NoSolverAvailableError:
                    pass

    @skipIfSolverNotAvailable("cvc4")
    def test_model_cvc4(self):
        self.do_model("cvc4")

    @skipIfSolverNotAvailable("z3")
    def test_model_z3(self):
        self.do_model("z3")

    @skipIfSolverNotAvailable("msat")
    def test_model_msat(self):
        self.do_model("msat")

    @skipIfSolverNotAvailable("yices")
    def test_model_yices(self):
        self.do_model("yices")

    @skipIfSolverNotAvailable("picosat")
    def test_model_picosat(self):
        self.do_model("picosat")

    @skipIfSolverNotAvailable("z3")
    def test_tactics_z3(self):
        from z3 import Tactic, Then

        my_tactic = lambda ctx : Then(Tactic('simplify', ctx),
                                      Tactic('propagate-values', ctx),
                                      Tactic('elim-uncnstr', ctx))

        for (f, validity, satisfiability, logic) in get_example_formulae():
            if not logic.theory.linear: continue
            if not logic.quantifier_free: continue
            if logic.theory.strings: continue
            if logic.theory.bit_vectors: continue
            s = Solver(name='z3')
            z3_f = s.converter.convert(f)
            simp_z3_f = my_tactic(s.z3.ctx)(z3_f)
            simp_f = s.converter.back(simp_z3_f.as_expr())
            v = is_valid(simp_f)
            s = is_sat(simp_f)
            self.assertEqual(v, validity, (f, simp_f))
            self.assertEqual(s, satisfiability, (f, simp_f))

    @skipIfSolverNotAvailable("z3")
    def test_examples_z3(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            try:
                v = is_valid(f, solver_name='z3', logic=logic)
                s = is_sat(f, solver_name='z3', logic=logic)

                self.assertEqual(validity, v, f)
                self.assertEqual(satisfiability, s, f)
            except NoSolverAvailableError:
                # Trying to solve a logic that mathsat does not support
                theory = logic.theory
                assert theory.strings

    def test_examples_by_logic(self):
        for (f, validity, satisfiability, logic) in get_example_formulae():
            if len(get_env().factory.all_solvers(logic=logic)) > 0:
                try:
                    v = is_valid(f, logic=logic)
                    s = is_sat(f, logic=logic)
                    self.assertEqual(validity, v, f.serialize())
                    self.assertEqual(satisfiability, s, f.serialize())
                except SolverReturnedUnknownResultError:
                    s = Solver(logic=logic)
                    print(s, logic, f.serialize())
                    self.assertFalse(logic.quantifier_free,
                                     "Unkown result are accepted only on "\
                                     "Quantified formulae")

    def test_examples_get_implicant(self):
        for (f, _, satisfiability, logic) in get_example_formulae():
            if logic.quantifier_free:
                for sname in get_env().factory.all_solvers(logic=logic):
                    f_i = get_implicant(f, logic=logic, solver_name=sname)
                    if satisfiability:
                        self.assertValid(Implies(f_i, f), logic=logic, msg=(f_i, f))
                    else:
                        self.assertIsNone(f_i)

    def test_solving_under_assumption(self):
        v1, v2 = [FreshSymbol() for _ in xrange(2)]
        xor = Or(And(v1, Not(v2)), And(Not(v1), v2))

        for name in get_env().factory.all_solvers():
            with Solver(name=name) as solver:
                solver.add_assertion(xor)
                res1 = solver.solve(assumptions=[v1, Not(v2)])
                model1 = solver.get_model()
                res2 = solver.solve(assumptions=[Not(v1), v2])
                model2 = solver.get_model()
                res3 = solver.solve(assumptions=[v1, v2])
                self.assertTrue(res1)
                self.assertTrue(res2)
                self.assertFalse(res3)

                self.assertEqual(model1.get_value(v1), TRUE())
                self.assertEqual(model1.get_value(v2), FALSE())
                self.assertEqual(model2.get_value(v1), FALSE())
                self.assertEqual(model2.get_value(v2), TRUE())

    def test_solving_under_assumption_theory(self):
        x = Symbol("x", REAL)
        y = Symbol("y", REAL)
        v1 = GT(x, Real(10))
        v2 = LE(y, Real(2))
        xor = Or(And(v1, Not(v2)), And(Not(v1), v2))

        for name in get_env().factory.all_solvers(logic=QF_LRA):
            with Solver(name=name) as solver:
                solver.add_assertion(xor)
                res1 = solver.solve(assumptions=[v1, Not(v2)])
                model1 = solver.get_model()
                res2 = solver.solve(assumptions=[Not(v1), v2])
                model2 = solver.get_model()
                res3 = solver.solve(assumptions=[v1, v2])
                self.assertTrue(res1)
                self.assertTrue(res2)
                self.assertFalse(res3)

                self.assertEqual(model1.get_value(v1), TRUE())
                self.assertEqual(model1.get_value(v2), FALSE())
                self.assertEqual(model2.get_value(v1), FALSE())
                self.assertEqual(model2.get_value(v2), TRUE())

    def test_solving_under_assumption_mixed(self):
        x = Symbol("x", REAL)
        v1 = GT(x, Real(10))
        v2 = Symbol("v2", BOOL)
        xor = Or(And(v1, Not(v2)), And(Not(v1), v2))

        for name in get_env().factory.all_solvers(logic=QF_UFLIRA):
            with Solver(name=name) as solver:
                solver.add_assertion(xor)
                res1 = solver.solve(assumptions=[v1, Not(v2)])
                model1 = solver.get_model()
                res2 = solver.solve(assumptions=[Not(v1), v2])
                model2 = solver.get_model()
                res3 = solver.solve(assumptions=[v1, v2])
                self.assertTrue(res1)
                self.assertTrue(res2)
                self.assertFalse(res3)

                self.assertEqual(model1.get_value(v1), TRUE())
                self.assertEqual(model1.get_value(v2), FALSE())
                self.assertEqual(model2.get_value(v1), FALSE())
                self.assertEqual(model2.get_value(v2), TRUE())

    def test_add_assertion(self):
        r = FreshSymbol(REAL)
        f1 = Plus(r, r)
        f2 = GT(r, r)

        for sname in get_env().factory.all_solvers(logic=QF_LRA):
            with Solver(name=sname) as solver:
                with self.assertRaises(PysmtTypeError):
                    solver.add_assertion(f1)
                self.assertIsNone(solver.add_assertion(f2))

    def test_get_value_of_function(self):
        """get_value on a function should raise an exception."""
        h = Symbol("h", FunctionType(REAL, [REAL, REAL]))

        h_0_0 = Function(h, (Real(0), Real(1)))
        f = GT(h_0_0, Real(0))
        for sname in get_env().factory.all_solvers(logic=QF_UFLIRA):
            with Solver(name=sname) as solver:
                solver.add_assertion(f)
                res = solver.solve()
                self.assertTrue(res)
                with self.assertRaises(PysmtTypeError):
                    solver.get_value(h)
                self.assertIsNotNone(solver.get_value(h_0_0))

    def test_get_value_of_function_bool(self):
        """Proper handling of models with functions with bool args."""
        hr = Symbol("hr", FunctionType(REAL, [BOOL, REAL, REAL]))
        hb = Symbol("hb", FunctionType(BOOL, [BOOL, REAL, REAL]))

        hr_0_1 = Function(hr, (TRUE(), Real(0), Real(1)))
        hb_0_1 = Function(hb, (TRUE(), Real(0), Real(1)))
        hbx = Function(hb, (Symbol("x"), Real(0), Real(1)))
        f = GT(hr_0_1, Real(0))
        g = hb_0_1

        for sname in get_env().factory.all_solvers(logic=QF_UFLIRA):
            with Solver(name=sname) as solver:
                # First hr
                solver.add_assertion(f)
                res = solver.solve()
                self.assertTrue(res)
                v = solver.get_value(hr_0_1)
                self.assertIsNotNone(solver.get_value(v))
                # Now hb
                solver.add_assertion(g)
                res = solver.solve()
                self.assertTrue(res)
                v = solver.get_value(hb_0_1)
                self.assertIsNotNone(v in [TRUE(), FALSE()])
                # Hbx
                solver.add_assertion(hbx)
                res = solver.solve()
                self.assertTrue(res)
                v = solver.get_value(hbx)
                self.assertIsNotNone(v in [TRUE(), FALSE()])
                # Get model
                model = solver.get_model()
                self.assertIsNotNone(model)

    @skipIfSolverNotAvailable("msat")
    def test_msat_converter_on_msat_error(self):
        import mathsat
        from pysmt.solvers.msat import MathSAT5Solver, MSatConverter


        env = get_env()
        msat = MathSAT5Solver(env, logic=QF_UFLIRA)

        class NewConverter(MSatConverter):
            def walk_plus(self, formula, args, **kwargs):
                res = mathsat.MSAT_MAKE_ERROR_TERM()
                return res

        new_converter = NewConverter(env, msat.msat_env)

        r, s = FreshSymbol(REAL), FreshSymbol(REAL)
        f1 = GT(r, s)
        f2 = Plus(r, s)

        t1 = new_converter.convert(f1)
        self.assertFalse(mathsat.MSAT_ERROR_TERM(t1))

        with self.assertRaises(InternalSolverError):
            new_converter.convert(f2)

    @skipIfSolverNotAvailable("msat")
    def test_msat_preferred_variable(self):
        a, b, c = [Symbol(x) for x in "abc"]
        na, nb, nc = [Not(Symbol(x)) for x in "abc"]

        f = And(Implies(a, And(b,c)),
                Implies(na, And(nb,nc)))

        s1 = Solver("msat")
        s1.add_assertion(f)
        s1.set_preferred_var(a, True)
        self.assertTrue(s1.solve())
        self.assertTrue(s1.get_value(a).is_true())

        s2 = Solver("msat")
        s2.add_assertion(f)
        s2.set_preferred_var(a, False)
        self.assertTrue(s2.solve())
        self.assertTrue(s2.get_value(a).is_false())

        # Show that calling without polarity still works
        # This case is harder to test, because we only say
        # that the split will occur on that variable first.
        s1.set_preferred_var(a)

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_conversion_error(self):
        from pysmt.type_checker import SimpleTypeChecker
        add_dwf = get_env().add_dynamic_walker_function
        create_node = get_env().formula_manager.create_node

        # Create a node that is not supported by any solver
        idx = op.new_node_type()
        x = Symbol("x")
        add_dwf(idx, SimpleTypeChecker, SimpleTypeChecker.walk_bool_to_bool)
        invalid_node = create_node(idx, args=(x,x))

        for sname in get_env().factory.all_solvers(logic=QF_BOOL):
            with self.assertRaises(ConvertExpressionError):
                is_sat(invalid_node, solver_name=sname, logic=QF_BOOL)

    @skipIfNoSolverForLogic(QF_LRA)
    def test_logic_as_string(self):
        self.assertEqual(convert_logic_from_string("QF_LRA"), QF_LRA)
        if PY2:
            self.assertEqual(convert_logic_from_string(unicode("QF_LRA")),
                             QF_LRA)
        with self.assertRaises(UndefinedLogicError):
            convert_logic_from_string("PAPAYA")
        self.assertIsNone(convert_logic_from_string(None))

        x = Symbol("x")
        self.assertTrue(is_sat(x, logic="QF_LRA"))
        with self.assertRaises(UndefinedLogicError):
            is_sat(x, logic="PAPAYA")
        self.assertTrue(is_sat(x, logic=None))
        self.assertTrue(is_sat(x))

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_solver_options(self):
        # Options are kwargs of the Solver() constructor.
        solver = Solver(logic=QF_BOOL, incremental=True)
        self.assertIsNotNone(solver)
        # Options are enforced at construction time
        if type(solver).__name__ == 'CVC4Solver':
            # We skip the rest of the test on CVC4 1.7 because its
            # python wrapper crashes if an unknown option is provided.
            # See: https://github.com/CVC4/CVC4/issues/2810
            return
        with self.assertRaises(TypeError):
            Solver(logic=QF_BOOL, invalid_option=False)
        with self.assertRaises(PysmtValueError):
            Solver(logic=QF_BOOL, solver_options={'invalid': None})

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_options_random_seed(self):
        for sname in get_env().factory.all_solvers(logic=QF_BOOL):
            if sname in ["btor", "bdd"]:
                with self.assertRaises(PysmtValueError):
                    Solver(name=sname, random_seed=42)
            else:
                s = Solver(name=sname, random_seed=42)
                self.assertIsNotNone(s)

    @skipIfSolverNotAvailable("picosat")
    def test_picosat_options(self):
        from pysmt.solvers.pico import PicosatOptions
        from tempfile import TemporaryFile
        x, y = Symbol("x"), Symbol("y")
        with TemporaryFile() as fout:
            solver_options = {'preprocessing': False,
                              'enable_trace_generation': False,
                              'output': fout,
                              'global_default_phase': PicosatOptions.GLOBAL_DEFAULT_PHASE_FALSE,
                              'more_important_lit': [x],
                              'less_important_lit': [y],
                              'propagation_limit': 100,
                              'verbosity': 1,
                          }
            with Solver(name='picosat', solver_options=solver_options) as s:
                s.add_assertion(And(x,y))
                s.solve()

    @skipIfNoSolverForLogic(QF_BOOL)
    def test_incremental_is_sat(self):
        from pysmt.exceptions import SolverStatusError
        with Solver(incremental=False, logic=QF_BOOL) as s:
            self.assertTrue(s.is_sat(Symbol("x")))
            with self.assertRaises(SolverStatusError):
                s.is_sat(Not(Symbol("x")))

    @skipIfSolverNotAvailable("btor")
    def test_btor_options(self):
        for (f, _, sat, logic) in get_example_formulae():
            if logic == QF_BV:
                solver = Solver(name="btor",
                                solver_options={"rewrite-level":0,
                                                "fun:dual-prop":1,
                                                "eliminate-slices":1})
                solver.add_assertion(f)
                res = solver.solve()
                self.assertTrue(res == sat)

if __name__ == '__main__':
    main()
