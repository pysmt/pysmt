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
import warnings

from pysmt.test import SkipTest
from pysmt.shortcuts import get_env, reset_env
from pysmt.smtlib.parser import SmtLibParser, get_formula_fname
from pysmt.smtlib.script import check_sat_filter
from pysmt.logics import (QF_LIA, QF_LRA, LRA, QF_UFLIRA, QF_UFBV, QF_BV,
                          QF_ALIA, QF_ABV, QF_AUFLIA, QF_AUFBV, QF_NRA, QF_NIA,
                          UFBV, BV, QF_UF)
from pysmt.exceptions import NoSolverAvailableError, SolverReturnedUnknownResultError

def smtlib_tests(logic_pred):
    """Returns the smtlib instances matching the logic predicate"""
    tests = []
    for (logic, f, expected_result) in SMTLIB_TEST_FILES:
        smtfile = os.path.join(SMTLIB_DIR, f)
        if logic_pred(logic):
            tests.append((smtfile, logic, expected_result))
    return tests

# We use test generation in order to be able to obtain a separate
# test for each file.
# This is a feature of pytest. The correct way to invoke these
# tests is, e.g.,
#  $ python -m pytest pysmt/test/smtlib/test_parser_qf_lra.py
# The function 'execute_script_fname' is a general checker that
# parses and invokes a solver for the given smt file
def execute_script_fname(smtfile, logic, expected_result):
    """Read and call a Solver to solve the instance"""

    reset_env()
    Solver = get_env().factory.Solver
    parser = SmtLibParser()
    script = parser.get_script_fname(smtfile)
    try:
        solver = Solver(logic=logic, incremental=False,
                        generate_models=False)
        if logic == QF_UF and type(solver).__name__ == 'CVC4Solver':
            warnings.warn("Test (%s, %s) skipped because CVC4 can't handle QF_UF." % (logic, smtfile))
            return
        if logic == QF_UF and type(solver).__name__ == 'BoolectorSolver':
            warnings.warn("Test (%s, %s) skipped because Boolector can't handle QF_UF." % (logic, smtfile))
            return
        log = script.evaluate(solver)
    except NoSolverAvailableError:
        raise SkipTest("No solver for logic %s." % logic)
    except SolverReturnedUnknownResultError:
        if not logic.quantifier_free:
            warnings.warn("Test (%s, %s) could not be solved due to quantifiers." % (logic, smtfile))
            return
        raise

    res = check_sat_filter(log)
    assert expected_result == res


def formulas_from_smtlib_test_set(logics=None):
    """Returns a generator over the test-set of SMT-LIB files.

    Note: This resets the Environment at each call.
    """
    for (logic, fname, expected_result) in SMTLIB_TEST_FILES:
        if logics is not None and logic not in logics:
            continue
        reset_env()
        smtfile = os.path.join(SMTLIB_DIR, fname)
        formula = get_formula_fname(smtfile)
        yield (logic, fname, formula, expected_result)


# Constants to make definition of the benchmarks more readable
SAT   = True
UNSAT = False

# Directory where SMT-LIB files are saved
SMTLIB_DIR = "pysmt/test/smtlib/"
SMTLIB_TEST_FILES = [
    #
    # QF_LIA
    #
    (QF_LIA, "small_set/QF_LIA/prp-23-47.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-20-46.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-24-47.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-24-46.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-22-46.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-25-49.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-21-46.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-23-46.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-25-48.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-25-47.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-24-48.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/prp-25-46.smt2.bz2", UNSAT),
    (QF_LIA, "small_set/QF_LIA/issue_159.smt2.bz2", SAT),
    #
    # QF_LRA
    #
    (QF_LRA, "small_set/QF_LRA/uart-8.induction.cvc.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/uart-10.induction.cvc.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/uart-18.induction.cvc.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/uart-26.induction.cvc.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/uart-11.induction.cvc.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/uart-16.induction.cvc.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/uart-6.induction.cvc.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/uart-14.induction.cvc.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_11nodes.abstract.base.smt2.bz2", UNSAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_8nodes.synchro.base.smt2.bz2", UNSAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_3nodes.bug.induct.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_15nodes.abstract.base.smt2.bz2", UNSAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_12nodes.synchro.base.smt2.bz2", UNSAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_8nodes.missing.induct.smt2.bz2", SAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_14nodes.abstract.base.smt2.bz2", UNSAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_9nodes.abstract.base.smt2.bz2", UNSAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_8nodes.synchro.induct.smt2.bz2", UNSAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_4nodes.synchro.base.smt2.bz2", UNSAT),
    (QF_LRA, "small_set/QF_LRA/simple_startup_14nodes.synchro.induct.smt2.bz2", UNSAT),
    #
    # LRA
    #
    (LRA, "small_set/LRA/water_tank-node21140.smt2.bz2", UNSAT),
    (LRA, "small_set/LRA/water_tank-node22228.smt2.bz2", UNSAT),
    (LRA, "small_set/LRA/water_tank-node9350.smt2.bz2", UNSAT),
    (LRA, "small_set/LRA/intersection-example-simple.proof-node679466.smt2.bz2", UNSAT),
    (LRA, "small_set/LRA/intersection-example-simple.proof-node394346.smt2.bz2", UNSAT),
    (LRA, "small_set/LRA/water_tank-node24658.smt2.bz2", UNSAT),
    #
    # QF_LIRA
    #
    (QF_UFLIRA, "small_set/QF_LIRA/lira1.smt2.bz2", SAT),
    (QF_UFLIRA, "small_set/QF_LIRA/prp-20-46.smt2.bz2", SAT),
    #
    # QF_UFBV
    #
    #(QF_UFBV, "small_set/QF_UFBV/btfnt_atlas_out.smt2.bz2", UNSAT),
    (QF_UFBV, "small_set/QF_UFBV/calc2_sec2_bmc10.smt2.bz2", UNSAT),
    (QF_BV, "small_set/QF_BV/bench_4631_simp.smt2.bz2", SAT),
    (QF_BV, "small_set/QF_BV/bench_5200.smt2.bz2", UNSAT),
    (QF_BV, "small_set/QF_BV/bench_9457_simp.smt2.bz2", SAT),
    #
    # UFBV
    #
    (BV, "small_set/BV/AR-fixpoint-1.smt2.bz2", UNSAT),
    (BV, "small_set/BV/audio_ac97_common.cpp.smt2.bz2", SAT),
    (UFBV, "small_set/UFBV/small-swap2-fixpoint-5.smt2.bz2", SAT),
    (UFBV, "small_set/UFBV/small-seq-fixpoint-10.smt2.bz2", UNSAT),
    #
    # Arrays
    #
    (QF_ABV, "small_set/QF_ABV/a268test0002.smt2.bz2", SAT),
    (QF_ABV, "small_set/QF_ABV/com.galois.ecc.P384ECC64.group_add6.short.smt2.bz2", UNSAT),

    (QF_ALIA, "small_set/QF_ALIA/ios_t1_ios_np_sf_ai_00001_001.cvc.smt2.bz2", UNSAT),
    (QF_ALIA, "small_set/QF_ALIA/pointer-invalid-15.smt2.bz2", SAT),

    (QF_AUFBV, "small_set/QF_AUFBV/com.galois.ecc.P384ECC64.mod_div10.short.smt2.bz2", UNSAT),

    (QF_AUFLIA, "small_set/QF_AUFLIA/array_incompleteness1.smt2.bz2", UNSAT),
    (QF_AUFLIA, "small_set/QF_AUFLIA/swap_invalid_t1_pp_nf_ai_00002_002.cvc.smt2.bz2", SAT),
    #
    # QF_NRA
    #
    (QF_NRA, "small_set/QF_NRA/ball_count_2d_hill_simple.05.redlog_global_6.smt2.bz2", UNSAT),
    (QF_NRA, "small_set/QF_NRA/cos-problem-12-chunk-0004.smt2.bz2", SAT),
    (QF_NRA, "small_set/QF_NRA/simple_ballistics_reach.01.seq_lazy_linear_enc_global_10.smt2.bz2", UNSAT),
    #
    # QF_NIA
    #
    (QF_NIA, "small_set/QF_NIA/aproveSMT3509292547826641386.smt2.bz2", SAT),
    (QF_NIA, "small_set/QF_NIA/problem-000158.cvc.2.smt2.bz2", UNSAT),
    (QF_NIA, "small_set/QF_NIA/term-DtOD2C.smt2.bz2", SAT),
    #
    # QF_UF
    #
    (QF_UF, "small_set/QF_UF/test0.smt2.bz2", SAT),
]
