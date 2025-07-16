import pytest

import os
from subprocess import run
from pysmt.shortcuts import (
    Solver as pysmt_solver,
    TRUE,
    FALSE,
    Not as pysmt_Not,
    Symbol,
    REAL,
    Real,
    Implies as pysmt_Implies,
    Div,
    LE,
    reset_env
)
from pysmt.test import skipIfSolverNotAvailable


class TestSMTSolvers:
    @skipIfSolverNotAvailable("cvc5")
    def test_cvc5_strange_formula3(self):
        reset_env()
        s = pysmt_solver("cvc5", logic="QF_NRA", random_seed=42)
        s.set_option("nl-ext", "none")
        x = Symbol("x", REAL)
        prop = pysmt_Implies(
            (Real(20) + (Real(-1) * x)) < Real(0),
            LE(
                (Div(Real(187), Real(464)) * ((Real(-50) + x) * (Real(-50) + x))),
                Div(Real(2093974), Real(5773)),
            ),
        )
        result = s.is_valid(prop)
        assert result is False, "CVC5 solver failed to handle negated linear formula 3"
