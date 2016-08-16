# This example shows how to define a generic SMT-LIB solver, and use
# it within pySMT. The example looks for mathsat in /tmp, you can
# create a symlink there.
#
# Using this process you can experiment with any SMT-LIB 2 compliant
# solver even if it does not have python bindings, or has not been
# integrated with pySMT.
#
# Note: When using the SMT-LIB wrapper, you can only use logics
# supported by pySMT. If the version of pySMT in use does not support
# Arrays, then you cannot represent arrays.
#

# To define a Generic Solver you need to provide:
#
# - A name to associate to the solver
# - The path to the script + Optional arguments
# - The list of logics supported by the solver
#
# It is usually convenient to wrap the solver in a simple shell script.
# See examples for Z3, Mathsat and Yices in pysmt/test/smtlib/bin/*.template
#
from pysmt.logics import QF_UFLRA, QF_UFIDL, QF_LRA, QF_IDL, QF_LIA
from pysmt.shortcuts import get_env, GT, Solver, Symbol
from pysmt.typing import REAL, INT
from pysmt.exceptions import NoSolverAvailableError

name = "mathsat" # Note: The API version is called 'msat'
path = ["/tmp/mathsat"] # Path to the solver
logics = [QF_UFLRA, QF_UFIDL] # Some of the supported logics

env = get_env()

# Add the solver to the environment
env.factory.add_generic_solver(name, path, logics)

r, s = Symbol("r", REAL), Symbol("s", REAL)
p, q = Symbol("p", INT), Symbol("q", INT)

f_lra = GT(r, s)
f_idl = GT(p, q)

# PySMT takes care of recognizing that QF_LRA can be solved by a QF_UFLRA solver.
with Solver(name=name, logic=QF_LRA) as s:
    res = s.solve()
    assert res, "Was expecting '%s' to be SAT" % f_lra


with Solver(name=name, logic=QF_IDL) as s:
    s.add_assertion(f_idl)
    res = s.solve()
    assert res, "Was expecting '%s' to be SAT" % f_idl

try:
    with Solver(name=name, logic=QF_LIA) as s:
        pass
except NoSolverAvailableError:
    # If we ask for a logic that is not contained by any of the
    # supported logics an exception is thrown
    print("%s does not support QF_LIA" % name)
