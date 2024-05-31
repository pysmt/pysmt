# Portfolio solving makes it possible to run multiple solvers in
# parallel.  As soon as the first solver completes, all other solvers
# are stopped.  Current support for portfolio is mostly focused on
# one-shot calls, with only functional incrementality: the interface
# looks incremental, but internally there is no guarantee of re-using
# the solver state.
#
from pysmt.shortcuts import Symbol, Implies, TRUE, FALSE, Not

x, y = Symbol("x"), Symbol("y")
f = Implies(x, y)

# The first example shows how to use multiple solvers in the with the
# is_sat shortcut
#
from pysmt.shortcuts import is_sat

# We enable logging to see what is going on behind the scenes:
import logging
_info = logging.getLogger(__name__).info
logging.basicConfig(level=logging.DEBUG)

# A solver set is an iterable of solver names or pairs of
# solvers+options (See next example)

_info("Example 1: is_sat")
solvers_set = ["z3", "yices", "msat"]
res = is_sat(f, portfolio=solvers_set)
assert res is True

# Behind the scenes, pySMT launched 3 processes and solved the
# expression in parallel.
#
# The is_sat shortcut is useful for prototyping and exploration, but
# we typically need more control over the solver. The Portfolio class
# behaves as a solver and as such implements most of the methods of a
# regular solver.
from pysmt.shortcuts import Portfolio
from pysmt.logics import QF_UFLIRA

# The options given to the Portfolio will be passed to all solvers, in
# particular, we are enabling incrementality and model generation.

_info("Example 2: Portfolio()")
with Portfolio(solvers_set,
               logic=QF_UFLIRA,
               incremental=True,
               generate_models=True) as s:
    s.add_assertion(f)
    s.push()
    s.add_assertion(x)
    res = s.solve()
    v_y = s.get_value(y)
    assert v_y is TRUE()

    s.pop()
    s.add_assertion(Not(y))
    res = s.solve()
    v_x = s.get_value(x)
    assert v_x is FALSE()

# Portfolio can also be useful to tweak heuristics of the solvers.
# For supported solver options, please refer to the solver
# documentation. This is an area of pySMT that could use additional
# feedback and help!

_info("Example 3: Portfolio w options")
with Portfolio([("msat", {"random_seed": 1}),
                ("msat", {"random_seed": 17}),
                ("msat", {"random_seed": 42}),
                "cvc5", "yices"],
               logic=QF_UFLIRA,
               incremental=False,
               generate_models=False) as s:
    res = s.is_sat(f)
    assert res is True
