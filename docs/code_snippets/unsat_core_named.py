# This snippet requires an unsat-core-capable solver (see the
# documentation of the ``UnsatCoreSolver`` shortcut, e.g. the result
# of ``Factory.all_unsat_core_solvers()``).
#
# When ``unsat_cores_mode="named"``, only assertions added with a
# ``named`` argument can be reported in the core. This is useful when
# the assertions come from different sources (different rules, a
# theory, user input, ...) and the core must be mapped back to the
# structure of the original problem.

from pysmt.shortcuts import Symbol, UnsatCoreSolver
from pysmt.typing import INT

a = Symbol("a", INT)

# ``a >= 1`` and ``a <= 0`` are contradictory.  Each assertion is given
# a name so that the core can be reported by name.

with UnsatCoreSolver(logic="QF_LIA",
                     unsat_cores_mode="named") as solver:
    solver.add_assertion(a >= 1, named="a_positive")
    solver.add_assertion(a <= 0, named="a_nonpositive")
    if not solver.solve():
        core = solver.get_named_unsat_core()
        print("The named unsat core:")
        for name, f in sorted(core.items()):
            print("  %s -> %s" % (name, f.serialize()))
