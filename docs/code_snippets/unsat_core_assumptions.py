# This snippet requires an unsat-core-capable solver (see the
# documentation of the ``UnsatCoreSolver`` shortcut, e.g. the result
# of ``Factory.all_unsat_core_solvers()``).
#
# ``solve()`` accepts an optional list of *assumptions*.  Assumptions
# are not asserted as part of the theory; they are extra constraints
# that only apply to this particular solving session.
#
# Contract (settled in pysmt/pysmt#680):
#
# * in both unsat cores modes, ``get_unsat_core()`` reports the
#   assumptions that are part of the core;
# * ``get_named_unsat_core()`` never reports assumptions, because they
#   carry no name.
#
# This mirrors the split in SMT-LIB between ``get-unsat-core`` and
# ``get-unsat-assumptions``.

from pysmt.shortcuts import Symbol, UnsatCoreSolver
from pysmt.typing import INT

a = Symbol("a", INT)

# The base theory: ``a >= 1``.  On its own it is satisfiable, but the
# assumption ``a <= 0`` contradicts it.

with UnsatCoreSolver(logic="QF_LIA",
                     unsat_cores_mode="named") as solver:
    solver.add_assertion(a >= 1, named="a_positive")
    if not solver.solve([a <= 0]):
        print("UNSAT under the assumption a <= 0.")
        core = solver.get_unsat_core()
        print("Core (named assertions plus the assumption):")
        for f in sorted(core, key=lambda f: f.serialize()):
            print("  ", f.serialize())
        named = solver.get_named_unsat_core()
        print("Named core (note: the assumption is not in it):")
        for name, f in named.items():
            print("  %s -> %s" % (name, f.serialize()))
