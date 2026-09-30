# This snippet requires an unsat-core-capable solver (see the
# documentation of the ``UnsatCoreSolver`` shortcut, e.g. the result
# of ``Factory.all_unsat_core_solvers()``).
#
# The shortcut ``get_unsat_core()`` asserts each clause of the input
# separately and returns a subset of them (the UNSAT core) whose
# conjunction is still unsatisfiable. The core need not be minimal.

from pysmt.shortcuts import Symbol, Int, Equals, get_unsat_core
from pysmt.typing import INT

a = Symbol("a", INT)

# Two contradictory facts: ``a = 1`` and ``a = 2``.
# Each of them is satisfiable on its own, but together they are not.

core = get_unsat_core([Equals(a, Int(1)), Equals(a, Int(2))])
print("The conjunction of the two formulae is UNSAT. The unsat core is:")
for f in sorted(core, key=lambda f: f.serialize()):
    print("  ", f.serialize())
