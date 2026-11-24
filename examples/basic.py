# Checking satisfiability of a formula.
#
# This example shows:
#  1. How to build a formula
#  2. How to perform substitution
#  3. Printing
#  4. Satisfiability checking
from pysmt.shortcuts import And, Not, Symbol, is_sat

varA = Symbol("A")  # Default type is Boolean
varB = Symbol("B")
f = And([varA, Not(varB)])
g = f.substitute({varB: varA})

res = is_sat(f)
assert res  # SAT
print(f"f := {f} is SAT? {res}")

res = is_sat(g)
print(f"g := {g} is SAT? {res}")
assert not res  # UNSAT
