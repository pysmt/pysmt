# This example requires Z3 and MathSAT to be installed
#
# This examples shows how to:
# 1. Perform quantifier elimination
# 2. Pass results from one solver to another
#
from pysmt.shortcuts import Symbol, Or, ForAll, GE, Real, Plus
from pysmt.shortcuts import qelim, is_sat
from pysmt.typing import REAL

x, y, z = [Symbol(s, REAL) for s in "xyz"]

f = ForAll([x], Or(LT(x, Real(5)),
                   GE(Plus(x, y, z), Real(8))))
print("f := %s" % f)
#f := (forall x . ((x < 5.0) | (8.0 <= (x + y + z))))

qf_f = qelim(f, solver_name="z3")
print("Quantifier-Free equivalent: %s" % qf_f)
#Quantifier-Free equivalent: (3.0 <= (z + y))

res = is_sat(qf_f, solver_name="msat")
print("SAT check using MathSAT: %s" % res)
#SAT check using MathSAT: True
