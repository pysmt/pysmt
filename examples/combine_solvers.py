# This example requires Z3 and MathSAT to be installed (but you can
#  replace MathSAT with any other solver for QF_LRA)
#
# This examples shows how to:
# 1. Define Real valued constants using floats and fractions
# 2. Perform quantifier elimination
# 3. Pass results from one solver to another
#
from pysmt.shortcuts import Symbol, Or, ForAll, GE, LT, Real, Plus
from pysmt.shortcuts import qelim, is_sat
from pysmt.typing import REAL

x, y, z = [Symbol(s, REAL) for s in "xyz"]

f = ForAll([x], Or(LT(x, Real(5.0)),
                   GE(Plus(x, y, z), Real((17,2))))) # (17,2) ~> 17/2
print("f := %s" % f)
#f := (forall x . ((x < 5.0) | (17/2 <= (x + y + z))))

qf_f = qelim(f, solver_name="z3")
print("Quantifier-Free equivalent: %s" % qf_f)
#Quantifier-Free equivalent: (7/2 <= (z + y))

res = is_sat(qf_f, solver_name="msat")
print("SAT check using MathSAT: %s" % res)
#SAT check using MathSAT: True
