from pysmt.shortcuts import *
from pysmt.typing import REAL
from pysmt.exceptions import DeltaSATError

dreal = Solver(name="dreal")

r = Symbol('r', REAL)
s = Symbol('s', REAL)

f = And(r <= s)
dreal.add_assertion(f)

try:
    res = dreal.solve()
except DeltaSATError:
    # Test if the formula is really SAT
    is_model = dreal.get_model().get_value(f)
    print(dreal.get_model())

print(res)
