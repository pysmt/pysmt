# This is the tutorial example of pySMT.
#
# This example shows how to:
# 1. Deal with Theory atoms
# 2. Specify a solver in the shortcuts (get_model, is_sat etc.)
# 3. Obtain an print a model
#
#
# The goal of the puzzle is to assign a value from 1 to 10 to each letter s.t.
#    H+E+L+L+O = W+O+R+L+D = 25
#
from pysmt.shortcuts import Symbol, And, GE, LT, Plus, Equals, Int, get_model
from pysmt.typing import INT

hello = [Symbol(s, INT) for s in "hello"]
world = [Symbol(s, INT) for s in "world"]
letters = set(hello+world)
domains = And([And(GE(l, Int(1)),
                   LT(l, Int(10))) for l in letters])

sum_hello = Plus(hello) # n-ary operators can take lists
sum_world = Plus(world) # as arguments
problem = And(Equals(sum_hello, sum_world),
              Equals(sum_hello, Int(25)))
formula = And(domains, problem)

print("Serialization of the formula:")
print(formula)

model = get_model(formula)
if model:
    print(model)
else:
    print("No solution found")
