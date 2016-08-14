# This is a different take on the puzzle.py example
#
# This examples shows how to:
# 1. Enable and use infix notation
# 2. Use a solver context
#
from pysmt.shortcuts import Symbol, And, Plus, Int
from pysmt.shortcuts import Solver
from pysmt.typing import INT

# Infix-Notation is automatically enabled whenever you import pysmt.shortcuts.
#
# To enable it without using shortcuts, do:
#
#   from pysmt.environment import get_env
#   get_env().enable_infix_notation = True
#
# Similarly, you can disable infix_notation to prevent its accidental use.
#

hello = [Symbol(s, INT) for s in "hello"]
world = [Symbol(s, INT) for s in "world"]
letters = set(hello+world)

# Infix notation for Theory atoms does the overloading of python
# operator. For boolean connectors, we use e.g., x.And(y) This
# increases readability without running into problems of operator
# precedence.
#
# Note how you can mix prefix and infix notation.
domains = And([(Int(1) <= l).And(Int(10) >= l) for l in letters])

sum_hello = Plus(hello) # n-ary operators can take lists
sum_world = Plus(world) # as arguments
problem = (sum_hello.Equals(sum_world)).And(sum_hello.Equals(Int(25)))
formula = domains.And(problem)

print("Serialization of the formula:")
print(formula)

# A context (with-statment) lets python take care of creating and
# destroying the solver.
with Solver() as solver:
    solver.add_assertion(formula)
    if solver.solve():
        for l in letters:
            print("%s = %s" %(l, solver.get_value(l)))
    else:
        print("No solution found")
