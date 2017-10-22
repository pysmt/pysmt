# Perform Quantifier Elimination of an LRA formula
#
# This example requires MathSAT or Z3 to be installed
#
# In Quantifier Elimination (QE) we take a formula with quantifiers,
# and rewrite it in an equivalent formula without quantifiers
#
# Example:
#  forall x. exists y. phi(x,y) = exists y . phi'(y)
#
#  If x is a Boolean variable, then we can apply Shannon's expansion
#  to perform the quantifier elimination
#
#  phi'(y) = exists y. phi(FALSE, y) /\ phi(TRUE, y)
#
#  The semantics of forall tells us that the expression must be
#  satisfiable for both values of x: x=TRUE and x=FALSE.
#
# If x is a Rational variable, we cannot enumerate all its possible
# values. One technique to deal with quantifier elimination in LRA is
# called Fourier-Motzkin [1]
#
# [1] https://en.wikipedia.org/wiki/Fourier%E2%80%93Motzkin_elimination
from pysmt.shortcuts import Symbol, ForAll, Exists, qelim
from pysmt.typing import REAL

# (x,y) is a point in a 2d space.

x = Symbol("x", REAL)
y = Symbol("y", REAL)

# phi(x,y) is true if (x,y) is within a given area. In particular, we
# pick a rectangular area of size 5x10: the bottom-left corner has
# coordinate (0,0), the top-right has coordinate (5, 10).
#

rect = (x >= 0.0) & (x <= 5.0) & \
      (y >= 0.0) & (y <= 10.0)

# The first expression that we build asks if for any value of x we can
# define a value of y that would satisfy the expression above.
f1 = ForAll([x], Exists([y], rect))

# This is false, because we know that if we pick x=11, the formula
# above cannot be satisfied. Eliminating all the symbols in an
# expression is the same as solving the expression.
#
# The function to perform quantifier elimination is called qelim:
qf_f1 = qelim(f1)
print(qf_f1)

# We can restrict the values that x can adopt by imposing them as
# precondition.
#
# If we perform quantifier elimination on this expression we obtain an
# unsurprising result:
#
f2 = ForAll([x], Exists([y], ((x >= 0.0) & (x <= 4.0)).Implies(rect)))
qf_f2 = qelim(f2)
print(qf_f2)

# The power of quantifier elimination lies in the possibility of
# representing sets of solutions. Lets introduce a new symbol z, that
# represents the grid distance (aka Manhattan distance) of (x,y) from
# the origin.
z = Symbol("z", REAL)
distance= z.Equals(x + y)

# We want to characterize the set of points in the rectangle, in terms
# of their grid distance from the origin. In other words, we want to
# constraint z to be able to assume values that are possible within
# the rectangle. We want a formula in z that is satisfiable iff there
# is a value for z s.t.  exists a value for x,y within the rectangle.
# An example of the type of information that we expect to see is the
# maximum and minimum value of z.
f3 = Exists([x,y], rect & distance)
qe_f3 = qelim(f3)
print(qe_f3.serialize())

# Depending on the solver in use you might get a different
# result. Try: qelim(f3, solver_name="msat_fm")
#
# MathSAT Fourier Motzkin (FM) returns a compact result: (0.0
# <= z) & (z <= 15.0) , meaning that the further point in grid
# distance is at most 15.0 units away from the origin.
#
# By definition, the expression obtained after performing quantifier
# elimination is in the quantifier free fragment of the logic.  It is
# therefore possible to remove the quantifiers using qelim, and use a
# solver that does not support quantifiers natively to solve the new
# formula.
from pysmt.oracles import get_logic
print(get_logic(f3), get_logic(qe_f3))
