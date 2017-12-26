# This example requires a solver that supports QF_AUFLIRA
#  e.g. MathSat or Z3
#
# Theory combination is the possibility of mixing theories with an SMT
# problem. This goes beyond having subexpressions belonging to
# different theories, and really requires mixing theories in the same
# expression.
#
# In this example, we use four theories supported by pySMT:
# BitVectors, Integers, Reals, and Arrays.
#
#
from pysmt.shortcuts import Symbol, BV, Real, And, BVToNatural, ToReal
from pysmt.shortcuts import get_model
from pysmt.typing import BV8, REAL, INT, ArrayType

# We create a map from BitVectors to Reals, so that each bitvector
# value (interpreted as unary number) is equal to the Real
# value.
#
# The map is represented by an Array of type BV8 -> Real
map_type = ArrayType(BV8, REAL)
my_map = Symbol("my_map", map_type)

# Fill-up the map, by defining all 256 values:
for i in range(0, 255):
    my_map = my_map.Store(BV(i, 8), Real(i))

# We want to find find a value for which our relation does not work.
# In other words, we ask if there is a value for the bitvector
# s.t. the corresponding value in the array is different from the
# unary interpretation of the bitvector.
bv_var = Symbol("bv", BV8)
int_var = Symbol("int", INT)
real_var = Symbol("real", REAL)

f = And(
    # Convert the BV into INT
    int_var.Equals(BVToNatural(bv_var)),
    # Convert the INT into REAL
    real_var.Equals(ToReal(int_var)),
    # Compare the value stored in the map with the REAL value
    my_map.Select(bv_var).NotEquals(real_var)
    )

print(get_model(f)) # Indeed our range only gets up to 254!!!
