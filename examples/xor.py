# Verify the correctness of a rewriting using Bit-Vectors
#
# The following expression computes the xor of y and x:
#  (((y & x)*-2) + (y + x)
#
# We verify that this is indeed the case
#
# Source: https://yurichev.com/writings/SAT_SMT_draft-EN.pdf
#
from pysmt.shortcuts import SBV, Symbol, is_valid, Equals
from pysmt.typing import BV16

# X and Y are BV of width 16
x = Symbol("x", BV16)
y = Symbol("y", BV16)

r1 = y + x            # add   r1,ry,rx
r2 = y & x            # and   r2,ry,rx
r3 = r2 * SBV(-2, 16) # mul   r3,r2,-2
r4 = r3 + r1          # add   r4,r3,r1

# x xor y == r4
real_xor = x ^ y
assert is_valid(real_xor.Equals(r4))
