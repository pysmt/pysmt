from pysmt.shortcuts import Symbol, LE, GE, And, Int
from pysmt.typing import INT

h = Symbol("H", INT)

# domain = (1 <= h) & (10 >= h)
domain = And(LE(Int(1), h), GE(Int(10), h))
