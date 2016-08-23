from pysmt.shortcuts import Symbol
from pysmt.typing import INT

h = Symbol("H", INT)

domain = (1 <= h) & (10 >= h)
