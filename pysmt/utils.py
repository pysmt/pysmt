import sys
from six import PY2

def is_integer(n):
    if PY2:
        return type(n) == long or type(n) == int
    else:
        return type(n) == int
