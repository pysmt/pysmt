import io
from six import PY2
from fractions import Fraction

def is_python_integer(n):
    if PY2:
        return type(n) == long or type(n) == int
    else:
        return type(n) == int


def is_python_rational(n):
    return is_python_integer(n) or type(n) == float or type(n) == Fraction


def is_python_boolean(n):
    return n is True or n is False


def BufferedTextReader(fname):
    if PY2:
        return io.BufferedReader(io.FileIO(fname, 'r'))
    else:
        return io.TextIOWrapper(open(fname, 'rb'))
