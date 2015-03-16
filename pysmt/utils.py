import io
from six import PY2

def is_integer(n):
    if PY2:
        return type(n) == long or type(n) == int
    else:
        return type(n) == int


def BufferedTextReader(fname):
    if PY2:
        return io.BufferedReader(io.FileIO(fname, 'r'))
    else:
        return io.TextIOWrapper(open(fname, 'rb'))
