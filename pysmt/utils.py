import io, re

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

def interactive_char_iterator(handle):
    c = handle.read(1)
    while c:
        yield c
        c = handle.read(1)


def set_bit(v, index, x):
    """Set the index:th bit of v to x, and return the new value."""
    mask = 1 << index
    if x:
        v |= mask
    else:
        v &= ~mask
    return v


def twos_complement(val, bits):
    """Retuns the 2-complemented value of val assuming bits word width"""
    if (val & (1 << (bits - 1))) != 0: # if sign bit is set
        val = val - (2 ** bits)        # compute negative value
    return val


_simple_symbol_prog = re.compile(r"^[~!@\$%\^&\*_\-+=<>\.\?\/A-Za-z][~!@\$%\^&\*_\-+=<>\.\?\/A-Za-z0-9]*$")
def quote(name, style='|'):
    if _simple_symbol_prog.match(name) is None:
        name = name.replace("\\", "\\\\").replace("%s" % style, "\\%s" % style)
        return "%s%s%s" % (style, name, style)
    else:
        return name

def unquote(name, style='|'):
    if name.startswith(style):
        if name.endswith(style):
            name = name.replace("%s" % style, "\\%s" % style).replace("\\\\", "\\")
            return name[1:-1]
        else:
            raise ValueError("Malformed Name")
    else:
        return name
