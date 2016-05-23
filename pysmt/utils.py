import re
import io
import itertools
from six import PY2
from fractions import Fraction


def all_assignments(bool_variables, env):
    """Generates all possible assignments for a set of boolean variables."""
    mgr = env.formula_manager
    for set_ in powerset(bool_variables):
        yield dict((v, mgr.Bool(v in set_)) for v in bool_variables)


def powerset(elements):
    """Generates the powerset of the given elements set.

    E.g., powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)
    """
    return itertools.chain.from_iterable(itertools.combinations(elements, r)
                                         for r in range(len(elements)+1))

#
# Bit Operations
#
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


#
# Python Compatibility Functions
#
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


#
# Symbol (un)quoting
#
_simple_symbol_prog = re.compile(r"^[~!@\$%\^&\*_\-+=<>\.\?\/A-Za-z][~!@\$%\^&\*_\-+=<>\.\?\/A-Za-z0-9]*$")
_keywords = set(["Int", "Real", "Bool"])

def quote(name, style='|'):
    if name in _keywords or _simple_symbol_prog.match(name) is None:
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
