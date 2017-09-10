#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
import re
import itertools


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


def open_(fname):
    """Transparently handle .bz2 files."""
    if fname.endswith(".bz2"):
        import bz2
        if PY2:
            return bz2.BZ2File(fname, "r")
        else:
            return bz2.open(fname, "rt")
    return open(fname)
