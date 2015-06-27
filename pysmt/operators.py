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
"""This module defines all the operators used internally by pySMT.

Note that other expressions can be built in the FormulaManager, but
they will be rewritten (during construction) in order to only use
these operators.
"""
from six.moves import xrange


ALL_TYPES = list(xrange(0,40))

(
FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF, # Boolean Logic (0-6)
SYMBOL, FUNCTION,                           # Symbols and functions calls (7-8)
REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT, # Constants (9-11)
PLUS, MINUS, TIMES,                         # LIA/LRA operators (12-14)
LE, LT, EQUALS,                             # LIA/LRA relations (15-17)
ITE,                                        # Term-ite (18)
TOREAL,                                     # LIRA toreal() function (19)
#
# MG: FLOOR? INT_MOD_CONGR?
#
# BV
BV_CONSTANT,                                # 20
BV_NOT, BV_AND, BV_OR, BV_XOR,              # Logical Operators on Bit
BV_CONCAT, BV_EXTRACT,                      #
BV_ULT, BV_ULE,                             # Comparison
BV_NEG, BV_ADD,                             # Basic arithmetic (31-33)
BV_MUL, BV_UDIV, BV_UREM,                   # Division/Multiplication (34-38)
BV_LSHL, BV_LSHR,                           # Shifts (39-41)
BV_ROL, BV_ROR,                             # Rotation (42-43)
BV_ZEXT, BV_SEXT,                           # Extension (44-45)
# BV Operators to be supported in the future
# BV_SLT, BV_SLE
# BV_COMP
# BV_SUB
# BV_SDIV
# BV_SREM
# BV_ASHR
) = ALL_TYPES

QUANTIFIERS = frozenset([FORALL, EXISTS])

BOOL_CONNECTIVES = frozenset([AND, OR, NOT, IMPLIES, IFF])

BOOL_OPERATORS = frozenset(QUANTIFIERS | BOOL_CONNECTIVES)

RELATIONS = frozenset([LE, LT, EQUALS, BV_ULE, BV_ULT])

CONSTANTS = frozenset([REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT, BV_CONSTANT])

BV_OPERATORS = frozenset([BV_CONSTANT, BV_NOT, BV_AND, BV_OR, BV_XOR,
                          BV_CONCAT, BV_EXTRACT, BV_ULT, BV_ULE, BV_NEG, BV_ADD, BV_MUL,
                          BV_UDIV, BV_UREM, BV_LSHL, BV_LSHR, BV_ROL, BV_ROR,
                          BV_ZEXT, BV_SEXT])

LIRA_OPERATORS = frozenset([PLUS, MINUS, TIMES, TOREAL])
CUSTOM_NODE_TYPES = []

THEORY_OPERATORS = LIRA_OPERATORS | BV_OPERATORS

def new_node_type(new_node_id=None):
    """Adds a new node type to the list of custom node types and returns the ID."""
    if new_node_id is None:
        if len(CUSTOM_NODE_TYPES) == 0:
            new_node_id = ALL_TYPES[-1] + 1
        else:
            new_node_id = CUSTOM_NODE_TYPES[-1] + 1

    assert new_node_id not in ALL_TYPES
    assert new_node_id not in CUSTOM_NODE_TYPES
    CUSTOM_NODE_TYPES.append(new_node_id)
    return new_node_id


def op_to_str(node_id):
    """Returns a string representation of the given node."""
    if node_id not in __OP_STR__:
        return str(node_id)
    return __OP_STR__[node_id]

def all_types():
    """Returns an iterator over all base and custom types."""
    return iter(ALL_TYPES + CUSTOM_NODE_TYPES)


__OP_STR__ = {
    FORALL : "FORALL",
    EXISTS : "EXISTS",
    AND : "AND",
    OR : "OR",
    NOT : "NOT",
    IMPLIES : "IMPLIES",
    IFF : "IFF",
    SYMBOL : "SYMBOL",
    FUNCTION : "FUNCTION",
    REAL_CONSTANT : "REAL_CONSTANT",
    BOOL_CONSTANT : "BOOL_CONSTANT",
    INT_CONSTANT : "INT_CONSTANT",
    PLUS : "PLUS",
    MINUS : "MINUS",
    TIMES : "TIMES",
    LE : "LE",
    LT : "LT",
    EQUALS : "EQUALS",
    ITE : "ITE",
    TOREAL : "TOREAL",
    BV_CONSTANT : "BV_CONSTANT",
    BV_NOT : "BV_NOT",
    BV_AND : "BV_AND",
    BV_OR : "BV_OR",
    BV_XOR : "BV_XOR",
    BV_CONCAT : "BV_CONCAT",
    BV_EXTRACT : "BV_EXTRACT",
    BV_ULT : "BV_ULT",
    BV_ULE : "BV_ULE",
    BV_NEG : "BV_NEG",
    BV_ADD : "BV_ADD",
    BV_MUL : "BV_MUL",
    BV_UDIV : "BV_UDIV",
    BV_UREM : "BV_UREM",
    BV_LSHL : "BV_LSHL",
    BV_LSHR : "BV_LSHR",
    BV_ROL : "BV_ROL",
    BV_ROR : "BV_ROR",
    BV_ZEXT : "BV_ZEXT",
    BV_SEXT : "BV_SEXT",
}
