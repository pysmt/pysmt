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
from itertools import chain


ALL_TYPES = list(range(0,66))

(
FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF, # Boolean Logic (0-6)
SYMBOL, FUNCTION,                           # Symbols and functions calls (7-8)
REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT, STR_CONSTANT, # Constants (9-12)
PLUS, MINUS, TIMES,                         # LIA/LRA operators (13-15)
LE, LT, EQUALS,                             # LIA/LRA relations (16-18)
ITE,                                        # Term-ite (19)
TOREAL,                                     # LIRA toreal() function (20)
#
# MG: FLOOR? INT_MOD_CONGR?
#
# BV
BV_CONSTANT,                                # Bit-Vector constant (21)
BV_NOT, BV_AND, BV_OR, BV_XOR,              # Logical Operators on Bit (22-25)
BV_CONCAT,                                  # BV Concatenation (26)
BV_EXTRACT,                                 # BV sub-vector extraction (27)
BV_ULT, BV_ULE,                             # Unsigned Comparison (28-29)
BV_NEG, BV_ADD, BV_SUB,                     # Basic arithmetic (30-32)
BV_MUL, BV_UDIV, BV_UREM,                   # Division/Multiplication (33-35)
BV_LSHL, BV_LSHR,                           # Shifts (36-37)
BV_ROL, BV_ROR,                             # Rotation (38-39)
BV_ZEXT, BV_SEXT,                           # Extension (40-41)
BV_SLT, BV_SLE,                             # Signed Comparison (42-43)
BV_COMP,                                    # Returns 1_1 if the arguments are
                                            # equal otherwise it returns 0_1 (44)
BV_SDIV, BV_SREM,                           # Signed Division and Reminder(45-46)
BV_ASHR,                                    # Arithmetic shift right (47)
#
# STRINGS
#
STR_LENGTH,                                 # Length (48)
STR_CONCAT,                                 # Concat (49)
STR_CONTAINS,                               # Contains (50)
STR_INDEXOF,                                # IndexOf (51)
STR_REPLACE,                                # Replace (52)
STR_SUBSTR,                                 # Sub String (53)
STR_PREFIXOF,                               # Prefix (54)
STR_SUFFIXOF,                               # Suffix (55)
STR_TO_INT,                                 # atoi (56)
INT_TO_STR,                                 # itoa (57)
STR_CHARAT,                                 # Char at an index (58)
#
# ARRAYS
#
ARRAY_SELECT,                               # Array Select (59)
ARRAY_STORE,                                # Array Store (60)
ARRAY_VALUE,                                # Array Value (61)

DIV,                                        # Arithmetic Division (62)
POW,                                        # Arithmetic Power (63)
ALGEBRAIC_CONSTANT,                         # Algebraic Number (64)
BV_TONATURAL,                               # BV to Natural Conversion (65)
) = ALL_TYPES

QUANTIFIERS = frozenset([FORALL, EXISTS])

BOOL_CONNECTIVES = frozenset([AND, OR, NOT, IMPLIES, IFF])

BOOL_OPERATORS = frozenset(QUANTIFIERS | BOOL_CONNECTIVES)

CONSTANTS = frozenset([BOOL_CONSTANT, REAL_CONSTANT, INT_CONSTANT,
                       BV_CONSTANT, STR_CONSTANT, ALGEBRAIC_CONSTANT])

# Relations are predicates on theory atoms.
# Relations have boolean type. They are a subset of the operators for a theory
BV_RELATIONS = frozenset([BV_ULE, BV_ULT, BV_SLT, BV_SLE])

IRA_RELATIONS = frozenset([LE, LT])

STR_RELATIONS = frozenset([STR_CONTAINS, STR_PREFIXOF, STR_SUFFIXOF])

RELATIONS = frozenset((EQUALS,)) | BV_RELATIONS | IRA_RELATIONS | STR_RELATIONS

# Operators are functions that return a Theory object
BV_OPERATORS = frozenset([BV_NOT, BV_AND, BV_OR, BV_XOR,
                          BV_CONCAT, BV_EXTRACT, BV_NEG, BV_ADD,
                          BV_SUB, BV_MUL, BV_UDIV, BV_UREM, BV_LSHL, BV_LSHR,
                          BV_ROL, BV_ROR, BV_ZEXT, BV_SEXT,
                          BV_COMP, BV_SDIV, BV_SREM, BV_ASHR])

STR_OPERATORS = frozenset([STR_LENGTH, STR_CONCAT, STR_INDEXOF, STR_REPLACE,
                           STR_SUBSTR, STR_CHARAT, STR_TO_INT, INT_TO_STR,])

IRA_OPERATORS = frozenset([PLUS, MINUS, TIMES, TOREAL, DIV, POW, BV_TONATURAL])

ARRAY_OPERATORS = frozenset([ARRAY_SELECT, ARRAY_STORE, ARRAY_VALUE])

THEORY_OPERATORS = IRA_OPERATORS | BV_OPERATORS | ARRAY_OPERATORS | STR_OPERATORS

CUSTOM_NODE_TYPES = []

assert (BOOL_OPERATORS | THEORY_OPERATORS | RELATIONS | \
        CONSTANTS | frozenset((SYMBOL, FUNCTION, ITE))) == frozenset(ALL_TYPES)

assert len(BOOL_OPERATORS & THEORY_OPERATORS) == 0
assert len(BOOL_OPERATORS & RELATIONS) == 0
assert len(BOOL_OPERATORS & CONSTANTS) == 0
assert len(THEORY_OPERATORS & RELATIONS) == 0
assert len(THEORY_OPERATORS & CONSTANTS) == 0
assert len(RELATIONS & CONSTANTS) == 0


def new_node_type(node_id=None, node_str=None):
    """Adds a new node type to the list of custom node types and returns the ID."""
    if node_id is None:
        if len(CUSTOM_NODE_TYPES) == 0:
            node_id = ALL_TYPES[-1] + 1
        else:
            node_id = CUSTOM_NODE_TYPES[-1] + 1

    assert node_id not in ALL_TYPES
    assert node_id not in CUSTOM_NODE_TYPES
    CUSTOM_NODE_TYPES.append(node_id)
    if node_str is None:
        node_str = "Node_%d" % node_id
    __OP_STR__[node_id] = node_str
    return node_id


def op_to_str(node_id):
    """Returns a string representation of the given node."""
    return __OP_STR__[node_id]


def all_types():
    """Returns an iterator over all base and custom types."""
    return chain(iter(ALL_TYPES), iter(CUSTOM_NODE_TYPES))


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
    STR_CONSTANT : "STR_CONSTANT",
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
    BV_SUB : "BV_SUB",
    BV_MUL : "BV_MUL",
    BV_UDIV : "BV_UDIV",
    BV_UREM : "BV_UREM",
    BV_LSHL : "BV_LSHL",
    BV_LSHR : "BV_LSHR",
    BV_ROL : "BV_ROL",
    BV_ROR : "BV_ROR",
    BV_ZEXT : "BV_ZEXT",
    BV_SEXT : "BV_SEXT",
    BV_SLT : "BV_SLT",
    BV_SLE : "BV_SLE",
    BV_COMP : "BV_COMP",
    BV_SDIV : "BV_SDIV",
    BV_SREM : "BV_SREM",
    BV_ASHR : "BV_ASHR",
    STR_LENGTH: "STR_LENGTH",
    STR_CONCAT: "STR_CONCAT",
    STR_CONTAINS: "STR_CONTAINS",
    STR_INDEXOF: "STR_INDEXOF",
    STR_REPLACE:"STR_REPLACE",
    STR_SUBSTR: "STR_SUBSTR",
    STR_PREFIXOF: "STR_PREFIXOF",
    STR_SUFFIXOF: "STR_SUFFIXOF",
    STR_TO_INT: "STR_TO_INT",
    INT_TO_STR: "INT_TO_STR",
    STR_CHARAT: "STR_CHARAT",
    BV_TONATURAL : "BV_TONATURAL",
    ARRAY_SELECT : "ARRAY_SELECT",
    ARRAY_STORE : "ARRAY_STORE",
    ARRAY_VALUE : "ARRAY_VALUE",
    DIV: "DIV",
    POW: "POW",
    ALGEBRAIC_CONSTANT: "ALGEBRAIC_CONSTANT",
}
