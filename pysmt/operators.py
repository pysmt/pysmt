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


ALL_TYPES = list(xrange(0,63))

(
FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF, # Boolean Logic (0-6)
SYMBOL, FUNCTION,                           # Symbols and functions calls (7-8)
REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT,STRING_CONSTANT, # Constants (9-12)
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
#STRINGS
STR_LENGTH,                                 #length(48)
STR_CONCAT,                                 #concat(49)
STR_CONTAINS,                               #contains(50)
STR_INDEXOF,                                #indexOf(51)
STR_REPLACE,                                #replace (52)
STR_SUBSTR,                                 #Sub String (53)
STR_PREFIXOF,                               # prefix (54)
STR_SUFFIXOF,                               # suffix (55)
STRING_TO_INTEGER,                          # atoi (56)
INTEGER_TO_STRING,                          # itoa (57)
STRING_TO_UINT16,                           # atoi - 16bit (58) 
UINT16_TO_STRING,                           # itoa - 16 bit (59)
STRING_TO_UINT32,                           # atoi - 32 bit unsigned (60)
UINT32_TO_STRING,                           # itoa - 32 bit unsigned  (61)     
STR_CHARAT,                                 # Char at an index (62)
) = ALL_TYPES

QUANTIFIERS = frozenset([FORALL, EXISTS])

BOOL_CONNECTIVES = frozenset([AND, OR, NOT, IMPLIES, IFF])

BOOL_OPERATORS = frozenset(QUANTIFIERS | BOOL_CONNECTIVES)

RELATIONS = frozenset([LE, LT, EQUALS, BV_ULE, BV_ULT, BV_SLT, BV_SLE])

CONSTANTS = frozenset([REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT,
                       BV_CONSTANT, STRING_CONSTANT])

BV_OPERATORS = frozenset([BV_CONSTANT, BV_NOT, BV_AND, BV_OR, BV_XOR,
                          BV_CONCAT, BV_EXTRACT, BV_ULT, BV_ULE, BV_NEG, BV_ADD,
                          BV_SUB, BV_MUL, BV_UDIV, BV_UREM, BV_LSHL, BV_LSHR,
                          BV_ROL, BV_ROR, BV_ZEXT, BV_SEXT, BV_SLT, BV_SLE,
                          BV_COMP, BV_SDIV, BV_SREM, BV_ASHR])

STRING_OPERATORS = frozenset([  STRING_CONSTANT, STR_LENGTH, STR_CONCAT, STR_CONTAINS, STR_INDEXOF, STR_REPLACE,
                                STR_SUBSTR, STR_PREFIXOF, STR_SUFFIXOF, STRING_TO_INTEGER, INTEGER_TO_STRING,
                                STRING_TO_UINT16, UINT16_TO_STRING, STRING_TO_UINT32, UINT32_TO_STRING, STR_CHARAT ])

LIRA_OPERATORS = frozenset([PLUS, MINUS, TIMES, TOREAL])
CUSTOM_NODE_TYPES = []

THEORY_OPERATORS = LIRA_OPERATORS | BV_OPERATORS | STRING_OPERATORS

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
    STRING_CONSTANT : "STRING_CONSTANT",
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
    STRING_TO_INTEGER:"STRING_TO_INTEGER",
    INTEGER_TO_STRING:"INTEGER_TO_STRING",
    STRING_TO_UINT16:"STRING_TO_UINT16",
    UINT16_TO_STRING:"UINT16_TO_STRING",
    STRING_TO_UINT32:"STRING_TO_UINT32",
    UINT32_TO_STRING:"UINT32_TO_STRING",
    STR_CHARAT:"STR_CHARAT"
}
