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

ALL_TYPES = range(0,20)

(
FORALL, EXISTS, AND, OR, NOT, IMPLIES, IFF, # Boolean Logic (0-6)
SYMBOL, FUNCTION,                           # Symbols and functions calls (7-8)
REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT, # Constants (9-11)
PLUS, MINUS, TIMES,                         # LIA/LRA operators (12-14)
LE, LT, EQUALS,                             # LIA/LRA relations (15-17)
ITE,                                        # Term-ite (18)
TOREAL                                      # LIRA toreal() function (19)
) = ALL_TYPES

QUANTIFIERS = frozenset([FORALL, EXISTS])

BOOL_CONNECTIVES = frozenset([AND, OR, NOT, IMPLIES, IFF])

BOOL_OPERATORS = frozenset(QUANTIFIERS | BOOL_CONNECTIVES)

RELATIONS = frozenset([LE, LT, EQUALS])

CONSTANTS = frozenset([REAL_CONSTANT, BOOL_CONSTANT, INT_CONSTANT])

CUSTOM_NODE_TYPES = []

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
