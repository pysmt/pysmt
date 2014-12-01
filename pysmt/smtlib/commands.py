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
"""Defines constants for the commands of the SMT-LIB"""

SET_INFO='set-info'
RESET_ASSERTIONS='reset-assertions'
GET_VALUE='get-value'
SET_OPTION='set-option'
ASSERT='assert'
CHECK_SAT='check-sat'
EXIT='exit'
SET_LOGIC='set-logic'
DECLARE_FUN='declare-fun'
DECLARE_CONST='declare-const'
DEFINE_FUN='define-fun'
PUSH='push'
POP='pop'


ALL_COMMANDS = [
    SET_INFO,
    RESET_ASSERTIONS,
    GET_VALUE,
    SET_OPTION,
    ASSERT,
    CHECK_SAT,
    EXIT,
    SET_LOGIC,
    DECLARE_FUN,
    DECLARE_CONST,
    DEFINE_FUN,
    PUSH,
    POP,
]
