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


def conjunctive_partition(formula):
    """ Returns a generator over the top-level conjuncts of the given formula

    The result is such that for every formula phi, the following holds:
    phi <-> And(conjunctive_partition(phi))
    """
    to_process = [formula]
    seen = set()
    while to_process:
        cur = to_process.pop()
        if cur not in seen:
            seen.add(cur)
            if cur.is_and():
                to_process += cur.args()
            else:
                yield cur

def disjunctive_partition(formula):
    """ Returns a generator over the top-level disjuncts of the given formula

    The result is such that for every formula phi, the following holds:
    phi <-> Or(conjunctive_partition(phi))
    """
    to_process = [formula]
    seen = set()
    while to_process:
        cur = to_process.pop()
        if cur not in seen:
            seen.add(cur)
            if cur.is_or():
                to_process += cur.args()
            else:
                yield cur
