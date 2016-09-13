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
from pysmt.smtlib.parser import open_
from pysmt.shortcuts import FreshSymbol, Or, And, Not


def read_dimacs(fname):
    """Read a DIMACS CNF file from the given file.

    Returns a tuple: (vars_cnt, clauses, comments)
    """
    prob_type, vars_cnt, clauses_cnt = None, None, None
    max_var = 0
    comments = []
    clauses = []

    with open_(fname) as fin:
        for line in fin:
            if line[0] == "c":
                comments.append(line)
            elif line[0] == "p":
                _, prob_type, vars_cnt, clauses_cnt = line.split(" ")
                prob_type = prob_type.strip()
                if prob_type != "cnf":
                    raise IOError("File does not contain a cnf.")
                vars_cnt = int(vars_cnt.strip())
                clauses_cnt = int(clauses_cnt)
                break

        for line in fin:
            if line[0] == "c":
                comments.append(line)
            else:
                # TODO: More robust parsing of clauses
                cl = line.strip().split(" ")
                assert cl[-1].strip() == "0", cl
                clause = [int(lit) for lit in cl[:-1]]
                max_var = max(max_var, max(abs(lit) for lit in clause))
                assert not any(lit == 0 for lit in clause), clause
                clauses.append(clause)

    # Validation
    if clauses_cnt != len(clauses):
        raise IOError("Mismatch between declared clauses (%d) " % clauses_cnt +
                      "and actual clauses (%d) in DIMACS file." % len(clauses))
    if max_var > vars_cnt:
        raise IOError("Mismatch between declared variables (%d) " % vars_cnt +
                      "and actual variables (%d) in DIMACS file." % max_var)

    return vars_cnt, clauses, comments


def dimacs_to_pysmt(vars_cnt, clauses, comments):
    """Convert a DIMACS structure into a pySMT formula.

    Returns (formula, symbol_table). The symbol_table contains a
    mapping from pySMT symbol to DIMACS var_idx.

    """
    st = {}
    rev_st = {}
    for i in xrange(1, vars_cnt+1):
        s = FreshSymbol(template=("_dimacs_%d"%i+"_%d"))
        st[i] = s
        st[-i] = Not(s)
        rev_st[s] = i
    res = And(Or(st[lit] for lit in clause) \
              for clause in clauses)
    return res, rev_st


if __name__ == "__main__":
    import sys

    dimacs = read_dimacs(sys.argv[1])
    f, st = dimacs_to_pysmt(*dimacs)
    print(f.size())
    print(dimacs[0], dimacs[1], "".join(dimacs[2]))
