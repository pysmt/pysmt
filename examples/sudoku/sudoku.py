#!/usr/bin/env python

import math
import argparse

from pysmt.shortcuts import Int, FreshSymbol, Solver, Equals
from pysmt.shortcuts import Or, get_env, BV, AllDifferent
from pysmt import typing
from pysmt.logics import QF_LIA, QF_BV


class Sudoku(object):
    """A sudoku problem representation and solving"""

    def __init__(self, size=3, solver_name=None, use_bv=None):
        self.size = size

        if use_bv is None:
            # If BV is unspecified, check to see if a BV solver is
            # available, otherwise default to INT
            all_bv_solvers = get_env().factory.all_solvers(QF_BV)
            use_bv = (len(all_bv_solvers) > 0)
        self.use_bv = use_bv

        # Logic selection
        logic = QF_LIA
        if use_bv:
            logic = QF_BV
            # Compute the minimum BV size needed for this problem
            self.bv_size = int(math.floor(math.log(self.size**2, 2))) + 1

        # Build a solver initialized with the proper assertions and
        # the matrix of SMT-variables representing each cell.
        self.solver, self.var_table = \
              self.get_prepared_solver(logic, solver_name)


    def get_type(self):
        """Returns the type of variables: either INT or BV depending on the
        use_bv flag of the constructor
        """
        if self.use_bv:
            return typing.BVType(self.bv_size)
        else:
            return typing.INT

    def const(self, value):
        """Create a constant with the given value of the correct type"""
        if self.use_bv:
            return BV(value, self.bv_size)
        else:
            return Int(value)

    def get_prepared_solver(self, logic, solver_name=None):
        """Returns a solver initialized with the sudoku constraints and a
        matrix of SMT variables, each representing a cell of the game.
        """
        sq_size = self.size**2
        ty = self.get_type()
        var_table = [[FreshSymbol(ty) for _ in xrange(sq_size)]
                          for _ in xrange(sq_size)]

        solver = Solver(logic=logic, name=solver_name)
        # Sudoku constraints
        # all variables are positive and lower or equal to than sq_size
        for row in var_table:
            for var in row:
                solver.add_assertion(Or([Equals(var, self.const(i))
                                         for i in xrange(1, sq_size + 1)]))

        # each row and each column contains all different numbers
        for i in xrange(sq_size):
            solver.add_assertion(AllDifferent(var_table[i]))
            solver.add_assertion(AllDifferent([x[i] for x in var_table]))

        # each square contains all different numbers
        for sx in xrange(self.size):
            for sy in xrange(self.size):
                square = [var_table[i + sx * self.size][j + sy * self.size]
                          for i in xrange(self.size) for j in xrange(self.size)]
                solver.add_assertion(AllDifferent(square))

        return solver, var_table

    def solve(self, constraints=None):
        """Solve a problem with the given constraints.

        constraints is a matrix of integer numbers, -1 indicates an
        empty cell.

        The function returns a completed matrix of integer numbers or
        None if the problem is unsolvable

        """
        self.solver.push()

        if constraints is not None:
            # User constraints
            for i, row in enumerate(constraints):
                for j, val in enumerate(row):
                    if val > 0:
                        self.solver.add_assertion(Equals(self.var_table[i][j],
                                                         self.const(val)))

        res = self.solver.solve()

        if res:
            result = []
            for r, lst in enumerate(self.var_table):
                r = []
                for var in lst:
                    val = self.solver.get_py_value(var)
                    r.append(val)
                result.append(r)
            self.solver.pop()
            return result
        else:
            self.solver.pop()
            return None



def read_constraints(fname):
    """reads the constraints from file
    (see problems/ folder for examples)
    """
    def reader(fname):
        with open(fname, "r") as f:
            for line in f:
                r = line.split()
                for x in r:
                    yield x

    r = reader(fname)
    size = int(next(r))
    constraints = []
    for _ in xrange(size**2):
        row = []
        for _ in xrange(size**2):
            w = next(r)
            if w != "X":
                row.append(int(w))
            else:
                row.append(-1)
        constraints.append(row)
    return constraints


def main():
    env = get_env()

    parser = argparse.ArgumentParser(description="Command-line interface " \
                                     "for solving sudoku problems")

    parser.add_argument('--size', '-n', metavar='number', type=int,
                        help='The sudoku base size', default=3)

    parser.add_argument('--solver', '-s', metavar='name', type=str,
                        choices=['auto'] + env.factory.all_solvers().keys(),
                        default='auto',
                        help='The solver to use (default: auto)')

    parser.add_argument('--bv', '-b', action="store_true",
                        help='Force the use of bit-vectors instead of integers')

    parser.add_argument('--lia', '-i', action="store_true",
                        help='Force use LIA instead of bit-vectors')

    parser.add_argument('--problem', '-p', metavar='filename', type=str,
                        help='The sudoku problem')

    args = parser.parse_args()

    solver = None if args.solver == "auto" else args.solver
    use_bv = True if args.bv else (False if args.lia else None)
    sudoku = Sudoku(size=args.size,
                    solver_name=solver,
                    use_bv=use_bv)

    constraints = None
    if args.problem:
        constraints = read_constraints(args.problem)
        res = sudoku.solve(constraints)
        if res is None:
            print "No solution exists"
        else:
            for row in res:
                print "\t".join(str(x) for x in row)
    else:
        print "No problem specified! Either use the gui.py script or pass" \
            " a problem with --problem flag. Example problems are available" \
            " in the problems/ folder."



if __name__ == "__main__":
    main()
