from pysmt.shortcuts import FreshSymbol, BV, Or, And, Equals, Plus, Solver
from pysmt.typing import BVType
from enum import Enum
import logging

logger = logging.getLogger('xoxo')
logger.setLevel(logging.DEBUG)
ch = logging.StreamHandler()

if __debug__: # start with -O
    log_level = logging.DEBUG
else:
    log_level = logging.INFO

ch.setLevel(log_level)

logger.addHandler(ch)

class Cell(Enum):
    s = BV(0,2) # space
    x = BV(1,2) # x
    o = BV(2,2) # o

board = [[FreshSymbol(BVType(2)) for _ in xrange(3)]
            for _ in xrange(3)]

solver = Solver()

for row in board:
    for cell in row:
        solver.add_assertion(Or([Equals(cell, i.value)
             for i in Cell]))

test = 'tests/test1.txt'

logger.debug(solver.assertions)

# load board
with open(test) as fh:
    for row, line in enumerate(fh.readlines()):
        for col, cell in enumerate(line.strip().split(' ')):
            if cell == Cell.x.name:
                solver.add_assertion(Equals(board[row][col], Cell.x.value))
            elif cell == Cell.o.name:
                solver.add_assertion(Equals(board[row][col], Cell.o.value))
            else:
                solver.add_assertion(Equals(board[row][col], Cell.s.value))

logger.debug(solver.assertions)

def print_board():
    for row in board:
        line = ""
        for cell in row:
            if solver.get_value(cell) == Cell.x.value:
                line += "x"
            elif solver.get_value(cell) == Cell.o.value:
                line += "o"
            else:
                line += " "
            line += " "
        print(line)

def get_win_assertion(player):
    return [
           # rows
           And(Equals(board[0][0], player), Equals(board[0][1], player), Equals(board[0][2], player)),
           And(Equals(board[1][0], player), Equals(board[1][1], player), Equals(board[1][2], player)),
           And(Equals(board[2][0], player), Equals(board[2][1], player), Equals(board[2][2], player)),

           # cols
           And(Equals(board[0][0], player), Equals(board[1][0], player), Equals(board[2][0], player)),
           And(Equals(board[0][1], player), Equals(board[1][1], player), Equals(board[2][1], player)),
           And(Equals(board[0][2], player), Equals(board[1][2], player), Equals(board[2][2], player)),

           # diags
           And(Equals(board[0][0], player), Equals(board[1][1], player), Equals(board[2][2], player)),
           And(Equals(board[2][0], player), Equals(board[1][1], player), Equals(board[0][2], player)),
           ]

def sum_board():
    import ipdb; ipdb.set_trace()

print(solver.solve([Or(get_win_assertion(Cell.x.value))]))
print(solver.solve([Or(get_win_assertion(Cell.o.value))]))

solver.solve() # need to run this before print_board is called
print_board()
sum_board()
