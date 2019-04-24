from pysmt.shortcuts import FreshSymbol, BV, Or, And, Equals, Plus, Solver, Int
from pysmt.typing import BVType
from enum import Enum
import logging

VECT_WIDTH = 5

class Cell(Enum):
    s = BV(0,VECT_WIDTH) # space
    x = BV(1,VECT_WIDTH) # x - human player goes first
    o = BV(2,VECT_WIDTH) # o - cpu player

x_turns = 0
o_turns = 0
x_val = Cell.x.value.constant_value()
o_val = Cell.o.value.constant_value()

board = [[FreshSymbol(BVType(VECT_WIDTH)) for _ in range(3)]
            for _ in range(3)]

solver = Solver()

# initialise board cells, each one has to be blank, x or o
for row in board:
    for cell in row:
        solver.add_assertion(Or([Equals(cell, i.value)
             for i in Cell]))

# load board
test = 'tests/blank.txt'
with open(test) as fh:
    for row, line in enumerate(fh.readlines()):
        for col, cell in enumerate(line.strip().split(' ')):
            if cell == Cell.x.name:
                solver.add_assertion(Equals(board[row][col], Cell.x.value))
            elif cell == Cell.o.name:
                solver.add_assertion(Equals(board[row][col], Cell.o.value))

def already_played(row, col):
    if solver.get_value(board[row][col]) == Cell.s.value:
        return False
    return True

def print_board():
    for row in board:
        line = ""
        for cell in row:
            if solver.get_value(cell) == Cell.x.value:
                line += "x"
            elif solver.get_value(cell) == Cell.o.value:
                line += "o"
            else:
                line += "-"
            line += " "
        print(line)

def play_move(p, row, col):
    logger.debug("adding assertion for player %s at (%d, %d)" % (p.name, row, col))
    solver.add_assertion(And(Equals(board[row][col], p.value)))

def get_win_formula(p):
    return [
           # rows
           And(Equals(board[0][0], p.value), Equals(board[0][1], p.value), Equals(board[0][2], p.value)),
           And(Equals(board[1][0], p.value), Equals(board[1][1], p.value), Equals(board[1][2], p.value)),
           And(Equals(board[2][0], p.value), Equals(board[2][1], p.value), Equals(board[2][2], p.value)),

           # cols
           And(Equals(board[0][0], p.value), Equals(board[1][0], p.value), Equals(board[2][0], p.value)),
           And(Equals(board[0][1], p.value), Equals(board[1][1], p.value), Equals(board[2][1], p.value)),
           And(Equals(board[0][2], p.value), Equals(board[1][2], p.value), Equals(board[2][2], p.value)),

           # diags
           And(Equals(board[0][0], p.value), Equals(board[1][1], p.value), Equals(board[2][2], p.value)),
           And(Equals(board[2][0], p.value), Equals(board[1][1], p.value), Equals(board[0][2], p.value)),
           ]

# only return options not already played
def find_all_moves(p):
    logger.debug("finding all possible moves for %s" % p.name)
    options = []
    for r, row in enumerate(board):
        for c, cell in enumerate(row):
            if not Equals(board[r][c], p.value) in solver.assertions: # if not already played
                options.append(Equals(cell, p.value))
                logger.debug("%d,%d" % (r,c))
    return options

def pick_new_move(p):
    logger.debug("picking a move for %s" % p.name)
    for r, row in enumerate(board):
        for c, cell in enumerate(row):
            if not Equals(board[r][c], p.value) in solver.assertions: # if not already played
                if solver.get_value(cell) == p.value: # and is in the solution
                    return(r,c)

# used to determine how many counters can be on the board given the current turn
def get_board_sum():
    return board[0][0] + board[0][1] + board[0][2] + board[1][0] + board[1][1] + board[1][2] + \
            board[2][0] + board[2][1] + board[2][2]

def convert_num_to_indices(num):
    row = int(num/3)
    col = num % 3
    return(row,col)

while True:
    # get user input and handle errors
    logger.info("-" * 40)
    solver.solve([Equals(get_board_sum(), BV(x_turns * x_val + o_turns * o_val, VECT_WIDTH))])
    print_board()
    try:
        next_cell = int(input("type a cell (1-9):")) - 1
    except ValueError:
        continue
    if next_cell < 0 or next_cell > 8:
        continue

    # convert index to rows, cols, check if space is free
    row, col = convert_num_to_indices(next_cell)
    if(not already_played(row, col)):
        play_move(Cell.x, row, col)
        x_turns += 1
    else:
        logger.info("that cell is already taken")
        continue

    # check for x to win
    if solver.solve([
                        Or(get_win_formula(Cell.x)),
                        Equals(get_board_sum(), BV(x_turns * x_val + o_turns * o_val, VECT_WIDTH))]):
        print("x wins")
        print_board()
        exit(0)
    elif x_turns == 5:
        print("no win possible")
        exit(0)

    # o's turn played by cpu
    o_turns += 1

    # see if o can win this turn
    if solver.solve([
                        Or(get_win_formula(Cell.o)),
                        Equals(get_board_sum(), BV(x_turns * x_val + o_turns * o_val, VECT_WIDTH))]):
        logger.debug("found a way for o to win")
        result = pick_new_move(Cell.o)
        play_move(Cell.o, result[0], result[1])
        print("o wins")
        print_board()
        exit(0)

    # try to block x next turn (x_turns+1) after both players have played again
    elif solver.solve([
                        Or(get_win_formula(Cell.x)),
                        And(Or(find_all_moves(Cell.o)), Or(find_all_moves(Cell.x))),
                        Equals(get_board_sum(), BV((x_turns+1) * x_val + o_turns * o_val, VECT_WIDTH))]):
        logger.debug("found a way to block x winning next time with board val %d" % ((x_turns+1) * x_val + o_turns * o_val))
        print_board()
        result = pick_new_move(Cell.x) # get the winning move for x and play for o
        play_move(Cell.o, result[0], result[1])

    # force solver to find a next move for o, rather than 2 moves for x by specifying possible next moves with find_all_moves()
    elif solver.solve([
                        Or(find_all_moves(Cell.o)),
                        Equals(get_board_sum(), BV(x_turns * x_val + o_turns * o_val, VECT_WIDTH))]):
        result = pick_new_move(Cell.o)
        play_move(Cell.o, result[0], result[1])
    
    # o can't play
    else:
        print("o can't play")
        exit(0)
