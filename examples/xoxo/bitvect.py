from pysmt.shortcuts import FreshSymbol, BV, Or, And, Equals, Plus, Solver, Int
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
    s = BV(0,4) # space
    x = BV(1,4) # x
    o = BV(2,4) # o

board = [[FreshSymbol(BVType(4)) for _ in range(3)]
            for _ in range(3)]

solver = Solver()

for row in board:
    for cell in row:
        solver.add_assertion(Or([Equals(cell, i.value)
             for i in Cell]))

test = 'tests/test1.txt'
test = 'tests/blank.txt'

# load board
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

def play_move(player, row, col):
    logger.debug("adding assertion player %s at (%d, %d)" % (player,row,col))
    solver.add_assertion(And(Equals(board[row][col], player)))

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

def get_next_move(player):
    return [
            Equals(board[0][0], player),
            Equals(board[0][1], player),
            Equals(board[0][2], player),
            Equals(board[1][0], player),
            Equals(board[1][1], player),
            Equals(board[1][2], player),
            Equals(board[2][0], player),
            Equals(board[2][1], player),
            Equals(board[2][2], player),
           ]


def get_sum_board():
    return board[0][0] + board[0][1] + board[0][2] +  \
            board[1][0] + board[1][1] + board[1][2] + \
            board[2][0] + board[2][1] + board[2][2]

def can_win(player, board_val):
    win_assert = Or(get_win_assertion(player))
    logger.debug("testing for player %s to win with board_val %d" % (player, board_val))
    res = solver.solve([win_assert, Equals(get_sum_board(), BV(board_val, 4))])
    logger.debug(solver.assertions)
    if res:
        logger.debug("found a win")
        return True
    logger.debug("no place to win")
    return False

def convert_num_to_indices(num):
    row = int(num/3)
    col = num % 3
    return(row,col)

def get_new_move(player):
    logger.debug("looking for a move for %s" % player)
    #import ipdb; ipdb.set_trace()
    for r, row in enumerate(board):
        for c, cell in enumerate(row):
            if not Equals(board[r][c], player) in solver.assertions: # if not already played
                if solver.get_value(cell) == player: # and is marked as a move
                    return(r,c)

human_turns = 0
cpu_turns = 0
while True:
    solver.solve([Equals(get_sum_board(), BV(human_turns * 1 + cpu_turns * 2,4))])

    # get user input and handle errors
    logger.info("-" * 40)
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
        play_move(Cell.x.value, row, col)
        human_turns += 1
    else:
        logger.info("that cell is already taken")
        continue

    if can_win(Cell.x.value, human_turns * 1 + cpu_turns * 2):
        print("x wins")
        print_board()
        exit(0)

    cpu_turns += 1

    # see if cpu can win this turn
    if can_win(Cell.o.value, human_turns * 1 + cpu_turns * 2):
        result = get_new_move(Cell.o.value)
        play_move(Cell.o.value, result[0], result[1])
        print("o wins")
        print_board()
        exit(0)
    # try to block x
    elif solver.solve([Or(get_win_assertion(Cell.x.value)), Or(get_next_move(Cell.o.value)), Equals(get_sum_board(), BV((human_turns+1) * 1 + (cpu_turns) * 2,4))]):
        print("found a way to block x winning next time with board val %d" % ((human_turns+1) * 1 + (cpu_turns) * 2))
        print_board()
        result = get_new_move(Cell.x.value)
        play_move(Cell.o.value, result[0], result[1])
    # force solver to find a next move for o, rather than 2 moves for x by specifying possible next moves with get_next_move()
    elif solver.solve([Or(get_next_move(Cell.o.value)), Equals(get_sum_board(), BV(human_turns * 1 + cpu_turns * 2,4))]):
        result = get_new_move(Cell.o.value)
        play_move(Cell.o.value, result[0], result[1])
    else:
        print("o can't play")
        exit(0)

