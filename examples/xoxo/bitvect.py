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

board = [[FreshSymbol(BVType(4)) for _ in xrange(3)]
            for _ in xrange(3)]

solver = Solver()

for row in board:
    for cell in row:
        solver.add_assertion(Or([Equals(cell, i.value)
             for i in Cell]))

test = 'tests/test1.txt'
test = 'tests/blank.txt'

logger.debug(solver.assertions)

# load board
with open(test) as fh:
    for row, line in enumerate(fh.readlines()):
        for col, cell in enumerate(line.strip().split(' ')):
            if cell == Cell.x.name:
                solver.add_assertion(Equals(board[row][col], Cell.x.value))
            elif cell == Cell.o.name:
                solver.add_assertion(Equals(board[row][col], Cell.o.value))
#            else:
#                solver.add_assertion(Equals(board[row][col], Cell.s.value))

logger.debug(solver.assertions)

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
                line += " "
            line += " "
        print(line)

def play_move(player, row, col):
    solver.add_assertion(Equals(board[row][col], player))

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
    #return board[0][0] + board[0][1] + board[0][2] + board[1][0] + board[1][1] + board[1][2] + board[2][0] + board[2][1] + board[2][2]
    return board[0][0].BVAdd(board[0][1]).BVAdd(board[0][2]).BVAdd(board[1][0]).BVAdd(board[1][1]).BVAdd(board[1][2]).BVAdd(board[2][0]).BVAdd(board[2][1]).BVAdd(board[2][2])

def sum_board():
    sum = 0
    for row in board:
        for cell in row:
            logger.debug("%s = %s" % (cell, solver.get_py_value(cell)))
            sum += solver.get_py_value(cell)
    return sum

def can_win_next_time(player):
    win_assert = Or(get_win_assertion(player))
    next_move = Or(get_next_move(player))
    solver.solve()
    print_board()
    print(sum_board())
    res = solver.solve([win_assert, Equals(get_sum_board(), BV(8 ,4))])
    if res:
        print_board()
        print(sum_board())

def convert_num_to_indices(num):
    row = int(num/3)
    col = num % 3
    return(row,col)

turns = 0
while True:
    print(solver.solve([Equals(get_sum_board(), BV(1,4))]))
    print(sum_board())
    # get user input and handle errors
    logger.info("-" * 40)
    logger.info("turn %d" % turns)
    print_board()
    try:
        next_cell = int(raw_input("type a cell (1-9):")) - 1
    except ValueError:
        continue
    if next_cell < 0 or next_cell > 8:
        continue

    # convert index to rows, cols, check if space is free
    row, col = convert_num_to_indices(next_cell)
    if(not already_played(row, col)):
        play_move(Cell.x, row, col)
    else:
        logger.info("that cell is already taken")
        continue

    turns += 1
"""
    # assertions for next move
    x_next_move_assertion = Equals(Int((turns+1)*Cell.x.value + (turns*Cell.o.value)), Plus(Plus(board[0]), Plus(board[1]), Plus(board[2])))
    x_this_move_assertion = Equals(Int((turns-1)*(Cell.x.value + Cell.o.value)+Cell.x.value), Plus(Plus(board[0]), Plus(board[1]), Plus(board[2])))
    this_move_assertion = Equals(Int((turns)*(Cell.x.value + Cell.o.value)), Plus(Plus(board[0]), Plus(board[1]), Plus(board[2])))
    o_win_this_turn_assertions = And(Or(o_win_assertions), this_move_assertion)
    x_win_next_turn_assertions = And(Or(x_win_assertions), x_next_move_assertion)
    x_win_this_turn_assertions = And(Or(x_win_assertions), x_this_move_assertion)

    # detect x has won
    logger.debug("checking if x has won")
    logger.debug(x_win_this_turn_assertions)
    if solver.solve([x_win_this_turn_assertions]):
        print_solver_board()
        print("x wins")
        exit()

    # can I win next turn?
    logger.debug("look for o to win")
    logger.debug(o_win_this_turn_assertions)
    if solver.solve([o_win_this_turn_assertions]):
        logger.debug("o can win like this")
        print_solver_board()
        result = get_a_move(Cell.o)
        if result is not None:
            play_move(Cell.o, result[0], result[1])
            print_board()
            print("o wins")
            exit()

    logger.debug("look for x to win next turn")
    logger.debug(x_win_next_turn_assertions)
    if solver.solve([x_win_next_turn_assertions]):
        # can x win next turn? if so stop
        logger.debug("x can win like this")
        print_solver_board()
        result = get_a_move(Cell.x)
        if result is not None:
            play_move(Cell.o, result[0], result[1])
            continue

    # otherwise try and win
    logger.debug("looking for a win")
    played = False
    for future_turn in range(turns, 5):
        move_assertion = Equals(Int((future_turn)*(Cell.x.value + Cell.o.value)), Plus(Plus(board[0]), Plus(board[1]), Plus(board[2])))
        for assertion in o_win_assertions:
            logger.debug("trying %s turn %d" % (assertion, future_turn))
            res = solver.solve([assertion, move_assertion])
            if res:
                logger.debug("found a win on turn %d" % future_turn)
                print_solver_board()
                row, col = get_a_move(Cell.o)
                play_move(Cell.o, row, col)
                played = True
                break

        if played:
            break

    if not played:
        exit("I give up")
"""
