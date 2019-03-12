from pysmt.shortcuts import FreshSymbol, Symbol, String, LE, GE, Int, Not, Or, And, Equals, Plus, Solver, StrContains
from pysmt.typing import INT, STRING
from enum import Enum
import logging
logger = logging.getLogger('xoxo')
logger.setLevel(logging.DEBUG)
ch = logging.StreamHandler()
ch.setLevel(logging.INFO) # change to DEBUG for info on assertions
logger.addHandler(ch)

class Cell(Enum):
    x = 1
    o = 10
    s = 0

DEBUG = False
turns = 0
sq_size = 3
test = 'tests/test1.txt'
test = 'tests/blank.txt'

# create symbols for the board
board = [[FreshSymbol(INT) for _ in xrange(sq_size)]
    for _ in xrange(sq_size)]

solver = Solver(name="z3")

# setup assertions for board
for row in board:
    for cell in row:
        solver.add_assertion(Or([Equals(cell, Int(i.value))
             for i in Cell]))

display_board = [[Cell.s for _ in xrange(sq_size)] for _ in xrange(sq_size)]

# load board
with open(test) as fh:
    for row, line in enumerate(fh.readlines()):
        for col, cell in enumerate(line.strip().split(' ')):
            if cell == Cell.x.name:
                solver.add_assertion(Equals(board[row][col], Int(Cell.x.value)))
                display_board[row][col] = Cell.x
                turns += 1
            elif cell == Cell.o.name:
                solver.add_assertion(Equals(board[row][col], Int(Cell.o.value)))
                display_board[row][col] = Cell.o

def get_win_assertion(player):
    return [
        # rows
        Equals(Plus(board[0]), Int(player * sq_size)), 
        Equals(Plus(board[1]), Int(player * sq_size)), 
        Equals(Plus(board[2]), Int(player * sq_size)),
        # cols
        Equals(Plus([row[0] for row in board]), Int(player * sq_size)),
        Equals(Plus([row[1] for row in board]), Int(player * sq_size)),
        Equals(Plus([row[2] for row in board]), Int(player * sq_size)),
        # diags
        Equals(Plus([board[0][0], board[1][1], board[2][2]]), Int(player * sq_size)),
        Equals(Plus([board[0][2], board[1][1], board[2][0]]), Int(player * sq_size))
        ]

# assertions for players to win
o_win_assertions = get_win_assertion(Cell.o.value)
x_win_assertions = get_win_assertion(Cell.x.value)

logger.debug(solver.assertions)

def print_board():
    for row in display_board:
        logger.info(" ".join([cell.name.replace('s','.') for cell in row]))

def print_solver_board():
    logger.debug("solver board")
    for row in board:
        logger.debug(" ".join([Cell(int(solver.get_py_value(cell))).name.replace('s','.') for cell in row]))

def get_a_move(player):
    logger.debug("looking for a move for %s" % player)
    # prioritise center position
    if display_board[1][1] == Cell.s and Cell(int(solver.get_py_value(board[1][1]))) == player:
        return(1,1)
    for r, row in enumerate(board):
        for c, cell in enumerate(row):
            if display_board[r][c] == Cell.s and Cell(int(solver.get_py_value(cell))) == player:
                return(r,c)

def convert_num_to_indices(num):
    row = int(num/sq_size)
    col = num % sq_size
    return(row,col)

def already_played(row, col):
    if display_board[row][col] == Cell.s:
        return False
    return True

def play_move(player, row, col):
    display_board[row][col] = player
    solver.add_assertion(Equals(board[row][col], Int(player.value)))

while True:

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
        exit("x wins")

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
            exit("o wins")

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
