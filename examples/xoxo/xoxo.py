from pysmt.shortcuts import FreshSymbol, BV, Or, And, Equals, Solver
from pysmt.typing import BVType
from pysmt.logics import QF_BV
from enum import Enum
import os
import logging
from argparse import ArgumentParser

VECT_WIDTH = 5

class Cell(Enum):
    s = BV(0,VECT_WIDTH) # space
    x = BV(1,VECT_WIDTH) # x - human player goes first
    o = BV(2,VECT_WIDTH) # o - cpu player

logger = logging.getLogger('xoxo')

x_turns = 0
o_turns = 0
x_val = Cell.x.value.constant_value()
o_val = Cell.o.value.constant_value()

board = [[FreshSymbol(BVType(VECT_WIDTH)) for _ in range(3)]
            for _ in range(3)]

# python-side copy of the position: (row, col) -> Cell. The solver knows it too,
# but only IncrementalTrackingSolver exposes .assertions, so we keep our own
played = {}

# the example only needs bitvectors: asking for the logic lets pySMT pick any
# solver that supports it, instead of falling back on its default logic
solver = Solver(logic=QF_BV)

# initialise board cells, each one has to be blank, x or o
for row in board:
    for cell in row:
        solver.add_assertion(Or([Equals(cell, i.value)
             for i in Cell]))

def load_board(path):
    """Assert the counters already on the board, return how many each side played."""
    x_played = o_played = 0
    with open(path) as fh:
        for row, line in enumerate(fh.readlines()):
            for col, cell in enumerate(line.strip().split(' ')):
                if cell == Cell.x.name:
                    play_move(Cell.x, row, col)
                    x_played += 1
                elif cell == Cell.o.name:
                    play_move(Cell.o, row, col)
                    o_played += 1
    return x_played, o_played

def turns_played_formula(extra_x=0):
    """The board adds up to exactly the counters played, so the free cells are blank."""
    return Equals(get_board_sum(),
                  BV((x_turns + extra_x) * x_val + o_turns * o_val, VECT_WIDTH))

def already_played(row, col):
    return (row, col) in played

def print_board():
    # get_value() reads the last model, and adding an assertion invalidates it,
    # so solve for the board as it actually stands before printing it
    if not solver.solve([turns_played_formula()]):
        raise RuntimeError("the board is in an inconsistent state")
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
        logger.info(line)

def play_move(p, row, col):
    logger.debug("adding assertion for player %s at (%d, %d)" % (p.name, row, col))
    solver.add_assertion(Equals(board[row][col], p.value))
    played[(row, col)] = p

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

def free_cells():
    return [(r, c) for r in range(3) for c in range(3) if (r, c) not in played]

# only return options not already played
def find_all_moves(p):
    logger.debug("finding all possible moves for %s" % p.name)
    return [Equals(board[r][c], p.value) for r, c in free_cells()]

def pick_new_move(p):
    logger.debug("picking a move for %s" % p.name)
    for r, c in free_cells():
        if solver.get_value(board[r][c]) == p.value: # is in the solution
            return(r,c)

# used to determine how many counters can be on the board given the current turn
def get_board_sum():
    return board[0][0] + board[0][1] + board[0][2] + board[1][0] + board[1][1] + board[1][2] + \
            board[2][0] + board[2][1] + board[2][2]

def convert_num_to_indices(num):
    row = num // 3
    col = num % 3
    return(row,col)

def read_moves(scripted):
    """Cells to play, either from --moves or typed in by the user."""
    if scripted is not None:
        for move in scripted.split(','):
            yield move
        return
    while True:
        yield input("type a cell (1-9):")

if __name__ == '__main__':
    here = os.path.dirname(os.path.abspath(__file__))
    parser = ArgumentParser()
    parser.add_argument('--verbose', default=False, action='store_true')
    parser.add_argument('--board', default=os.path.join(here, 'tests', 'blank.txt'),
                        help="starting position to load")
    parser.add_argument('--moves', default=None,
                        help="comma separated cells to play instead of reading stdin")
    args = parser.parse_args()

    logging.basicConfig(format="%(message)s")
    if args.verbose:
        logger.setLevel(logging.DEBUG)
    else:
        logger.setLevel(logging.INFO)

    x_turns, o_turns = load_board(args.board)
    moves = read_moves(args.moves)

    while True:
        # get user input and handle errors
        logger.info("-" * 40)
        print_board()
        try:
            next_cell = int(next(moves)) - 1
        except StopIteration:
            break
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
        if solver.solve([Or(get_win_formula(Cell.x)), turns_played_formula()]):
            logger.info("x wins")
            print_board()
            break
        elif x_turns == 5:
            logger.info("it's a draw")
            print_board()
            break

        # o's turn played by cpu
        o_turns += 1

        # see if o can win this turn
        if solver.solve([Or(get_win_formula(Cell.o)), turns_played_formula()]):
            logger.debug("found a way for o to win")
            result = pick_new_move(Cell.o)
            play_move(Cell.o, result[0], result[1])
            logger.info("o wins")
            print_board()
            break

        # try to block x next turn (x_turns+1) after both players have played again
        elif solver.solve([Or(get_win_formula(Cell.x)),
                           And(Or(find_all_moves(Cell.o)), Or(find_all_moves(Cell.x))),
                           turns_played_formula(extra_x=1)]):
            logger.debug("found a way to block x winning next time with board val %d" %
                            ((x_turns+1) * x_val + o_turns * o_val))
            result = pick_new_move(Cell.x) # get the winning move for x and play for o
            play_move(Cell.o, result[0], result[1])

        # otherwise find any next move for o
        elif solver.solve([Or(find_all_moves(Cell.o)), turns_played_formula()]):
            result = pick_new_move(Cell.o)
            play_move(Cell.o, result[0], result[1])

        # o can't play
        else:
            logger.info("o can't play")
            print_board()
            break
