"""Play noughts and crosses (tic-tac-toe) against an SMT solver.

Encoding
--------
The board is nine bitvector variables, each constrained to hold one of three
values: 0 for an empty cell, 1 for a cross, 2 for a nought.  A move that has
been played is pinned down with an equality assertion, so the solver's
assertion stack *is* the current position.  Everything else is a query: the
solver is asked whether some formula can hold on top of that position, and
if it can, the model tells us where to play.

The trick that makes those queries work is `get_board_sum()`, the sum of all
nine cells.  The played cells are pinned, so constraining the total to be
exactly `crosses + 2 * noughts` leaves no room for extra counters and forces
every unplayed cell to 0 in the model.  Asking for a total one (or two)
higher instead describes a position with exactly one more cross (or nought)
than has really been played, which is how the solver is made to invent the
next move rather than merely confirm the current one.  Five bits are plenty:
the largest total the sum can ever reach is 9 * 2 = 18.

The game
--------
Every turn the solver is asked, in this order:

  1. can x hold a whole line?               -> the human has won
  2. can o hold a line one nought from now? -> play that winning nought
  3. can x hold a line one cross from now?  -> play there to block it
  4. is any cell still free?                -> play in one of them

The model of query 2, 3 or 4 puts a counter on a cell that has not been
played yet; `pick_new_move()` reads it back out, and that is the move.  Note
that this looks exactly one move ahead, so the computer is beatable.

Run it
------
    python xoxo.py                      # play from the empty board
    python xoxo.py --board boards/midgame.txt
    python xoxo.py --moves 5,1,9        # scripted game, no input needed
"""
from pysmt.shortcuts import FreshSymbol, BV, BVAdd, Or, And, Equals, Solver
from pysmt.typing import BVType
from pysmt.logics import QF_BV
from enum import Enum
from functools import reduce
import os
import sys
import logging
from argparse import ArgumentParser

# wide enough to hold the sum of the whole board without wrapping (9 * 2 = 18)
VECT_WIDTH = 5

class Cell(Enum):
    """What a cell can hold. The value doubles as the cell's numeric weight."""
    s = 0 # space
    x = 1 # cross - human player, goes first
    o = 2 # nought - cpu player

    @property
    def bv(self):
        """This cell content as a bitvector constant."""
        return BV(self.value, VECT_WIDTH)

# the eight lines that win the game, as lists of (row, col)
LINES = [[(r, 0), (r, 1), (r, 2)] for r in range(3)] + \
        [[(0, c), (1, c), (2, c)] for c in range(3)] + \
        [[(0, 0), (1, 1), (2, 2)], [(0, 2), (1, 1), (2, 0)]]

logger = logging.getLogger('xoxo')

board = [[FreshSymbol(BVType(VECT_WIDTH)) for _ in range(3)]
         for _ in range(3)]

# python-side copy of the position: (row, col) -> Cell. The solver knows it
# too, but only IncrementalTrackingSolver exposes .assertions, so keep our own
played = {}

x_turns = 0
o_turns = 0

# the example only needs bitvectors: asking for the logic lets pySMT pick any
# solver that supports it, instead of falling back on its default logic
solver = Solver(logic=QF_BV)

# every cell holds a blank, a cross or a nought and nothing else
for row in board:
    for cell in row:
        solver.add_assertion(Or([Equals(cell, content.bv) for content in Cell]))

def get_board_sum():
    """The sum of all nine cells, as a single bitvector term."""
    return reduce(BVAdd, (cell for row in board for cell in row))

def turns_played_formula(extra_x=0, extra_o=0):
    """Pin the total value of the board, and hence how many counters are on it.

    With no extras this says "nothing is on the board but the moves that were
    really played", which forces the free cells to be blank in the model. The
    extras ask for a hypothetical position with that many more counters.
    """
    total = (x_turns + extra_x) * Cell.x.value + (o_turns + extra_o) * Cell.o.value
    return Equals(get_board_sum(), BV(total, VECT_WIDTH))

def get_win_formula(p):
    """One formula per line, each saying that p holds that whole line."""
    return [And([Equals(board[r][c], p.bv) for r, c in line]) for line in LINES]

def free_cells():
    return [(r, c) for r in range(3) for c in range(3) if (r, c) not in played]

def find_all_moves(p):
    """One formula per free cell, each saying that p plays there."""
    logger.debug("finding all possible moves for %s" % p.name)
    return [Equals(board[r][c], p.bv) for r, c in free_cells()]

def pick_new_move(p):
    """Read back, from the last model, the cell it gave to p."""
    logger.debug("picking a move for %s" % p.name)
    for r, c in free_cells():
        if solver.get_value(board[r][c]) == p.bv:
            return (r, c)

def play_move(p, row, col):
    logger.debug("adding assertion for player %s at (%d, %d)" % (p.name, row, col))
    solver.add_assertion(Equals(board[row][col], p.bv))
    played[(row, col)] = p

def already_played(row, col):
    return (row, col) in played

def load_board(path):
    """Play out a starting position: one line per row, cells named x, o or -."""
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

def print_board():
    # get_value() reads the last model, and adding an assertion invalidates it,
    # so solve for the board as it actually stands before printing it
    if not solver.solve([turns_played_formula()]):
        raise RuntimeError("the board is in an inconsistent state")
    for row in board:
        line = ""
        for cell in row:
            if solver.get_value(cell) == Cell.x.bv:
                line += "x "
            elif solver.get_value(cell) == Cell.o.bv:
                line += "o "
            else:
                line += "- "
        logger.info(line)

def convert_num_to_indices(num):
    return (num // 3, num % 3)

def read_moves(scripted):
    """Cells to play, either from --moves or typed in by the user."""
    if scripted is not None:
        for move in scripted.split(','):
            yield move
        return
    while True:
        try:
            yield input("type a cell (1-9):")
        except EOFError: # stdin ran out, e.g. when the input is piped in
            return

if __name__ == '__main__':
    here = os.path.dirname(os.path.abspath(__file__))
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--verbose', default=False, action='store_true')
    parser.add_argument('--board', default=os.path.join(here, 'boards', 'blank.txt'),
                        help="starting position to load")
    parser.add_argument('--moves', default=None,
                        help="comma separated cells to play instead of reading stdin")
    args = parser.parse_args()

    logging.basicConfig(format="%(message)s", stream=sys.stdout)
    logger.setLevel(logging.DEBUG if args.verbose else logging.INFO)

    x_turns, o_turns = load_board(args.board)
    moves = read_moves(args.moves)

    while True:
        logger.info("-" * 40)
        print_board()

        # get the human's move and handle bad input
        try:
            next_cell = int(next(moves)) - 1
        except StopIteration:
            break
        except ValueError:
            continue
        if next_cell < 0 or next_cell > 8:
            continue
        row, col = convert_num_to_indices(next_cell)
        if already_played(row, col):
            logger.info("that cell is already taken")
            continue
        play_move(Cell.x, row, col)
        x_turns += 1

        # 1. did that move give x a line?
        if solver.solve([Or(get_win_formula(Cell.x)), turns_played_formula()]):
            logger.info("x wins")
            print_board()
            break
        elif x_turns == 5:
            # x has had all five of its moves, so the board is full
            logger.info("it's a draw")
            print_board()
            break

        # 2. can o finish a line with the nought it is about to play?
        if solver.solve([Or(get_win_formula(Cell.o)),
                         turns_played_formula(extra_o=1)]):
            logger.debug("found a way for o to win")
            play_move(Cell.o, *pick_new_move(Cell.o))
            o_turns += 1
            logger.info("o wins")
            print_board()
            break

        # 3. could x finish a line next turn? if so, take that cell first.
        # the position asked for has one more cross and one more nought than
        # has been played, so the model shows both moves at once
        elif solver.solve([Or(get_win_formula(Cell.x)),
                           And(Or(find_all_moves(Cell.o)), Or(find_all_moves(Cell.x))),
                           turns_played_formula(extra_x=1, extra_o=1)]):
            logger.debug("found a way to block x winning next time")
            block = pick_new_move(Cell.x) # x's winning cell, played by o instead
            play_move(Cell.o, *block)
            o_turns += 1

        # 4. no threat either way, so just take any free cell
        elif solver.solve([Or(find_all_moves(Cell.o)),
                           turns_played_formula(extra_o=1)]):
            play_move(Cell.o, *pick_new_move(Cell.o))
            o_turns += 1

        else:
            logger.info("o can't play")
            print_board()
            break
