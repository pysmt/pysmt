Noughts and Crosses
===================

* `xoxo.py </examples/xoxo/xoxo.py>`_ : plays noughts and crosses (tic-tac-toe)
  against you. You are ``x`` and move first, the solver plays ``o``.

Run it with::

    python xoxo.py                            # play from the empty board
    python xoxo.py --board boards/midgame.txt # start from a given position
    python xoxo.py --moves 5,1,9              # scripted game, no input needed
    python xoxo.py --verbose                  # show the queries being made

Any solver supporting ``QF_BV`` will do, for instance::

    pysmt-install --z3

Encoding the board
------------------

The board is nine ``BVType(5)`` variables. Each one is constrained once, up
front, to hold one of three values:

.. code:: python

    Or(Equals(cell, BV(0, 5)),   # blank
       Equals(cell, BV(1, 5)),   # a cross
       Equals(cell, BV(2, 5)))   # a nought

A move is *pinned* by asserting ``Equals(board[row][col], BV(1, 5))``, so the
solver's assertion stack is a faithful record of the position: it is
satisfied by exactly the boards that extend the game as played so far.

Everything else the program does is a *query*. It never asks the solver "what
is the board?", it asks "can the board also satisfy this?" and, if it can,
reads the answer out of the model.

The board sum
-------------

Constraining the position is only half the job: nothing so far stops the
solver from filling the empty cells with whatever it likes. That is what the
sum of all nine cells is for:

.. code:: python

    Equals(get_board_sum(), BV(crosses * 1 + noughts * 2, 5))

The played cells are already pinned and contribute a fixed amount, and no
cell can be negative, so pinning the total to exactly that amount leaves no
room for anything more: every unplayed cell is forced to ``0``. Five bits are
enough because the largest total possible is ``9 * 2 = 18``.

Asking for a total that is *one nought higher* is the interesting case. Now
the solver must place exactly one extra nought somewhere, and it is free to
choose where. Combine that with a win formula and the question becomes "is
there a single nought that completes a line?", and the answer, if there is
one, is in the model.

What is asked each turn
-----------------------

#. ``Or(lines of x)`` at the current total. Satisfiable: the human has won.
#. ``Or(lines of o)`` with one extra nought. Satisfiable: play that nought.
#. ``Or(lines of x)`` with one extra nought *and* one extra cross, both on
   free cells. Satisfiable: play where x would have won.
#. ``Or(free cell is a nought)`` with one extra nought. Play in any free cell.

The third query is worth a second look. It describes a board two moves into
the future: one more nought (o's move now) and one more cross (x's reply)
where x holds a line. Any model of it therefore contains both the cell x
wants and a cell for o, and playing o on *x's* cell is exactly the block.

Reading a move back out of a model happens in ``pick_new_move()``: walk the
cells that have not been played and return the first one the model gave to
the player we asked about.

Board files
-----------

One line per row, three cells per line separated by spaces, ``x``, ``o`` or
anything else for empty::

    x - -
    - o -
    - - -

The loader replays the position, so the turn counts stay consistent. Since
``x`` moves first, a position that is x's turn must have as many crosses as
noughts.

Limitations
-----------

The solver only looks one move ahead: it wins when it can and blocks when it
must, but it does not plan, so it can be beaten.
