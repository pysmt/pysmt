# Noughts and Crosses/Tic-Tac-Toe player with SAT solver

uses pySMT and the solver of your choice to play O's and X's. The computer plays Os.

# How it works

The game works by setting up a board of bit vectors. Every turn an assertion is added
for that player's value.

The solver then searches for solutions that satisfy in order:

* x has won: give up
* o to win next turn: play that move
* x to win next turn: play in that space
* play in an available space
* if no possiblity for the computer to win, give up.

# requirements

This installs pysmt and the z3 solver:

    pip install pysmt
    pysmt-install --z3
