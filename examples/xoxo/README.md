# Noughts and Crosses player with SAT solver

uses pySMT and the solver of your choice to play O's and X's. The computer plays Os.
Player X is given the value 1, and player O is given value 10. 
This makes it easy to detect number of turns taken as well as if a player has won.

# How it works

The game works by setting up a board with assertions for the valid settings.
Then a set of assertions are created to detect a win, and another set for which turn it is.
The solver uses these sets of assertions to determine the order of play:

* checking if x has won: give up
* look for o to win: play that move
* look for x to win next turn: play in that space
* looking for a win in the next 1 to 5 turns: play in a space (prioritise central position
* if no possiblity for the computer to win, give up.

# requirements

This installs pysmt and the z3 solver:

    pip install pysmt
    pysmt-install --z3

