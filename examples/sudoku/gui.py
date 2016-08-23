#!/usr/bin/env python

#
# Simple GUI for solving arbitrary-sized sudoku
#
# This example uses PyGObject and requires GTK3 for correctly working

import sys
from gi.repository import Gtk
from sudoku import Sudoku


class GridWindow(Gtk.Window):

    def __init__(self, size=3):
        Gtk.Window.__init__(self, title="Sudoku Example")

        self.size = size

        # This is an instance of a Sudoku solver
        self.sudoku = Sudoku(size)

        # Draw the window
        self.table = [[Gtk.Entry() for _ in xrange(size**2)]
                                   for _ in xrange(size**2)]
        vbox = Gtk.Box(orientation=Gtk.Orientation.VERTICAL)
        self.add(vbox)

        grid = Gtk.Grid()
        vbox.add(grid)

        for row,lst in enumerate(self.table):
            for col,entry in enumerate(lst):
                entry.set_max_length(3)
                entry.set_hexpand(True)
                entry.set_vexpand(True)
                entry.set_width_chars(2)
                grid.attach(entry, col, row, 1, 1)

        self.solve_button = Gtk.Button(label="Solve")
        self.solve_button.set_hexpand(True)
        vbox.add(self.solve_button)
        self.solve_button.connect("clicked", self.solve)

        self.clear_button = Gtk.Button(label="Clear")
        self.clear_button.set_hexpand(True)
        vbox.add(self.clear_button)
        self.clear_button.connect("clicked", self.clear)


    def clear(self, c): # pylint: disable=unused-argument
        """Reset the view emptying all cells"""
        for lst in self.table:
            for entry in lst:
                entry.set_text("")


    def solve(self, c):
        """Solve the problem using the currently-entered values"""
        sq_size = self.size**2


        # First, we compute the user constraints to feed into the Sudoku solver
        constraints = []
        for i in xrange(sq_size):
            row = []
            for j in xrange(sq_size):
                txt = self.table[i][j].get_text()
                try:
                    n = int(txt)
                except ValueError:
                    n = 0
                row.append(n)
            constraints.append(row)

        # Solve the problem
        result = self.sudoku.solve(constraints)

        if result is not None:
            # Show the result
            for r, lst in enumerate(result):
                for c, val in enumerate(lst):
                    self.table[r][c].set_text(str(val))

        else:
            # The problem is unsolvable, show a message
            dialog = Gtk.MessageDialog(self, 0, Gtk.MessageType.INFO,
                                       Gtk.ButtonsType.OK,
                                       "The problem is unsolvable!")
            dialog.run()
            dialog.destroy()




def main():
    size = 3
    if len(sys.argv) > 1:
        try:
            size = int(sys.argv[1])
        except ValueError:
            print "Unknown number %s" % sys.argv[1]
            print "Usage: %s [number of tiles]" % sys.argv[0]
            exit(1)

    win = GridWindow(size)
    win.connect("delete-event", Gtk.main_quit)
    win.show_all()
    Gtk.main()


if __name__ == "__main__":
    main()
