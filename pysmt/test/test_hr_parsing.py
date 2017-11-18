#
# This file is part of pySMT.
#
#   Copyright 2014 Andrea Micheli and Marco Gario
#
#   Licensed under the Apache License, Version 2.0 (the "License");
#   you may not use this file except in compliance with the License.
#   You may obtain a copy of the License at
#
#       http://www.apache.org/licenses/LICENSE-2.0
#
#   Unless required by applicable law or agreed to in writing, software
#   distributed under the License is distributed on an "AS IS" BASIS,
#   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#   See the License for the specific language governing permissions and
#   limitations under the License.
#
import unittest
import tempfile, os

from pysmt.parsing import HRParser, parse
from pysmt.shortcuts import Iff, Symbol, And, Or, LE, Real, Plus, Minus
from pysmt.test.examples import get_example_formulae
from pysmt.exceptions import NoSolverAvailableError
from pysmt.test import TestCase
from pysmt.typing import REAL


class TestHRParser(TestCase):

    def test_precedences(self):
        p = HRParser()

        a,b,c = (Symbol(v) for v in "abc")
        x,y = (Symbol(v, REAL) for v in "xy")

        tests = []
        tests.append(("a | b & c", Or(a, And(b,c))))
        tests.append(("a & b | c", Or(And(a, b) ,c)))

        f1 = LE(Plus(Plus(x, y), Real(5)), Real(7))
        f2 = LE(Plus(x, Real(5)), Minus(Real(7), y))
        tests.append(("x + y + 5.0 <= 7.0", f1))
        tests.append(("x + 5.0 <= 7.0 - y", f2))
        tests.append(("x + y + 5.0 <= 7.0 & x + 5.0 <= 7.0 - y", And(f1, f2)))
        tests.append(("x + 5.0 <= 7.0 - y | x + y + 5.0 <= 7.0 & x + 5.0 <= 7.0 - y",
                      Or(f2, And(f1, f2))))

        for string, formula in tests:
            self.assertEqual(p.parse(string), formula)
            self.assertEqual(parse(string), formula)


    def test_file_parsing(self):
        fname = None
        try:
            fd, fname = tempfile.mkstemp()
            os.close(fd)

            with open(fname, "w") as f:
                f.write("a | b & c\n")

            a,b,c = (Symbol(v) for v in "abc")
            p = HRParser()

            expected = Or(a, And(b,c))
            parsed = p.parse_fname(fname)

            self.assertEqual(parsed, expected)

        finally:
            if fname is not None:
                os.unlink(fname)

    def test_examples(self):
        p = HRParser()
        for (f, _, _, _) in get_example_formulae():
            s = f.serialize()
            res = p.parse(s)
            check = (res == f)
            if not check:
                try:
                    self.assertValid(Iff(res, f))
                except NoSolverAvailableError:
                    pass



if __name__ == '__main__':
    unittest.main()
