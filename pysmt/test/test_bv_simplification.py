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
from six.moves import xrange

from pysmt.shortcuts import Solver, BVAnd, BVOr, BVXor, BVConcat, BVULT, BVUGT, \
    BVULE, BVUGE, BVAdd, BVSub, BVMul, BVUDiv, BVURem, BVLShl, BVLShr, BVNot, \
    BVNeg, BVZExt, BVSExt, BVRor, BVRol, BV, BVExtract, BVSLT, BVSLE, BVComp, \
    BVSDiv, BVSRem, BVAShr
from pysmt.test import TestCase, skipIfSolverNotAvailable, main


class TestBvSimplification(TestCase):

    def setUp(self):
        self.width = 4
        self.bin_operators = [BVAnd, BVOr, BVXor, BVConcat, BVULT, BVUGT, BVULE,
                              BVUGE, BVAdd, BVSub, BVMul, BVUDiv, BVURem, BVLShl,
                              BVLShr, BVSLT, BVSLE, BVComp, BVSDiv, BVSRem,
                              BVAShr]
        self.unary_operators = [BVNot, BVNeg]
        self.special_operators = [BVZExt, BVSExt, BVRor, BVRol]
        self.solver = None
        self.solver_simplify = None

    def all_bv_numbers(self, width=None):
        if width is None:
            width = self.width
        for x in xrange(2 ** width):
            yield BV(x, width)

    @skipIfSolverNotAvailable("msat")
    def test_msat(self):
        self.solver = Solver(name="msat")
        conv = self.solver.converter
        self.solver_simplify = lambda x: conv.back(conv.convert(x))
        # Run the tests
        self.all_unary()
        self.all_binary()
        self.all_special()
        self.extract()
        self.concat_different_length()

    def check(self, f):
        simp_f = f.simplify()
        solver_f = self.solver_simplify(f)
        self.assertEqual(solver_f, simp_f)

    def all_binary(self):
        for l in self.all_bv_numbers():
            for r in self.all_bv_numbers():
                for op in self.bin_operators:
                    try:
                        self.check(op(l, r))
                    except AssertionError:
                        if op in [BVUDiv, BVSDiv] and r == BV(0, r.bv_width()):
                            print("Warning: Division value mismatch.")
                            print(l,op,r)

    def all_unary(self):
        for l in self.all_bv_numbers():
            for op in self.unary_operators:
                self.check(op(l))

    def extract(self):
        for l in self.all_bv_numbers():
            for s in xrange(0, self.width):
                for e in xrange(s, self.width):
                    self.check(BVExtract(l, start=s, end=e))

    def concat_different_length(self):
        for l in self.all_bv_numbers():
            for w in [1, self.width-1, self.width+1]:
                for r in self.all_bv_numbers(w):
                    self.check(BVConcat(l, r))

    def all_special(self):
        for l in self.all_bv_numbers():
            for n in xrange(0, self.width + 1):
                for op in self.special_operators:
                    self.check(op(l, n))


if __name__ == '__main__':
    main()
