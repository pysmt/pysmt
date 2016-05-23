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
from nose.plugins.attrib import attr
from pysmt.test import TestCase, skipIfSolverNotAvailable, main
from pysmt.test.examples import get_example_formulae
from pysmt.environment import get_env
from pysmt.shortcuts import Array, Store, Int
from pysmt.typing import INT



class TestSimplify(TestCase):

    @attr("slow")
    @skipIfSolverNotAvailable("z3")
    def test_simplify_qf(self):
        simp = get_env().simplifier
        Iff = get_env().formula_manager.Iff
        for (f, _, _, logic) in get_example_formulae():
            if logic.is_quantified(): continue
            simp.validate_simplifications = True
            sf = f.simplify()
            simp.validate_simplifications = False
            self.assertValid(Iff(f, sf), solver_name='z3',
                             msg="Simplification did not provide equivalent "+
                                "result:\n f= %s\n sf = %s" % (f, sf))

    @attr("slow")
    @skipIfSolverNotAvailable("z3")
    def test_simplify_q(self):
        simp = get_env().simplifier
        Iff = get_env().formula_manager.Iff
        for (f, _, _, logic) in get_example_formulae():
            if logic.quantifier_free: continue
            simp.validate_simplifications = True
            sf = f.simplify()
            simp.validate_simplifications = False
            self.assertValid(Iff(f, sf), solver_name='z3',
                             msg="Simplification did not provide equivalent "+
                            "result:\n f= %s\n sf = %s" % (f, sf))


    def test_array_value(self):
        a1 = Array(INT, Int(0), {Int(12) : Int(10)})
        a2 = Store(Array(INT, Int(0)), Int(12), Int(10))
        self.assertEquals(a1, a2.simplify())



if __name__ == '__main__':
    main()
