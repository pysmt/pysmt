#
# This file is part of pySMT.
#
#   Copyright 2015 Andrea Micheli and Marco Gario
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
from pysmt.test import TestCase, skipIfNoSolverForLogic, main
from pysmt.shortcuts import *
from pysmt.printers import  HRPrinter
from pysmt.typing import INT,STRING
from pysmt.logics import QF_SLIA

class TestSTRING(TestCase):
    
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_length(self):
        s1 = Symbol("s1",STRING)
        s2 = Symbol("s2",STRING)
        solver = Solver(logic=QF_SLIA)
        solver.add_assertion(  Not( Implies( Equals(s1,s2),
                                             Equals(str_length(s2), str_length(s1))
                                            )
                                   )
                             )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_concat(self):
        s1 = Symbol("s1",STRING)
        s2 = Symbol("s2",STRING)
        solver = Solver(logic=QF_SLIA)
        solver.add_assertion( Not (And (
                                   GE(
                                      str_length(str_concat(s1,s2)), 
                                      str_length(s1)
                                    ), 
                                   GE(
                                      str_length(str_concat(s1,s2)), 
                                      str_length(s2)
                                      )
                                   )
                                   )
                             )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_contains(self):
        s1 = Symbol("s1",STRING)
        s2 = Symbol("s2",STRING)
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        solver.add_assertion(  (
                                   Not(Implies(And(str_contains(s1, s2) , str_contains(s2,s1)), Equals(s1, s2)))
                                  )
                            )

        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_indexof(self):
        s1 = String("Hello World")
        t1 = String("o")
        
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion( 
                               Not(Equals(str_indexof(s1, t1, Int(0)), Int(4)))    
                            )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_replace(self):
        s1 = Symbol("s1",STRING)
        s2 = Symbol("s2",STRING)
        s3 = Symbol("s3",STRING)
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        
        solver.add_assertion( GT(str_length(s1), Int(0)))
        solver.add_assertion( GT(str_length(s2), Int(0)))
        solver.add_assertion( GT(str_length(s3), Int(0)))
        solver.add_assertion( Not(str_contains(s1, s2)))
        solver.add_assertion( Not(str_contains(s1, s3)))
        
        solver.add_assertion( Not (
                                   Equals(str_replace(str_replace(s1, s2,s3), s3, s2), s1)
                                  )
                            )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_substr(self):
        s1 = Symbol("s1",STRING)
        i = Symbol("index",INT)
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion(GT(i,Int(0)))
        solver.add_assertion(GT(str_length(s1),Int(1)))
        solver.add_assertion(LT(i,str_length(s1)))
        
        
        solver.add_assertion( 
                                Equals(
                                      str_concat(
                                                 str_substr(s1, Int(0), i),
                                                 str_substr(s1, Plus(i,Int(1)), str_length(s1))
                                                 ), 
                                      s1
                                      )
                            )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
    
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_prefixof(self):
        s1 = Symbol("s1",STRING)
        s2 = Symbol("s2",STRING)
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion(GT(str_length(s1), Int(2)))
        solver.add_assertion(GT(str_length(s2), str_length(s1)))
        
        solver.add_assertion( 
                                And(str_prefixof(s2,s1 ), str_contains(s2, s1))
                            )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_suffixof(self):
        s1 = Symbol("s1",STRING)
        s2 = Symbol("s2",STRING)
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion(GT(str_length(s1), Int(2)))
        solver.add_assertion(GT(str_length(s2), str_length(s1)))
        
        solver.add_assertion( 
                                And(str_suffixof(s2,s1 ), str_contains(s2, s1))
                            )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
       
    
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_to_int(self):
        s = String("1")
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion( 
                               Not(Equals(str_to_int(s),Int(1)))
                             )

        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_int_to_str(self):
        s = String("1")
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion( 
                               Not( Equals((int_to_str(Int(1))) , s))
                            )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
      
    
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_to_unit16(self):
        s = String("1")
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion( 
                               Not( Equals( str_to_uint16(s),Int(1)))
                             )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
        
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_uint16_to_str(self):
        s = String("1")
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion( 
                               Not( Equals((int_to_str(Int(1))) , s))
                            )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
        
       
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_to_uint32(self):
        s = String("1")
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion( 
                               Not( Equals( str_to_uint32(s),Int(1)))
                             )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
    
       
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_uint32_to_str(self):
        s = String("1")
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion( 
                               Not( Equals((int_to_str(Int(1))) , s))
                            )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return
      
    @skipIfNoSolverForLogic(QF_SLIA)
    def test_str_charat(self):
        s1 = String("Hello")
        solver = Solver(logic=QF_SLIA)
        solver.set_option('strings-exp','true')
        
        solver.add_assertion( 
                                Not(Equals(str_charat(s1, Int(0)), String("H")))
                            )
        res = solver.solve()
        if ( res):
            print solver.get_model()
        assert not res, "Was expecting  FALSE" 
        return

if __name__ == "__main__":
    main()
