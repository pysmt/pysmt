(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun p () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (= ((_ sign_extend 24) (_ bv72 8)) ((_ sign_extend 24) (select p (_ bv0 32))))))
(assert (not (= ((_ sign_extend 24) (_ bv76 8)) ((_ sign_extend 24) (select p (_ bv0 32))))))
(assert (not (= ((_ sign_extend 24) (_ bv80 8)) ((_ sign_extend 24) (select p (_ bv0 32))))))
(assert (= ((_ sign_extend 24) (_ bv82 8)) ((_ sign_extend 24) (select p (_ bv0 32)))))
(check-sat)
(exit)
