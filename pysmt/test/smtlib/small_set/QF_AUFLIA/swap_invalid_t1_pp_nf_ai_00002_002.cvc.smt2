(set-logic QF_AUFLIA)
(set-info :source |
Benchmarks used in the followin paper:
Big proof engines as little proof engines: new results on rewrite-based satisfiability procedure
Alessandro Armando, Maria Paola Bonacina, Silvio Ranise, Stephan Schulz. 
PDPAR'05
http://www.ai.dist.unige.it/pdpar05/


|)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(set-info :status sat)
(declare-fun a1 () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun i1 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (let ((?v_3 (select a1 i1)) (?v_4 (select a1 i0))) (let ((?v_0 (store (store a1 i1 ?v_4) i0 ?v_3))) (let ((?v_1 (select ?v_0 i1))) (let ((?v_2 (store (store ?v_0 i1 ?v_1) i1 ?v_1)) (?v_5 (store (store a1 i0 ?v_3) i1 ?v_4))) (let ((?v_6 (store (store ?v_5 i0 (select ?v_5 i1)) i1 (select ?v_5 i0)))) (let ((?v_7 (sk ?v_2 ?v_6))) (not (= (select ?v_2 ?v_7) (select ?v_6 ?v_7))))))))))
(check-sat)
(exit)
