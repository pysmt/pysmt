; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; WARNING:
;     OptiMathSAT and Z3 have different default behaviours
;     when multiple objectives are optimized in the same
;     formula. Z3 handles them lexicographically, whereas
;     OptiMathSAT handles them in boxed (multi-independent) mode.
;     Therefore, the following option should be correctly
;     set on any lexicographic formula:
;
;         (set-option :opt.priority lex)
;
;     When model-generation is enabled, the lexicographic
;     search ends with the optimum model stored in the
;     environment and ready for inspection.
;     It is also possible to view the partially-optimized
;     model associated with each objective on the stack
;     by means of the '(load-objective-model <numeral>)' command.
;     (for more details, see: smtlib2_load_objective_model.smt2)
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :produce-models true)
(set-option :opt.priority lex)

;
; PROBLEM
;
(declare-fun cost () Int)
(declare-fun s1 () Bool)
(declare-fun s2 () Bool)
(declare-fun s3 () Bool)
(declare-fun s4 () Bool)
(declare-fun q1 () Int)
(declare-fun q2 () Int)
(declare-fun q3 () Int)
(declare-fun q4 () Int)

; set goods quantity
(assert (= 250 (+ q1 q2 q3 q4)))

; set goods offered by each supplier
(assert (or (= q1 0) (and (<= 50 q1) (<= q1 250))))
(assert (or (= q2 0) (and (<= 100 q2) (<= q2 150))))
(assert (or (= q3 0) (and (<= 100 q3) (<= q3 100))))
(assert (or (= q4 0) (and (<= 50 q4) (<= q4 100))))

; supplier is used if sends more than zero items
(assert (and (=> s1 (not (= q1 0))) (=> s2 (not (= q2 0)))
           (=> s3 (not (= q3 0))) (=> s4 (not (= q4 0)))))

;
; GOAL
;
(minimize (+ (* q1 23) (* q2 21) (* q3 20) (* q4 10)))

; supply from the largest number of suppliers
(assert-soft s1 :id unused_suppliers)
(assert-soft s2 :id unused_suppliers)
(assert-soft s3 :id unused_suppliers)
(assert-soft s4 :id unused_suppliers)


;
; OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)

;
; LEXICOGRAPHIC OPTIMIZATION OPTIONS
;     The SMT-based Unified Lex Algorithm is not guaranteed to converge
;     towards an optimal solution when dealing with Real cost functions.
;     
; -opt.lex.engine=STR
;          Configures the engine for Lexicographic optimization. Possible values 
;          are:  
;           - uni: SMT-based Unified Lex Algorithm
;           - ite: OMT-based Iterated Lex Algorithm (default)
;
