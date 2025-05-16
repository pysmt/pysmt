; -*- SMT2 -*-
;
; This file comes from the optimathsat distribution with the permission of the authors.

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
