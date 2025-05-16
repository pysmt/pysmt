; -*- SMT2 -*-
;
; This file comes from the optimathsat distribution with the permission of the authors.


(set-option :produce-models true)
(set-option :opt.maxsmt_engine maxres)

;
; MaxSMT PROBLEM
;
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x (- y)))
(assert-soft (< x 0) :weight 0.5 :id goal)
(assert-soft (< x y) :weight 0.5 :id goal)
(assert-soft (< y 0) :weight 0.5 :id goal)

;
; OPTIMIZATION + OPTIMUM VALUE
;
(check-sat)
(get-objectives)

(exit)
