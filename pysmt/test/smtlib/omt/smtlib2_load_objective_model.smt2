; -*- SMT2 -*-
;
; This file comes from the optimathsat distribution with the permission of the authors.


(set-option :produce-models true)

;
; PROBLEM
;
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (and
            (<= 3 x)
            (<= x 5)
))
(assert (and
            (<= 10 z)
            (<= z 20)
))
(assert (= y (+ (* 2 x) z)))

;
; GOALS
;
(minimize x)
(maximize y)

(check-sat)

(exit)
