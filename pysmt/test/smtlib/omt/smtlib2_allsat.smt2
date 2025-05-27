; -*- SMT2 -*-
;
; This file comes from the optimathsat distribution with the permission of the authors.

(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)

(assert (= (> (+ x y) 0) a))
(assert (= (< (+ (* 2 x) (* 3 y)) (- 10)) c))
(assert (and (or a b) (or c d)))

(assert (=> e (< 10 x)))
(assert (=> (< 10 x) e))

(assert (<= x 100))
(assert (<= y 100))

(assert a)
(assert b)
(assert e)

(maximize x)
(maximize y)

(check-sat)
(get-objectives)

(exit)
