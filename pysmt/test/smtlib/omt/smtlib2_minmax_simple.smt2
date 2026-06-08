; -*- SMT2 -*-
;
; This file comes from the optimathsat distribution with the permission of the authors.

(set-option :produce-models true)
(set-option :opt.priority box)

;
; PROBLEM
;
(declare-fun x_real () Real)
(declare-fun y_real () Real)
(declare-fun z_real () Real)

(assert (and
    (<= 10 x_real) (<= x_real 100)
    (<=  0 y_real) (<= y_real 50)
    (<= 17 z_real) (<= z_real 42)
))

;
; GOAL:
;
(minmax x_real y_real z_real)
(maxmin x_real y_real z_real)

;
; OPTIMIZATION
;
(check-sat)
(get-objectives)
(get-model)
(exit)
