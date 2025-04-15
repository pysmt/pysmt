; -*- SMT2 -*-
;
; This file comes from the optimathsat distribution with the permission of the authors.

(set-option :produce-models true)
(set-option :config opt.priority=box)
(set-option :config opt.verbose=true)

;
; PROBLEM
;
(declare-fun real_x () Real)
(declare-fun real_y () Real)
(declare-fun real_z () Real)
(assert (and
        (<= 42 real_x)
        (<= real_y real_x)
        (<= real_z 24)
))

;
; GOALS
;
(minimize real_x)
(maximize real_y)
(maximize real_z)

;
; OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)
