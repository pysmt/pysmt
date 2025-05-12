; -*- SMT2 -*-
;
; This file comes from the optimathsat distribution with the permission of the authors.

(set-option :produce-models true)
(set-option :opt.priority pareto)

;
; PROBLEM
;
(declare-fun a_real () Real)
(declare-fun b_real () Real)
(assert (or
    (and (= a_real 1.0) (= b_real 1.0))
    (and (= a_real 2.0) (= b_real 1.0))
    (and (= a_real 1.0) (= b_real 2.0))
    (and (= a_real 2.0) (= b_real 2.0))
    (and (= a_real 3.0) (= b_real 1.0))
    (and (= a_real 1.0) (= b_real 3.0))
))

;
; GOALS
;
(maximize a_real)
(maximize b_real)

;
; INCREMENTAL OPTIMIZATION
;     3 pareto solutions
;     + unsat step
;
(check-sat)
(get-objectives)

(check-sat)
(get-objectives)

(check-sat)
(get-objectives)

(check-sat)
(get-objectives)

(exit)
