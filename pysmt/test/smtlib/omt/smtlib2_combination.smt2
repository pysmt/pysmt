; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; LINEAR OBJECTIVE COMBINATION:
;     In OptiMathSAT, an objective can be given a name
;     which can then be used to:
;     - express constraints that involve an objective function
;     - formulate new objectives defined in terms of another
;       objective.
;     - retrieve the value of an objective function from
;       the optimal model using '(get-value ...)'
;     A label remains in scope as long as the associated
;     objective is in scope.
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :produce-models true)
(set-option :config opt.priority=box)
(set-option :config opt.verbose=true)

;
; PROBLEM
;
(declare-fun production_cost () Real)
(declare-fun q0 () Real)           ; machine 'i' production load
(declare-fun q1 () Real) 
(declare-fun q2 () Real) 
(declare-fun q3 () Real)
(declare-fun m0 () Bool)           ; machine 'i' is used
(declare-fun m1 () Bool)
(declare-fun m2 () Bool)
(declare-fun m3 () Bool)
(assert (<= 1100 (+ q0 q1 q2 q3))) ; set goods quantity
(assert (and                       ; set goods produced per machine
    (and (<= 0 q0) (<= q0 800)) (and (<= 0 q1) (<= q1 500))
    (and (<= 0 q2) (<= q2 600)) (and (<= 0 q3) (<= q3 200))
))
(assert (and                       ; set machine `used` flag
    (=> (< 0 q0) m0) (=> (< 0 q1) m1)
    (=> (< 0 q2) m2) (=> (< 0 q3) m3)
))
(assert-soft (not m0) :id used_machines)
(assert-soft (not m1) :id used_machines)
(assert-soft (not m2) :id used_machines)
(assert-soft (not m3) :id used_machines)

;
; GOALS
; - 'total_cost' is a combination of 'production_cost'
;   and 'used_machines'
;
(minimize 
    (+ (* q0 8) (* q1 9) (* q2 9) (* q3 5)) 
    :id production_cost
)
(minimize (+ production_cost 
             (* (/ 785 10) (+ (* 2 used_machines) 8))
          )
          :id total_cost
) 

;
; OPTIMIZATION + MODEL VALUES
;
(check-sat)
(get-objectives)

(load-objective-model 1)
(get-value (total_cost))
(get-value (production_cost))

(exit)
