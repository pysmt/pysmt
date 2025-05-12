; -*- SMT2 -*-
;
; This file comes from the optimathsat distribution with the permission of the authors.

(set-option :produce-models true)
(set-option :config opt.priority=box)
(set-option :config opt.verbose=true)

;
; PROBLEM
;
(declare-fun production_cost () Int)
(declare-fun used_machines () Int)
(declare-fun q0 () Int)           ; machine 'i' production load
(declare-fun q1 () Int)
(declare-fun q2 () Int)
(declare-fun q3 () Int)
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

(check-sat)

(exit)
