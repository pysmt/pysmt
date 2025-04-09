; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; MINMAX/MAXMIN:
;     These smtlib2 extensions are only supported by OptiMathSAT.
;     These are syntactic-sugar functions that make it easier
;     to define minmax/maxmin objectives.
;     The syntax is:
;
;         (minmax <term_1> ... <term_n>)
;         (maxmin <term_1> ... <term_n>)
;
; MINMAX:
;     Minimize the maximum possible loss for a worst-case scenario.
;
; MAXMIN:
;     Maximize the minimum possible gain for a worst-case scenario.
;

;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

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
