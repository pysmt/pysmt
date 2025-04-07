; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; ASSERT-SOFT:
;     Both OptiMathSAT and Z3 support the command
;
;         (assert-soft <term> :weight <term> :id <string>)
;
;     but they handle it differently. Z3 minimizes by
;     default the objective function identified by <string>,
;     whereas OptiMathSAT does not. To emulate Z3's behaviour,
;     append the following line before the next (check-sat)
;     in the formula:
;
;         (minimize <string>)
;
;     In OptiMathSAT, (assert-soft ...) can be used to define
;     arbitrary Pseudo-Boolean objectives, which can be either
;     minimized or maximized. To that extent, the weight of
;     a soft-clause is allowed to have zero or negative value.
;     The corresponding goal <string> can be used inside other
;     constraints (e.g. to express a cardinality constraint over
;     a PB sum) or combined with other expressions to form more
;     complex objectives. 
;
; WARNING:
;     OptiMathSAT and Z3 handle the :weight argument differently.
;     Its argument is a <term> for OptiMathSAT, whereas it is a 
;     <numeral> constant for Z3.
;     (for more details about syntax,
;                       see: smtlib2_assert_soft.smt2)
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

;
; MaxSMT Engine:
; - omt:    use OMT-based encoding & engine
; - maxres: use Maximum Resolution engine
; - ext:    use external MaxSAT solver (only via API)
;
(set-option :produce-models true)
(set-option :opt.maxsmt_engine maxres)

;
; MaxSMT PROBLEM
;
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x (- y)))
(assert-soft (< x 0) :weight 1 :id goal)
(assert-soft (< x y) :weight 1 :id goal)
(assert-soft (< y 0) :weight 1 :id goal)

;
; OPTIMIZATION + OPTIMUM VALUE
;
(check-sat)
(get-objectives)

(exit)

