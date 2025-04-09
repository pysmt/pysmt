; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; ALLSAT WITH OPTIMIZATION:
;     OptiMathSAT extends MathSAT's allsat support by allowing
;     this command to be used together with optimization.
;
; WARNING #1:
;     (allsat ...) is supported only when:
;     - there is only one objective function
;     - or there are multiple objectives and the solver
;       is configured to run in lexicographic mode. In other
;       words, multi-objective Boxed and Pareto optimization
;       with (allsat ...) is currently not supported in OptiMathSAT
;
; WARNING #2:
;     (allsat ...) is not supported when the optimal
;     value of some objective function is:
;     - unbounded (e.g. -INF/+INF)
;     - strict-valued (e.g. K +/- epsilon)
;
; WARNING #3:
;     (allsat ...), both in MathSAT5 and in OptiMathSAT, is a
;     non-incremental command which alters the state of the solver
;     in an irreversible way. If you want to use this command within
;     an incremental context, surround it with (push 1)/(pop 1)
;     commands.
;
; NOTE:
;     If you have any real-world problem which requires one or more
;     of the aforementioned limitations of allsat to be removed, please
;     contact the development team of OptiMathSAT about it.
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

(set-option :produce-models true)
(set-option :opt.priority lex)

;
; PROBLEM
;
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

;; enumerate all the consistent assignments (i.e. solutions) for the given
;; list of predicates. Notice that the arguments to check-allsat can only be
;; Boolean constants. If you need to enumerate over arbitrary theory atoms,
;; you can always "label" them with constants, as done above for
;; "(> (+ x y) 0)", labeled by "a"

;
; GOALS
;

(maximize x)
(maximize y)

(check-sat)
(get-objectives)

(exit)
