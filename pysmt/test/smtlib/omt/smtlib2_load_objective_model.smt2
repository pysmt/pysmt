; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; WARNING:
;     Model Generation must be enabled; The Objective/formula
;     must also be satisfiable.
;
; LOAD-OBJECTIVE-MODEL:
;     At the end of a Boxed/Multi-Independent optimization, each
;     objective has its own Optimum Model which can be different
;     from that of other objectives.
;     In this case, the user must tell OptiMathSAT which model
;     wants to be loaded for inspection using the command:
;
;         (load-objective-model N)
;
;     where N is the index, starting from zero, of the objective
;     on the stack of objectives. e.g.:
;
;         (minimize ...) ; index: 0
;         (maximize ...) ; index: 1
;         (push 1)
;         (minimize ...) ; index: 2
;         (pop 1)
;         (minimize ...) ; index: 2
;         ...
;
;     It is also possible to specify a negative index value.
;     In this case, OptiMathSAT counts backwards starting from
;     the top-most objective. e.g.: (load-objective-model -1)
;     always refers to the most recently defined objective function
;     on the stack of objectives.
;
;     When running OptiMathSAT in Lexicographic, Pareto or
;     Single-Objective mode, the appropriate optimum model is 
;     automatically loaded in the solver environment, ready for
;     inspection. At the end of a (SAT) lexicographic search, each
;     objective on the stack is associated with its own optimum
;     model which was computed along the lexicographic search.
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

;
; ENABLE MODEL GENERATION
;
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
