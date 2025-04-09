; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; PARETO OPTIMIZATION:
;     Both OptiMathSAT and Z3 support pareto optimization,
;     with some differences:
;     - OptiMathSAT accepts either 'pareto' or 'par' as values
;     of 'opt.priority' option when configuring the pareto
;     optimization. Z3 only accepts the former value.
;     - OptiMathSAT can perform an optional preliminary
;     unboundedness test on the objective functions before
;     running the Pareto-front algorithm. This can be useful
;     because in the large majority of cases the currently implemented
;     Pareto-front algorithm is not able to converge at any solution
;     when some objective function is unbounded. This might not be
;     the case when multiple-objectives are defined on the same
;     variable(s). Model generation is required by OptiMathSAT
;     in order to perform Pareto optimization.
;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

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

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

;
; PARETO OPTIMIZATION OPTIONS
;     The 'incremental' mode reassembles the new Z3 pareto optimization
;     search, whereas 'callback' mode reassembles the old Z3 pareto
;     optimization search. The first requires multiple '(check-sat)' calls
;     in order to explore the Pareto-front, whereas the latter attempts to
;     print all Pareto-front solutions for each '(check-sat)', possibly
;     non terminating if there are infinitely many.
;
; -opt.par.engine=STR
;          Configures the engine for Pareto optimization. Possible values are:
;           - gia: Guided Improvement Algorithm
;           - lex: based on Lexicographic Optimization (default)
; -opt.par.mode=STR
;          Configures the type of Pareto search. Possible values are:
;           - incremental: return only one (if any) new Pareto solution for
;                 each satisfiability check. When all solutions have been
;                 explored, returns UNSAT and no solution. Subsequent
;                 checks restart the search. (default)
;           - callback: explore all Pareto solutions within a single
;                 satisfiability check. If the API is used, a callback
;                 function must be set to explore each new model.
; -opt.par.print_model=BOOL
;          If true, when the Pareto search is executed in 'callback' mode the
;          solver prints the complete model of each pareto solution instead of
;          printing only the value of the objective functions. (default: true)
;
