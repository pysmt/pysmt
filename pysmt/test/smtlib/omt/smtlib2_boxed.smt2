; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; WARNING:
;     OptiMathSAT and real_z3 have different default behaviours
;     when multiple objectives are optimized in the same
;     formula. real_z3 handles them lexicographically, whereas
;     OptiMathSAT handles them in boxed (multi-independent) mode.
;     Therefore, the following option should be correctly
;     set on any boxed/multi-independent formula:
;
;         (set-option :opt.priority box)
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

;
; BOXED OPTIMIZATION OPTIONS
;
; -opt.box.branch_preference=BOOL
;          Prefer branching on optimization search cuts. (default: true)
; -opt.box.engine=STR
;          Configures the engine for Multiple-Independent/Boxed optimization. 
;          Possible values are:  
;          - dpll: dpll-based boxed optimization (default)
;          - full: incremental optimization, one objective at a time
;          - partial: incremental optimization, all objectives at the same time
; -opt.box.shuffle=BOOL
;          Optimize objectives in random order. (default: true)
;
