; -*- SMT2 -*-
;
; Author: Patrick Trentin <patrick.trentin@unitn.it>
;
; This file is part of OptiMathSAT.
;
; BITVECTOR OPTIMIZATION:
;     Both OptiMathSAT and Z3 support Bit-Vector optimization.
;     OptiMathSAT allows the user to specify whether a BV
;     objective is intended as signed or not by means of
;     an additional (optional) parameter ':signed', e.g.
;
;         (minimize <bv_term> :signed)
;         (maximize <bv_term>)
;
;     When ':signed' is not specified, OptiMathSAT interprets
;     the BV goal as an unsigned term.
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
(declare-fun bv_8 () (_ BitVec 8))
(assert (or
    (and (bvsle ((_ to_bv 8) 120) bv_8)
         (bvsle bv_8 ((_ to_bv 8) 120))
    )
    (and (bvsle ((_ to_bv 8) 97) bv_8)
         (bvsle bv_8 ((_ to_bv 8) 97))
    )
    (and (bvsle ((_ to_bv 8) 54) bv_8)
         (bvsle bv_8 ((_ to_bv 8) 54))
    )
    (and (bvsle ((_ to_bv 8) 32) bv_8)
         (bvsle bv_8 ((_ to_bv 8) 32))
    )
    (and (bvsle ((_ to_bv 8) 22) bv_8)
         (bvsle bv_8 ((_ to_bv 8) 22))
    )
    (and (bvsle ((_ to_bv 8) 11) bv_8)
         (bvsle bv_8 ((_ to_bv 8) 11))
    )
    (and (bvsle ((_ to_bv 8) 8) bv_8)
         (bvsle bv_8 ((_ to_bv 8) 8))
    )
    (and (bvsle ((_ to_bv 8) (- 7)) bv_8)
         (bvsle bv_8 ((_ to_bv 8) (- 7)))
    )
    (and (bvsle ((_ to_bv 8) (- 16)) bv_8)
         (bvsle bv_8 ((_ to_bv 8) (- 16)))
    )
    (and (bvsle ((_ to_bv 8) (- 105)) bv_8)
         (bvsle bv_8 ((_ to_bv 8) (- 105)))
    )
))

;
; GOALS
;
(minimize bv_8)
(minimize bv_8 :signed)

;
; OPTIMIZATION + OPTIMUM VALUES
;
(check-sat)
(get-objectives)

(exit)

; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;

;
; BITVECTOR OPTIMIZATION OPTIONS
;
; -theory.bv.eager=BOOL
;          If true, BV atoms will be bit-blasted into the main DPLL solver.
; -opt.theory.bv.engine=STR
;          Sets the solving engine for dealing BitVector objectives:
;           - omt   : standard OMT techniques
;           - obvwa : bit-vector optimization with weak assumptions
;           - obvbs : bit-vector optimization with binary search (default)
; -opt.theory.bv.branch_preference=BOOL
;          If true, it sets a branching preference on the BV objective. 
;          (default: true) 
; -opt.theory.bv.polarity=BOOL
;          If true, sets the initial polarity of any BV objective towards the 
;          maximum gain direction. (default: true) 
;
