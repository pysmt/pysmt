; -*- SMT2 -*-
;
; This file comes from the optimathsat distribution with the permission of the authors.


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
