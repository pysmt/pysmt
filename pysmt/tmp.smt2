(declare-fun f (Int Int) Int)
(declare-fun g (Int) Int)
(declare-fun h (Int) Int)
(declare-const i1 Int)
(declare-const i2 Int)
(declare-const i3 Int)
(declare-const i4 Int)

(assert (= (h (g i1)) (g i1)))
(assert(= (h i2) (g i3)))


(check-sat)
