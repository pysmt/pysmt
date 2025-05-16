(set-option :produce-models true)

(declare-fun n1 () Int)
(declare-fun n2 () Int)
(declare-fun n3 () Int)
(declare-fun n4 () Int)

(assert (>= n1 0))
(assert (<= n1 1))
(assert (>= n2 0))
(assert (<= n2 1))
(assert (>= n3 0))
(assert (<= n3 1))
(assert (>= n4 0))
(assert (<= n4 1))

(assert (<= (+ n2 n3) 1))

(assert-soft (= n1 1))
(assert-soft (= n2 1))
(assert-soft (= n3 1))
(assert-soft (= n4 1))

(check-sat)
(get-objectives)
(get-model)
(exit)
