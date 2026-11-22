(set-option :produce-models true)

(declare-fun n1 () Bool)
(declare-fun n2 () Bool)
(declare-fun n3 () Bool)
(declare-fun n4 () Bool)

(assert (or (not n2) (not n3)))

(assert-soft n1)
(assert-soft n2)
(assert-soft n3)
(assert-soft n4)

(check-sat)
(get-objectives)
(get-model)
(exit)
