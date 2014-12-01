(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 24658 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun xuscore2dollarskuscore45 () Real)
(declare-fun ts27uscore3 () Real)
(declare-fun t27uscore0dollarskuscore3 () Real)
(declare-fun stuscore2dollarskuscore53 () Real)
(declare-fun yuscore2dollarskuscore53 () Real)
(assert (not (exists ((ts27uscore3 Real)) (=> (and (and (and (and (and (and (and (and (= stuscore2dollarskuscore53 1) (=> (and (<= 0 ts27uscore3) (<= ts27uscore3 t27uscore0dollarskuscore3)) (>= (+ (* (- 2) ts27uscore3) yuscore2dollarskuscore53) 5))) (>= t27uscore0dollarskuscore3 0)) (> yuscore2dollarskuscore53 5)) (= stuscore2dollarskuscore53 2)) (>= yuscore2dollarskuscore53 1)) (<= yuscore2dollarskuscore53 12)) (>= yuscore2dollarskuscore53 (- 5 (* 2 xuscore2dollarskuscore45)))) (<= yuscore2dollarskuscore53 (+ 10 xuscore2dollarskuscore45))) (<= (+ (* (- 2) t27uscore0dollarskuscore3) yuscore2dollarskuscore53) (+ 10 (+ t27uscore0dollarskuscore3 xuscore2dollarskuscore45)))))))
(check-sat)
(exit)
