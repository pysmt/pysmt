(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 22228 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun ts24uscore0 () Real)
(declare-fun xuscore2dollarskuscore33 () Real)
(declare-fun t24uscore0dollarskuscore0 () Real)
(declare-fun stuscore2dollarskuscore41 () Real)
(declare-fun yuscore2dollarskuscore41 () Real)
(assert (not (exists ((ts24uscore0 Real)) (=> (and (and (and (and (and (and (and (=> (and (<= 0 ts24uscore0) (<= ts24uscore0 t24uscore0dollarskuscore0)) (<= (+ ts24uscore0 yuscore2dollarskuscore41) 10)) (>= t24uscore0dollarskuscore0 0)) (< yuscore2dollarskuscore41 10)) (= stuscore2dollarskuscore41 0)) (>= yuscore2dollarskuscore41 1)) (<= yuscore2dollarskuscore41 12)) (>= yuscore2dollarskuscore41 (- 5 (* 2 xuscore2dollarskuscore33)))) (<= yuscore2dollarskuscore41 (+ 10 xuscore2dollarskuscore33))) (>= (+ t24uscore0dollarskuscore0 yuscore2dollarskuscore41) 1)))))
(check-sat)
(exit)
