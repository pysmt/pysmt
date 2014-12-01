(set-logic LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 9350 For more info see: No further information available.
|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun xuscore2dollarskuscore0 () Real)
(declare-fun t6uscore0dollarskuscore0 () Real)
(declare-fun yuscore2dollarskuscore8 () Real)
(declare-fun ts6uscore0 () Real)
(declare-fun stuscore2dollarskuscore8 () Real)
(assert (not (exists ((ts6uscore0 Real)) (=> (and (and (and (and (and (and (=> (and (<= 0 ts6uscore0) (<= ts6uscore0 t6uscore0dollarskuscore0)) (<= (+ ts6uscore0 yuscore2dollarskuscore8) 10)) (>= t6uscore0dollarskuscore0 0)) (< yuscore2dollarskuscore8 10)) (= stuscore2dollarskuscore8 0)) (>= yuscore2dollarskuscore8 1)) (<= yuscore2dollarskuscore8 12)) (<= yuscore2dollarskuscore8 (+ 10 xuscore2dollarskuscore0))) (or (= stuscore2dollarskuscore8 3) (>= (+ t6uscore0dollarskuscore0 yuscore2dollarskuscore8) 1))))))
(check-sat)
(exit)
