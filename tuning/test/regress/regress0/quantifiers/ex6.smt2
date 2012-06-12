(set-logic AUFLIRA)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun S (U) U)
(declare-fun G (U U) Bool)
(assert (and (forall ((x U)) (G (S x) x)) (forall ((x U) (y U) (z U)) (=> (and (G x y) (G y z)) (G x z))) (not (G (S (S a)) a))))
(check-sat)
(exit)
