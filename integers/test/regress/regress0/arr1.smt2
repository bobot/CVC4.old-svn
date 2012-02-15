(set-logic QF_AX)
(set-info  :status unsat)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(assert (not (=> (= i1 i2) (= (select a i1) (select a i2)))))
(check-sat)
