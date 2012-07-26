
(set-logic QF_AUFLIA)
(set-info :smt-lib-version 2.0)
(set-info :category "unknown")
(set-info :status unknown)
(declare-datatypes () ((nat (succ (pred nat)) (zero))))
(assert (not (= (pred zero) zero)))
(check-sat)
