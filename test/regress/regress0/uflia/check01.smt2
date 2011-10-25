(set-logic QF_UFLIA)
(set-info :smt-lib-version 2.0)
(set-info :status sat)

(declare-fun f (Int) Bool)

(assert (f 0))

(push 1)
(assert (not (f 0)))
(pop 1)
(check-sat)
