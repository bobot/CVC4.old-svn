; same as bug421.smt2 but adds --check-models on command line:
; this actually caused the same bug for a different reason, so
; we check them both independently in regressions
;
; COMMAND-LINE: --incremental --abstract-values --check-models
; EXPECT: sat
; EXPECT: ((a @1) (b @2))
; EXIT: 10
(set-logic QF_AUFLIA)
(set-option :produce-models true)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (not (= a b)))
(check-sat)
(get-value (a b))
