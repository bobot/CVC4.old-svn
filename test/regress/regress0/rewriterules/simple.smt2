(set-logic LIA)
(set-info :status unsat)

;; don't use a datatypes for currently focusing in uf
(declare-sort list 0)

(declare-fun cons (Int list) list)
(declare-fun nil  ()         list)


;;define length
(declare-fun length (list) Int)

(assert (forall ((?l list)) (! (= (length nil) 0) :rewrite-rule)))

(assert (forall ((?e Int) (?l list)) (! (= (length (cons ?e ?l)) (+ (length ?l) 1)) :rewrite-rule)))

(assert (= (length (cons 1 (cons  2 (cons 3 nil)))) 3))

(check-sat)
(exit)
