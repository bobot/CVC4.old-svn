;; Same than length.smt2 but the nil case is not a rewrite rule
;; So here the rewrite rules have no guards length

(set-logic LIA)
(set-info :status unsat)

;; don't use a datatypes for currently focusing in uf
(declare-sort list 0)

(declare-fun cons (Int list) list)
(declare-fun nil  ()         list)


;;define length
(declare-fun length (list) Int)

(assert (= (length nil) 0))

(assert (forall ((?e Int) (?l list)) (= (length (cons ?e ?l)) (+ 1 (length ?l)))))

(declare-fun gen_cons (Int list) list)

(assert (forall ((?n Int) (?l list)) (=> (= ?n 0) (= (gen_cons ?n ?l) ?l))))

(assert (forall ((?n Int) (?l list)) (=> (> ?n 0) (= (gen_cons ?n ?l)
        (gen_cons (- ?n 1) (cons 1 ?l))))))


;;(assert (not (forall ((?n Int)) (=> (>= ?n 0) (=> (= (length (gen_cons ?n nil)) ?n) (= (length (gen_cons (+ ?n 1) nil)) (+ ?n 1))) ))))

;;(assert (not (forall ((?n Int) (?l list)) (=> (>= ?n 0) (=> (= (length ?l) ?n) (= (length (cons 1 ?l)) (+ ?n 1))) ))))

;;(assert (not (forall ((?n Int)) (=> (>= ?n 0) (=> (= (length (gen_cons ?n nil)) ?n) (= (length (cons 1 (gen_cons ?n nil))) (+ ?n 1))) ))))

(assert (not (forall ((?n Int)) (=> (>= ?n 0) (=>
        (forall ((?l list)) (= (gen_cons ?n (cons 1 ?l)) (cons 1 (gen_cons ?n ?l))))
        (forall ((?l list)) (= (gen_cons (+ ?n 1) (cons 1 ?l)) (cons 1 (gen_cons (+ ?n 1) ?l))))
     )))))


(check-sat)

(exit)
