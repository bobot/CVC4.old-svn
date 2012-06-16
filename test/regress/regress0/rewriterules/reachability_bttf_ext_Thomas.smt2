;; Back to the Future ... Shuvendu K.Lhiri, Shaz Qadeer
(set-logic AUFLIA)
(set-info :status unsat)

(declare-sort elt 0)

(declare-fun f (elt) elt)
(declare-fun Rf (elt elt elt) Bool)

(declare-fun hack (elt) Bool)


;;eq
(assert-propagation ((?x elt)) () () (or (= ?x ?x) (not (= ?x ?x))) (((hack ?x))) )
;; reflexive
(assert-propagation ((?x elt)) () () (Rf ?x ?x ?x) (((hack ?x))) )
;; step
(assert-propagation ((?x elt)) () () (Rf ?x (f ?x) (f ?x)) (((f ?x))) )

;; reach
(assert-propagation ((?x1 elt)(?x2 elt)) () ((Rf ?x1 ?x2 ?x2)) (or (= ?x1 ?x2) (Rf ?x1 (f ?x1) ?x2)) (((f ?x1))) )
;; reach extended
(assert-propagation ((?x1 elt)(?x2 elt)) ((not (= ?x1 ?x2))(Rf ?x1 ?x2 ?x2)) () (Rf ?x1 (f ?x1) ?x2) (((Rf ?x1 (f ?x1) ?x2))) )
;; reach extended
(assert-propagation ((?x1 elt)(?x2 elt)) ((not (Rf ?x1 (f ?x1) ?x2))(Rf ?x1 ?x2 ?x2)) () (= ?x1 ?x2) (((Rf ?x1 (f ?x1) ?x2))) )

;; cycle
(assert-propagation ((?x1 elt)(?x2 elt)) () ((= (f ?x1) ?x1) (Rf ?x1 ?x2 ?x2)) (= ?x1 ?x2) () )
;; sandwich
(assert-propagation ((?x1 elt)(?x2 elt)) () ((Rf ?x1 ?x2 ?x1)) (= ?x1 ?x2) () )
;; order1
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))
                    (or (Rf ?x1 ?x2 ?x3) (Rf ?x1 ?x3 ?x2)) () )
;; order1 extended
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
                    (Rf ?x1 ?x2 ?x3) (((Rf ?x1 ?x2 ?x3))) )
;; order1 extended
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
                    (Rf ?x1 ?x3 ?x2) (((Rf ?x1 ?x3 ?x2))) )

;; order2
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x1 ?x2 ?x3))
                    (and (Rf ?x1 ?x2 ?x2) (Rf ?x2 ?x3 ?x3)) () )
;; transitive1
(assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x1 ?x2 ?x2)(Rf ?x2 ?x3 ?x3))
                    (Rf ?x1 ?x3 ?x3) () )
;; transitive2
(assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x0 ?x1 ?x2)(Rf ?x1 ?x3 ?x2))
                    (and (Rf ?x0 ?x1 ?x3) (Rf ?x0 ?x3 ?x2)) () )
;;transitive3
(assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x0 ?x1 ?x2)(Rf ?x0 ?x3 ?x1))
                    (and (Rf ?x0 ?x3 ?x2) (Rf ?x3 ?x1 ?x2)) () )

(declare-fun e1 () elt)
(declare-fun e2 () elt)
(declare-fun e3 () elt)
(declare-fun e4 () elt)


(assert (and (hack e1) (hack e2) (hack e3) (hack e4) (hack (f e2))))


;;Example0
;;(assert (not (=> (and (not (= e1 e2)) (Rf e1 e2 e3)) (Rf e1 (f e1) e3))) )

;;Thomas' example1 x,e1 y,e2 z,e3 y',e4
;;(assert (not (=> (and (Rf e1 e2 e3) (not (= e2 e3)) (= e4 (f e2))) (Rf e1 e4 e3))))

(declare-fun Rf_avoid (elt elt elt) Bool)

(assert-rewrite ((?x0 elt)(?x1 elt)(?exc elt)) () (Rf_avoid ?x0 ?x1 ?exc)
                 (or (Rf ?x0 ?x1 ?exc) (and (Rf ?x0 ?x1 ?x1) (not (Rf ?x0 ?exc ?exc)))) () )

(declare-fun null () elt)
(assert (= (f null) null))

(declare-fun join (elt elt) elt)

(assert-propagation ((?x elt)(?y elt)(?z elt)) () ((Rf ?x ?z ?z)(Rf ?y ?z ?z)) (Rf ?x (join ?x ?y) ?z) () )
(assert-propagation ((?x elt)(?y elt)) () () (or (and (Rf ?x (join ?x ?y) (join ?x ?y)) (Rf ?y (join ?x ?y) (join ?x ?y))) (= (join ?x ?y) null))  (((join ?x ?y))) )

;;Thomas' example2
(assert (not (=> (and (Rf e1 null null) (= (join e1 e2) null)
;; (next' == upd(next, e, e1)
)
;; (reach(next', e1, null) )
(or (and (Rf e1 null null) (Rf_avoid e1 null e2) )
    (and (not (= e2 null)) (Rf_avoid e1 e2 null) (Rf e1 null e2) (Rf_avoid e1 null e2) )
    (and (not (= e2 null)) (Rf_avoid e1 e2 null) (Rf e1 null null) (Rf_avoid e1 null e2) ) )
)))

(check-sat)
(exit)