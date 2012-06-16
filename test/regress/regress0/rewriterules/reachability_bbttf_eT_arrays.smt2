;; Back to the Future ... Shuvendu K.Lhiri, Shaz Qadeer
(set-logic AUFLIA)
(set-info :status unsat)

(declare-sort elt 0)
(define-sort mem () (Array elt elt))

(declare-fun R (mem elt elt elt) Bool)

;; reflexive
(assert-propagation ((?m mem)(?x elt)) () () (R ?m ?x ?x ?x) ((?m ?x)) )
;; step
(assert-propagation ((?m mem)(?x elt)) () () (R ?m ?x (select ?m ?x) (select ?m ?x)) (((select ?m ?x))) )
;; (assert-propagation ((?x elt)) () () (Rf ?x (f ?x) (f ?x)) (((Rf ?x (f ?x) (f ?x)))) )
;; (assert-propagation ((?x elt)) () () (=> true (Rf ?x (f ?x) (f ?x))) (((f ?x))) )

;; reach
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)) () ((R ?m ?x1 ?x2 ?x2)) (or (= ?x1 ?x2) (R ?m ?x1 (select ?m ?x1) ?x2)) (((select ?m ?x1))) )
;; ;; reach extended
;; (assert-propagation ((?x1 elt)(?x2 elt)) ((not (= ?x1 ?x2))(Rf ?x1 ?x2 ?x2)) () (Rf ?x1 (f ?x1) ?x2) (((Rf ?x1 (f ?x1) ?x2))) )
;; ;; reach extended
;; (assert-propagation ((?x1 elt)(?x2 elt)) ((not (Rf ?x1 (f ?x1) ?x2))(Rf ?x1 ?x2 ?x2)) () (= ?x1 ?x2) (((Rf ?x1 (f ?x1) ?x2))) )

;; cycle
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)) ((= (select ?m ?x1) ?x1)) ((R ?m ?x1 ?x2 ?x2)) (= ?x1 ?x2) (((select ?m ?x1))) )
;; (assert-propagation ((?x1 elt)(?x2 elt)) ((= (f ?x1) ?x1)) ((Rf ?x1 ?x2 ?x2)) (= ?x1 ?x2) () )

;; (assert-propagation ((?x1 elt)(?x2 elt)) () () (=> (and (= (f ?x1) ?x1) (Rf ?x1 ?x2 ?x2)) (= ?x1 ?x2)) (((Rf ?x1 ?x2 ?x2)(f ?x1))) )

;; sandwich
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)) () ((R ?m ?x1 ?x2 ?x1)) (= ?x1 ?x2) () )
;; (assert-propagation ((?x1 elt)(?x2 elt)) () () (=> (Rf ?x1 ?x2 ?x1) (= ?x1 ?x2)) (((Rf ?x1 ?x2 ?x1))) )

;; order1
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)(?x3 elt)) ()
                    ((R ?m ?x1 ?x2 ?x2)(R ?m ?x1 ?x3 ?x3)) (or (R ?m ?x1 ?x2 ?x3) (R ?m ?x1 ?x3 ?x2)) () )

;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ()
;;                     (=> (and (Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)) (or (Rf ?x1 ?x2 ?x3) (Rf ?x1 ?x3 ?x2))) (((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))) )

;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
;;                     (Rf ?x1 ?x2 ?x3) (((Rf ?x1 ?x2 ?x3))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
;;                     (Rf ?x1 ?x3 ?x2) (((Rf ?x1 ?x3 ?x2))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
;;                     (Rf ?x1 ?x2 ?x3) (((Rf ?x1 ?x3 ?x2))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
;;                     (Rf ?x1 ?x3 ?x2) (((Rf ?x1 ?x2 ?x3))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x3 ?x2))) ()
;;                     (Rf ?x1 ?x2 ?x3) (((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))) )
;; ;; order1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) ((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3)(not (Rf ?x1 ?x2 ?x3))) ()
;;                     (Rf ?x1 ?x3 ?x2) (((Rf ?x1 ?x2 ?x2)(Rf ?x1 ?x3 ?x3))) )

;; order2
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)(?x3 elt)) () ((R ?m ?x1 ?x2 ?x3))
                    (and (R ?m ?x1 ?x2 ?x2) (R ?m ?x2 ?x3 ?x3)) () )
;; transitive1
(assert-propagation ((?m mem)(?x1 elt)(?x2 elt)(?x3 elt)) () ((R ?m ?x1 ?x2 ?x2)(R ?m ?x2 ?x3 ?x3))
                    (R ?m ?x1 ?x3 ?x3) () )
;; ;; transitive1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ((not (Rf ?x1 ?x3 ?x3))(Rf ?x2 ?x3 ?x3))
;;                     (not (Rf ?x1 ?x2 ?x2)) () )
;; ;; transitive1 extended
;; (assert-propagation ((?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x1 ?x2 ?x2)(not (Rf ?x1 ?x3 ?x3)))
;;                     (not (Rf ?x2 ?x3 ?x3)) () )

;;transitive2
(assert-propagation ((?m mem)(?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((R ?m ?x0 ?x1 ?x2)(R ?m ?x1 ?x3 ?x2))
                    (and (R ?m ?x0 ?x1 ?x3) (R ?m ?x0 ?x3 ?x2)) () )

;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ()
;;                     (=> (and (Rf ?x0 ?x1 ?x2)(Rf ?x1 ?x3 ?x2))
;;                         (and (Rf ?x0 ?x1 ?x3) (Rf ?x0 ?x3 ?x2)))
;;                     (((Rf ?x0 ?x1 ?x2)(Rf ?x1 ?x3 ?x2))) )

;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((not (Rf ?x0 ?x1 ?x3))(Rf ?x1 ?x3 ?x2))
;;                     (not (Rf ?x0 ?x1 ?x2)) (((Rf ?x0 ?x1 ?x2))) )
;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x0 ?x1 ?x2)(not (Rf ?x0 ?x1 ?x3)))
;;                     (not (Rf ?x1 ?x3 ?x2)) (((Rf ?x1 ?x3 ?x2))) )
;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((not (Rf ?x0 ?x3 ?x2))(Rf ?x1 ?x3 ?x2))
;;                     (not (Rf ?x0 ?x1 ?x2)) (((Rf ?x0 ?x1 ?x2))) )
;; ;; transitive2 extended
;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((Rf ?x0 ?x1 ?x2)(not (Rf ?x0 ?x3 ?x2)))
;;                     (not (Rf ?x1 ?x3 ?x2)) (((Rf ?x1 ?x3 ?x2))) )

;; ;;transitive3
(assert-propagation ((?m mem)(?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ((R ?m ?x0 ?x1 ?x2)(R ?m ?x0 ?x3 ?x1))
                    (and (R ?m ?x0 ?x3 ?x2) (R ?m ?x3 ?x1 ?x2)) () )

;; (assert-propagation ((?x0 elt)(?x1 elt)(?x2 elt)(?x3 elt)) () ()
;;                     (=> (and (Rf ?x0 ?x1 ?x2)(Rf ?x0 ?x3 ?x1))
;;                         (and (Rf ?x0 ?x3 ?x2) (Rf ?x3 ?x1 ?x2))) (((Rf ?x0 ?x1 ?x2)(Rf ?x0 ?x3 ?x1))) )


(declare-fun next () mem)

(declare-fun e1 () elt)
(declare-fun e2 () elt)
(declare-fun e3 () elt)
(declare-fun e4 () elt)


;;Example0
;;(assert (not (=> (and (not (= e1 e2)) (Rf e1 e2 e3)) (Rf e1 (f e1) e3))) )

;;Thomas' example1 x,e1 y,e2 z,e3 y',e4
;;(assert (not (=> (and (Rf e1 e2 e3) (not (= e2 e3)) (= e4 (f e2))) (Rf e1 e4 e3))))

(declare-fun R_avoid (mem elt elt elt) Bool)

(assert-rewrite ((?m mem)(?x0 elt)(?x1 elt)(?exc elt)) () (R_avoid ?m ?x0 ?x1 ?exc)
                 (or (R ?m ?x0 ?x1 ?exc) (and (R ?m ?x0 ?x1 ?x1) (not (R ?m ?x0 ?exc ?exc)))) () )

(assert-rewrite ((?p elt)(?q elt)(?u elt)(?v elt)(?w elt)(?m mem)) () (R (store ?m ?p ?q) ?u ?v ?w)
                (or (and (R ?m ?u ?v ?w) (R_avoid ?m ?u ?w ?p) )
                    (and (not (= ?p ?w)) (R_avoid ?m ?u ?p ?w) (R ?m ?u ?v ?p) (R_avoid ?m ?q ?w ?p) )
                    (and (not (= ?p ?w)) (R_avoid ?m ?u ?p ?w) (R ?m ?q ?v ?w) (R_avoid ?m ?q ?w ?p) ) )
                ()
)



(declare-fun join (mem elt elt) elt)

(declare-fun null () elt)
(assert (= (select next null) null))

(assert-propagation ((?m mem)(?x elt)(?y elt)(?z elt)) () ((R ?m ?x ?z ?z)(R ?m ?y ?z ?z)) (R ?m ?x (join ?m ?x ?y) ?z) (((join ?m ?x ?y))) )
(assert-propagation ((?m mem)(?x elt)(?y elt)) () () (or (and (R ?m ?x (join ?m ?x ?y) (join ?m ?x ?y)) (R ?m ?y (join ?m ?x ?y) (join ?m ?x ?y))) (= (join ?m ?x ?y) null))  (((join ?m ?x ?y))) )


(declare-fun next2 () mem)

;;Thomas' example2
(assert (not (=>
              (and (R next e1 null null)
                   (= (join next e1 e2) null)
                   (= next2 (store next e2 e1))
                   )
              (R next2 e1 null null)
              )
             )
        )

;;Thomas' example3
;; join(next, first, e) == null &&
;; reach(next, e, null) &&
;; e != null &&
;; next' == upd(next, e, first) &&
;; first' == e &&
;; e' == sel (next, e)
;; ==>
;; join(next', first', e') == null 


;; ;;Thomas' example3
;; (assert(not
;;         (=>
;;          (and
;;           ;; (= (join e1 e2) null)
;;           (Rf e2 null null)
;;           (not (= e2 null)))
;;          ;; (next' == upd(next, e2, e1)
;;          ;;join(next',e1,e2) == null
;; (or (and (not (Rf (f e2) e2 e2)) (not (Rf e1 e2 e2) ))
;; ;;    (and (Rf (f e2) e2 e2) (not (Rf e1 e1 e1) ))
;;     (and (Rf e1 e2 e2) (not (Rf (f e2) e1 e1)) )
;; )
;; ;; (or
;; ;;  (and (not (Rf e1 e2 e2)) (not (Rf e2 e2 e2)))
;; ;;  (and (Rf e1 e2 e2) (not (Rf e2 e1 e1)))
;; ;;  (and (Rf e2 e2 e2) (not (Rf e1 e1 e1)))
;; ;; )
;; )))



;; ;;Thomas' example wrong sat?
;; (assert (not (=> (and
;;                   (= (join e1 e2) null)
;;                   (Rf e2 null null) (not (= e2 null)))
;; ;; (next' == upd(next, e2, e1)
;; ;;join(next',e1,e2) == null
;; (not (Rf e2 e2 e2))
;; ;; (or
;; ;;  (and (not (Rf e1 e2 e2)) (not (Rf e2 e2 e2)))
;; ;;  (and (Rf e1 e2 e2) (not (Rf e2 e1 e1)))
;; ;;  (and (Rf e2 e2 e2) (not (Rf e1 e1 e1)))
;; ;; )
;; )))

;; ;;example4
;; (assert (not (=> (and
;;                   (= (join e1 e2) null)
;;                   (Rf e2 null null) (not (= e2 null))
;;                   )
;; (not (Rf e2 e2 e2))
;; )))


;; ;;example5
;; (assert (and
;;          ;; (= (join e1 e2) null)
;;          (= (f (f e1)) e1)
;;          (Rf e1 e2 e2)
;;          (not (= e2 e1))
;;          (not (= e2 (f e1)))
;;          )
;; )




(check-sat)
(exit)

