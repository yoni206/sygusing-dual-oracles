(set-logic ALL)

(declare-sort S 0)


(define-fun pre ( (u (-> S Bool))) Bool (and  (forall ((x S)) (not (u x)))))



(declare-const u (-> S Bool))
(declare-const x S)

(assert (and (pre u) (not  (u x))))
(check-sat)
(get-model)
