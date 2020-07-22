(set-logic ALL)
(declare-datatype S ( ( s1 ) ( s2 ) ( s3 ) ))

(define-fun f ((s S)) Bool (or (= s s1) (= s s2) (= s s3)))

(declare-fun b1 () Bool)
(declare-fun b2 () Bool)

(define-fun c ((x S)) Bool (or (and b1 (f x)) (and b2 (not (f x)))))

(assert (f s1))
(assert (forall ((x S)) (c x)))
(assert (distinct b1 b2))


(check-sat)
(get-model)