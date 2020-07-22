(set-logic ALL)
(set-option :uf-ho true)

; The structures from Figure 1 of the PLDI 2020 paper (left to right, top to bottom; 1-5 are +, 6-9 are -)

; same datatype for vertices of all structures,
; unary relations for universes of each structure,
; binary relations for edges in each structure.

(declare-datatype V ((v1) (v2) (v3) (v4) (v5)))

(define-fun V1 ((v V)) Bool (= v v1))
(define-fun V2 ((v V)) Bool (or (= v v1) (= v v2)))
(define-fun V3 ((v V)) Bool (or (= v v1) (= v v2) (= v v3)))
(define-fun V4 ((v V)) Bool (or (= v v1) (= v v2) (= v v3) (= v v4)))
(define-fun V5 ((v V)) Bool (or (= v v1) (= v v2) (= v v3) (= v v4) (= v v5)))
(define-fun V6 ((v V)) Bool (or (= v v1) (= v v2)))
(define-fun V7 ((v V)) Bool (or (= v v1) (= v v2) (= v v3)))
(define-fun V8 ((v V)) Bool (or (= v v1) (= v v2) (= v v3) (= v v4)))
(define-fun V9 ((v V)) Bool (or (= v v1) (= v v2) (= v v3) (= v v4)))

(define-fun E1 ((u V) (v V)) Bool false)

(define-fun E2 ((u V) (v V)) Bool false)

(define-fun E3c ((u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
    (and (= u v2) (= v v3))
))
(define-fun E3 ((u V) (v V)) Bool (or (E3c u v) (E3c v u)))

(define-fun E4c ((u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
    (and (= u v1) (= v v4))
    (and (= u v2) (= v v4))
    (and (= u v3) (= v v4))
))
(define-fun E4 ((u V) (v V)) Bool (or (E4c u v) (E4c v u)))

(define-fun E5c ((u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
    (and (= u v2) (= v v3))
    (and (= u v3) (= v v4))
    (and (= u v3) (= v v5))
    (and (= u v4) (= v v5))
))
(define-fun E5 ((u V) (v V)) Bool (or (E5c u v) (E5c v u)))

(define-fun E6c ((u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
))
(define-fun E6 ((u V) (v V)) Bool (or (E6c u v) (E6c v u)))

(define-fun E7c ((u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
))
(define-fun E7 ((u V) (v V)) Bool (or (E7c u v) (E7c v u)))

(define-fun E8c ((u V) (v V)) Bool (or
    (and (= u v1) (= v v3))
    (and (= u v1) (= v v4))
    (and (= u v2) (= v v4))
    (and (= u v3) (= v v4))
))
(define-fun E8 ((u V) (v V)) Bool (or (E8c u v) (E8c v u)))

(define-fun E9c ((u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
    (and (= u v2) (= v v4))
    (and (= u v3) (= v v4))
))
(define-fun E9 ((u V) (v V)) Bool (or (E9c u v) (E9c v u)))

; evaluating a matrix where the prefix is forall X,Y. exists Z.

(define-fun matrix ((U (-> V Bool)) (E (-> V (-> V Bool))) (x V) (y V) (z V)) Bool 
            (=> (E x y) (and (E x z) (E y z)))
)

(define-fun eval ((U (-> V Bool)) (E (-> V (-> V Bool)))) Bool (
    forall ((x V) (y V)) (=> (and (U x) (U y)) (exists ((z V)) (and (U z) (matrix U E x y z))))
))

; structures 1-5 are positive, 6-9 are negative
(assert (or 
  (not (eval V1 E1))
  (not (eval V2 E2))
  (not (eval V3 E3))
  (not (eval V4 E4))
  (not (eval V5 E5))
  (not (not (eval V6 E6)))
  (not (not (eval V7 E7)))
  (not (not (eval V8 E8)))
  (not (not (eval V9 E9)))))

(check-sat)
