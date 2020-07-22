(set-logic ALL)
(set-option :uf-ho true)
(set-option :produce-models true)
(set-option :lang smt2)

; The structures from Figure 1 of the PLDI 2020 paper (left to right, top to bottom; 1-5 are +, 6-9 are -)
; here, we make two edges in structure 5 partial (controlled by p1 p2)

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

(define-fun E1 ((p1 Bool) (p2 Bool) (u V) (v V)) Bool false)

(define-fun E2 ((p1 Bool) (p2 Bool) (u V) (v V)) Bool false)

(define-fun E3c ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
    (and (= u v2) (= v v3))
))
(define-fun E3 ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or (E3c p1 p2 u v) (E3c p1 p2 v u)))

(define-fun E4c ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
    (and (= u v1) (= v v4))
    (and (= u v2) (= v v4))
    (and (= u v3) (= v v4))
))
(define-fun E4 ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or (E4c p1 p2 u v) (E4c p1 p2 v u)))

(define-fun E5c ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
    (and (= u v2) (= v v3))
    (and (= u v3) (= v v4))
    (and (= u v3) (= v v5))
    (and (= u v4) (= v v5))
    (and p1 (= u v1) (= v v4))
    (and p2 (= u v2) (= v v5))
))
(define-fun E5 ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or (E5c p1 p2 u v) (E5c p1 p2 v u)))

(define-fun E6c ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
))
(define-fun E6 ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or (E6c p1 p2 u v) (E6c p1 p2 v u)))

(define-fun E7c ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
))
(define-fun E7 ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or (E7c p1 p2 u v) (E7c p1 p2 v u)))

(define-fun E8c ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or
    (and (= u v1) (= v v3))
    (and (= u v1) (= v v4))
    (and (= u v2) (= v v4))
    (and (= u v3) (= v v4))
))
(define-fun E8 ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or (E8c p1 p2 u v) (E8c p1 p2 v u)))

(define-fun E9c ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or
    (and (= u v1) (= v v2))
    (and (= u v1) (= v v3))
    (and (= u v2) (= v v4))
    (and (= u v3) (= v v4))
))
(define-fun E9 ((p1 Bool) (p2 Bool) (u V) (v V)) Bool (or (E9c p1 p2 u v) (E9c p1 p2 v u)))

; evaluating a matrix where the prefix is forall X,Y. exists Z.
; search for a matrix with 2 CNF clauses over the literals: e(X,Y) ~e(X,Y) e(X,Z) ~e(X,Z) e(Y,Z) ~e(Y,Z)
(declare-fun x11 () Bool)
(declare-fun x12 () Bool)
(declare-fun x13 () Bool)
(declare-fun x14 () Bool)
(declare-fun x15 () Bool)
(declare-fun x16 () Bool)
(declare-fun x21 () Bool)
(declare-fun x22 () Bool)
(declare-fun x23 () Bool)
(declare-fun x24 () Bool)
(declare-fun x25 () Bool)
(declare-fun x26 () Bool)
(define-fun matrix ((p1 Bool) (p2 Bool) (U (-> V Bool)) (E (-> Bool (-> Bool (-> V (-> V Bool))))) (x V) (y V) (z V)) Bool (and
    (or (and x11 (E p1 p2 x y)) (and x12 (not (E p1 p2 x y))) (and x13 (E p1 p2 x z)) (and x14 (not (E p1 p2 x z))) (and x15 (E p1 p2 y z)) (and x16 (not (E p1 p2 y z))))
    (or (and x21 (E p1 p2 x y)) (and x22 (not (E p1 p2 x y))) (and x23 (E p1 p2 x z)) (and x24 (not (E p1 p2 x z))) (and x25 (E p1 p2 y z)) (and x26 (not (E p1 p2 y z))))
))

(define-fun eval ((p1 Bool) (p2 Bool) (U (-> V Bool)) (E (-> Bool (-> Bool (-> V (-> V Bool)))))) Bool (
    forall ((x V) (y V)) (=> (and (U x) (U y)) (exists ((z V)) (and (U z) (matrix p1 p2 U E x y z))))
))

; structures 1-5 are positive, 6-9 are negative
(assert (forall ((p1 Bool) (p2 Bool)) (eval p1 p2 V1 E1)))
(assert (forall ((p1 Bool) (p2 Bool)) (eval p1 p2 V2 E2)))
(assert (forall ((p1 Bool) (p2 Bool)) (eval p1 p2 V3 E3)))
(assert (forall ((p1 Bool) (p2 Bool)) (eval p1 p2 V4 E4)))
(assert (forall ((p1 Bool) (p2 Bool)) (eval p1 p2 V5 E5)))
(assert (forall ((p1 Bool) (p2 Bool)) (not (eval p1 p2 V6 E6))))
(assert (forall ((p1 Bool) (p2 Bool)) (not (eval p1 p2 V7 E7))))
(assert (forall ((p1 Bool) (p2 Bool)) (not (eval p1 p2 V8 E8))))
(assert (forall ((p1 Bool) (p2 Bool)) (not (eval p1 p2 V9 E9))))

(check-sat)
(get-model)
