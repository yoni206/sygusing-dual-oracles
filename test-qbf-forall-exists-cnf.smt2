(set-logic ALL)
(set-option :produce-models true)

; (declare-fun x11 () Bool)
; (declare-fun x12 () Bool)
; (declare-fun x13 () Bool)
; (declare-fun x14 () Bool)

; (assert (= x11 false))
; (assert (= x12 false))
; (assert (= x13 false))
; (assert (= x14 true))


; (declare-const s1 Bool) 
; (declare-const s2 Bool) 
; (declare-const new_s1 Bool) 
; (declare-const new_s2 Bool) 
; (declare-const cti Bool) 
; (declare-const inv_pre1 Bool)
; (declare-const inv_pre2 Bool)
; (declare-const inv_post1 Bool)
; (declare-const inv_post2 Bool)



(assert
(forall ((x11 Bool) (x12 Bool) (x13 Bool) (x14 Bool))
(exists (
(s1 Bool) 
(s2 Bool) 
(new_s1 Bool) 
(new_s2 Bool) 
(cti Bool) 
(inv_pre1 Bool)
(inv_pre2 Bool)
(inv_post1 Bool)
(inv_post2 Bool)
)
(and
  ;tseitin
  (or (not inv_pre1) (not s1))
  (or inv_pre1 s1)
  (or (not inv_post1) (not new_s1))
  (or inv_post1 new_s1)
  (or (not s1) (not x11) inv_pre2)
  (or s1 (not x12) inv_pre2)
  (or (not s2) (not x13) inv_pre2)
  (or s2 (not x14) inv_pre2)
  (or s1 s2 x12 x14 (not inv_pre2))
  (or s1 (not s2) x12 x13 (not inv_pre2))
  (or (not s1) s2 x11 x14 (not inv_pre2))
  (or (not s1) (not s2) x11 x13 (not inv_pre2))
  (or (not new_s1) (not x11) inv_post2)
  (or new_s1 (not x12) inv_post2)
  (or (not new_s2) (not x13) inv_post2)
  (or new_s2 (not x14) inv_post2)
  (or new_s1 new_s2 x12 x14 (not inv_post2))
  (or new_s1 (not new_s2) x12 x13 (not inv_post2))
  (or (not new_s1) new_s2 x11 x14 (not inv_post2))
  (or (not new_s1) (not new_s2) x11 x13 (not inv_post2))
  (or (not new_s1) s1 s2 )
  (or new_s1 (not s1) )
  (or new_s1 (not s2) )
  (or (not new_s2) s2 )
  (or new_s2 (not s2) )
  (or cti (not x12))
  (or cti (not x14))
  (or (not cti) inv_pre1)
  (or (not cti) inv_pre2)
  (or (not cti) (not inv_post1) (not inv_post2))
))))



(check-sat)
(get-model)