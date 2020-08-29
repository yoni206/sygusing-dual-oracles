(set-logic QF_UF)
(declare-fun v_1 () Bool)
(declare-fun v_2 () Bool)
(declare-fun v_3 () Bool)
(declare-fun v_4 () Bool)
(assert (or v_1 v_2 (not v_3)))
(assert (or (not v_1) (not v_2) v_3))
(assert (or v_2 v_3 (not v_4)))
(assert (or (not v_2) (not v_3) v_4))
(assert (or (not v_1) (not v_3) (not v_4)))
(assert (or v_1 v_3 v_4))
(assert (or (not v_1) v_2 v_4))
(assert (or v_1 (not v_2) (not v_4)))
(check-sat)
