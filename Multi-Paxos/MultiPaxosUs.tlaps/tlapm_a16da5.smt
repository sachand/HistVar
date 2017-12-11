;; Proof obligation:
;;ASSUME NEW CONSTANT Acceptors,
;;        NEW CONSTANT Values,
;;        NEW CONSTANT Quorums,
;;        NEW CONSTANT Proposers,
;;        NEW VARIABLE sent,
;;        sent
;;        \in SUBSET ([type : {"1a"}, bal : Nat, from : Proposers]
;;                    \cup [type : {"1b"}, bal : Nat,
;;                          voted : SUBSET [bal : Nat, slot : Nat, val : Values],
;;                          from : Acceptors]
;;                    \cup [type : {"2a"}, bal : Nat,
;;                          decrees : SUBSET [slot : Nat, val : Values],
;;                          from : Proposers]
;;                    \cup [type : {"2b"}, bal : Nat, slot : Nat, val : Values,
;;                          from : Acceptors])
;;        /\ MsgInv ,
;;        Next \/ ?h4fd5f73954dc53af536c1c75068837 = vars ,
;;        NEW CONSTANT p \in Proposers,
;;        NEW CONSTANT m \in ?sent#prime,
;;        NEW CONSTANT b \in Nat,
;;        NEW CONSTANT Q \in Quorums,
;;        NEW CONSTANT S \in SUBSET sent,
;;        /\ ~(\E m2 \in sent : m2.type = "2a" /\ m2.bal = b)
;;        /\ S \in SUBSET {m2 \in sent : m2.type = "1b" /\ m2.bal = b}
;;        /\ \A a \in Q : \E m2 \in S : m2.from = a
;;        /\ Send({[type |-> "2a", bal |-> b, from |-> p,
;;                  decrees |-> ProposeDecrees(UNION {m_1.voted :
;;                                                      m_1
;;                                                      \in {m_1 \in S :
;;                                                             m_1.from \in Q}})]}) ,
;;        m.type = "2a" ,
;;        NEW CONSTANT d \in {t \in
;;                              UNION {m_1.voted :
;;                                       m_1 \in {m_1 \in S : m_1.from \in Q}} :
;;                              \A t1
;;                                 \in UNION {m_1.voted :
;;                                              m_1
;;                                              \in {m_1 \in S : m_1.from \in Q}} :
;;                                 t1.slot = t.slot => t1.bal =< t.bal},
;;        NEW CONSTANT b2 \in Nat,
;;        b2 \in 0..b - 1 
;; PROVE  \A d2 \in UNION {m_1.voted : m_1 \in {m_1 \in S : m_1.from \in Q}} :
;;           ~(~d2.bal =< d.bal /\ d2.slot = d.slot)
(set-logic AUFNIRA)
(declare-sort str 0)
(declare-sort tla_Field 0)
(declare-sort u 0)
;; Declaration of terms, predicates and strings
(declare-fun Acceptors () u)
(declare-fun MsgInv () u)
(declare-fun Next () u)
(declare-fun ProposeDecrees (u) u)
(declare-fun Proposers () u)
(declare-fun Q () u)
(declare-fun Quorums () u)
(declare-fun S () u)
(declare-fun Send (u) u)
(declare-fun Values () u)
(declare-fun a__15 () u)
(declare-fun a_aunde_unde_15a () u)
(declare-fun a_aunde_unde_17a () u)
(declare-fun a_b2a () Int)
(declare-fun a_h4fd5f73954dc53af536c1c75068837a () u)
(declare-fun a_senthash_primea () u)
(declare-fun a_skcunde_d2a () u)
(declare-fun b () Int)
(declare-fun d () u)
(declare-fun f__bal () tla_Field)
(declare-fun f__decrees () tla_Field)
(declare-fun f__from () tla_Field)
(declare-fun f__slot () tla_Field)
(declare-fun f__type () tla_Field)
(declare-fun f__val () tla_Field)
(declare-fun f__voted () tla_Field)
(declare-fun int2u (Int) u)
(declare-fun isFldOf (tla_Field u) Bool)
(declare-fun m () u)
(declare-fun p () u)
(declare-fun record__2 (u u u) u)
(declare-fun record__3 (u u u u) u)
(declare-fun record__5 (u u u) u)
(declare-fun record__6 (u u u u) u)
(declare-fun record__8 (u u) u)
(declare-fun record__9 (u u u u u) u)
(declare-fun sent () u)
(declare-fun str2u (str) u)
(declare-fun str_a_1aa () str)
(declare-fun str_a_1ba () str)
(declare-fun str_a_2aa () str)
(declare-fun str_a_2ba () str)
(declare-fun tla_dot_i (u tla_Field) Int)
(declare-fun tla_dot_u (u tla_Field) u)
(declare-fun tla_in (u u) Bool)
(declare-fun tla_leq (u u) Bool)
(declare-fun u2bool (u) Bool)
(declare-fun vars () u)
;; Axioms
(assert (forall ((M_20 Int) (N_21 Int)) 
		(! (= (tla_leq (int2u M_20) (int2u N_21)) (<= M_20 N_21)) :pattern ((tla_leq (int2u M_20) (int2u N_21))))))
(assert (forall ((X_22 Int) (Y_23 Int)) 
		(=> (= (int2u X_22) (int2u Y_23)) (= X_22 Y_23))))
(assert (forall ((X_22 str) (Y_23 str)) 
		(=> (= (str2u X_22) (str2u Y_23)) (= X_22 Y_23))))
(assert (forall ((M_20 tla_Field) (X_22 u) (Y_23 u)) 
		(=> (and (isFldOf M_20 Y_23) (= X_22 Y_23)) (isFldOf M_20 X_22))))
(assert (forall ((X__f__bal u) (X__f__slot u) (X__f__val u)) 
		(= (tla_dot_u (record__5 X__f__bal X__f__slot X__f__val) f__bal) X__f__bal)))
(assert (forall ((X__f__bal u) (X__f__slot u) (X__f__val u)) 
		(= (tla_dot_u (record__5 X__f__bal X__f__slot X__f__val) f__slot) X__f__slot)))
(assert (forall ((X__f__bal u) (X__f__slot u) (X__f__val u)) 
		(= (tla_dot_u (record__5 X__f__bal X__f__slot X__f__val) f__val) X__f__val)))
(assert (forall ((X__f__slot u) (X__f__val u)) 
		(= (tla_dot_u (record__8 X__f__slot X__f__val) f__slot) X__f__slot)))
(assert (forall ((X__f__slot u) (X__f__val u)) 
		(= (tla_dot_u (record__8 X__f__slot X__f__val) f__val) X__f__val)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__decrees u) (X__f__from u)) 
		(= (tla_dot_u (record__6 X__f__type X__f__bal X__f__decrees X__f__from) f__type) X__f__type)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__decrees u) (X__f__from u)) 
		(= (tla_dot_u (record__6 X__f__type X__f__bal X__f__decrees X__f__from) f__bal) X__f__bal)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__decrees u) (X__f__from u)) 
		(= (tla_dot_u (record__6 X__f__type X__f__bal X__f__decrees X__f__from) f__decrees) X__f__decrees)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__decrees u) (X__f__from u)) 
		(= (tla_dot_u (record__6 X__f__type X__f__bal X__f__decrees X__f__from) f__from) X__f__from)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__from u)) 
		(= (tla_dot_u (record__2 X__f__type X__f__bal X__f__from) f__type) X__f__type)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__from u)) 
		(= (tla_dot_u (record__2 X__f__type X__f__bal X__f__from) f__bal) X__f__bal)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__from u)) 
		(= (tla_dot_u (record__2 X__f__type X__f__bal X__f__from) f__from) X__f__from)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__slot u) (X__f__val u) (X__f__from u)) 
		(= (tla_dot_u (record__9 X__f__type X__f__bal X__f__slot X__f__val X__f__from) f__type) X__f__type)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__slot u) (X__f__val u) (X__f__from u)) 
		(= (tla_dot_u (record__9 X__f__type X__f__bal X__f__slot X__f__val X__f__from) f__bal) X__f__bal)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__slot u) (X__f__val u) (X__f__from u)) 
		(= (tla_dot_u (record__9 X__f__type X__f__bal X__f__slot X__f__val X__f__from) f__slot) X__f__slot)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__slot u) (X__f__val u) (X__f__from u)) 
		(= (tla_dot_u (record__9 X__f__type X__f__bal X__f__slot X__f__val X__f__from) f__val) X__f__val)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__slot u) (X__f__val u) (X__f__from u)) 
		(= (tla_dot_u (record__9 X__f__type X__f__bal X__f__slot X__f__val X__f__from) f__from) X__f__from)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__voted u) (X__f__from u)) 
		(= (tla_dot_u (record__3 X__f__type X__f__bal X__f__voted X__f__from) f__type) X__f__type)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__voted u) (X__f__from u)) 
		(= (tla_dot_u (record__3 X__f__type X__f__bal X__f__voted X__f__from) f__bal) X__f__bal)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__voted u) (X__f__from u)) 
		(= (tla_dot_u (record__3 X__f__type X__f__bal X__f__voted X__f__from) f__voted) X__f__voted)))
(assert (forall ((X__f__type u) (X__f__bal u) (X__f__voted u) (X__f__from u)) 
		(= (tla_dot_u (record__3 X__f__type X__f__bal X__f__voted X__f__from) f__from) X__f__from)))
(assert (distinct str_a_1aa str_a_1ba str_a_2aa str_a_2ba))
;; Conclusion
(assert (not (not (and (< (tla_dot_i d f__bal) (tla_dot_i a_skcunde_d2a f__bal)) 
	(= (tla_dot_i a_skcunde_d2a f__slot) (tla_dot_i d f__slot))))))
;; Main assertions from the proof obligation
(assert (forall ((a_v16a u) (a_aunde_unde_17a u)) 
		(=> (forall ((a_v18a u)) 
		(= (tla_in a_v18a a_aunde_unde_17a) (exists ((a_v19a u)) 
		(and (tla_in a_v19a S) 
	(tla_in (tla_dot_u a_v19a f__from) Q) 
	(tla_in a_v18a (tla_dot_u a_v19a f__voted)))))) 
		(= (tla_in a_v16a a_aunde_unde_15a) (and (isFldOf f__type a_v16a) 
	(isFldOf f__bal a_v16a) 
	(isFldOf f__from a_v16a) 
	(isFldOf f__decrees a_v16a) 
	(= (tla_dot_u a_v16a f__type) (str2u str_a_2aa)) 
	(= (tla_dot_u a_v16a f__bal) (int2u b)) 
	(= (tla_dot_u a_v16a f__from) p) 
	(= (tla_dot_u a_v16a f__decrees) (ProposeDecrees a_aunde_unde_17a)))))))
(assert (forall ((a_v1a u)) 
		(=> (tla_in a_v1a sent) 
		(or (and (isFldOf f__type a_v1a) 
	(isFldOf f__bal a_v1a) 
	(isFldOf f__from a_v1a) 
	(= (tla_dot_u a_v1a f__type) (str2u str_a_1aa)) 
	true 
	(<= 0 (tla_dot_i a_v1a f__bal)) 
	(tla_in (tla_dot_u a_v1a f__from) Proposers)) 
	(and (isFldOf f__type a_v1a) 
	(isFldOf f__bal a_v1a) 
	(isFldOf f__voted a_v1a) 
	(isFldOf f__from a_v1a) 
	(= (tla_dot_u a_v1a f__type) (str2u str_a_1ba)) 
	true 
	(<= 0 (tla_dot_i a_v1a f__bal)) 
	(forall ((a_v4a u)) 
		(=> (tla_in a_v4a (tla_dot_u a_v1a f__voted)) 
		(and (isFldOf f__bal a_v4a) 
	(isFldOf f__slot a_v4a) 
	(isFldOf f__val a_v4a) 
	true 
	(<= 0 (tla_dot_i a_v4a f__bal)) 
	true 
	(<= 0 (tla_dot_i a_v4a f__slot)) 
	(tla_in (tla_dot_u a_v4a f__val) Values)))) 
	(tla_in (tla_dot_u a_v1a f__from) Acceptors)) 
	(and (isFldOf f__type a_v1a) 
	(isFldOf f__bal a_v1a) 
	(isFldOf f__decrees a_v1a) 
	(isFldOf f__from a_v1a) 
	(= (tla_dot_u a_v1a f__type) (str2u str_a_2aa)) 
	true 
	(<= 0 (tla_dot_i a_v1a f__bal)) 
	(forall ((a_v7a u)) 
		(=> (tla_in a_v7a (tla_dot_u a_v1a f__decrees)) 
		(and (isFldOf f__slot a_v7a) 
	(isFldOf f__val a_v7a) 
	true 
	(<= 0 (tla_dot_i a_v7a f__slot)) 
	(tla_in (tla_dot_u a_v7a f__val) Values)))) 
	(tla_in (tla_dot_u a_v1a f__from) Proposers)) 
	(and (isFldOf f__type a_v1a) 
	(isFldOf f__bal a_v1a) 
	(isFldOf f__slot a_v1a) 
	(isFldOf f__val a_v1a) 
	(isFldOf f__from a_v1a) 
	(= (tla_dot_u a_v1a f__type) (str2u str_a_2ba)) 
	true 
	(<= 0 (tla_dot_i a_v1a f__bal)) 
	true 
	(<= 0 (tla_dot_i a_v1a f__slot)) 
	(tla_in (tla_dot_u a_v1a f__val) Values) 
	(tla_in (tla_dot_u a_v1a f__from) Acceptors))))))
(assert (u2bool MsgInv))
(assert (or (u2bool Next) 
	(= a_h4fd5f73954dc53af536c1c75068837a vars)))
(assert (tla_in p Proposers))
(assert (tla_in m a_senthash_primea))
(assert (<= 0 b))
(assert (tla_in Q Quorums))
(assert (forall ((a_v10a u)) 
		(=> (tla_in a_v10a S) 
		(tla_in a_v10a sent))))
(assert (not (exists ((a_m2a u)) 
		(and (tla_in a_m2a sent) 
	(= (tla_dot_u a_m2a f__type) (str2u str_a_2aa)) 
	(= (tla_dot_i a_m2a f__bal) b)))))
(assert (forall ((a_v11a u)) 
		(=> (tla_in a_v11a S) 
		(and (tla_in a_v11a sent) 
	(= (tla_dot_u a_v11a f__type) (str2u str_a_1ba)) 
	(= (tla_dot_i a_v11a f__bal) b)))))
(assert (forall ((a u)) 
		(=> (tla_in a Q) 
		(exists ((a_m2a u)) 
		(and (tla_in a_m2a S) 
	(= (tla_dot_u a_m2a f__from) a))))))
(assert (u2bool (Send a_aunde_unde_15a)))
(assert (= (tla_dot_u m f__type) (str2u str_a_2aa)))
(assert (exists ((a_v12a u)) 
		(and (tla_in a_v12a S) 
	(tla_in (tla_dot_u a_v12a f__from) Q) 
	(tla_in d (tla_dot_u a_v12a f__voted)))))
(assert (forall ((a_t1a u)) 
		(=> (and (exists ((a_v14a u)) 
		(and (tla_in a_v14a S) 
	(tla_in (tla_dot_u a_v14a f__from) Q) 
	(tla_in a_t1a (tla_dot_u a_v14a f__voted)))) 
	(= (tla_dot_u a_t1a f__slot) (int2u (tla_dot_i d f__slot)))) 
		(tla_leq (tla_dot_u a_t1a f__bal) (int2u (tla_dot_i d f__bal))))))
(assert (<= 0 a_b2a))
(assert (<= 0 a_b2a))
(assert (<= (+ a_b2a 1) b))
(assert (exists ((a_v13a u)) 
		(and (tla_in a_v13a S) 
	(tla_in (tla_dot_u a_v13a f__from) Q) 
	(tla_in a_skcunde_d2a (tla_dot_u a_v13a f__voted)))))
(check-sat)
(exit)