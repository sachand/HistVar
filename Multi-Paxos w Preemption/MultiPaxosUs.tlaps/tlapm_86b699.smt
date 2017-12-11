;; Proof obligation:
;;ASSUME NEW CONSTANT Acceptors,
;;        NEW CONSTANT Values,
;;        NEW CONSTANT Quorums,
;;        NEW CONSTANT Proposers,
;;        NEW VARIABLE sent,
;;        TypeOK
;;        /\ (\A m \in sent :
;;               /\ m.type = "1b"
;;                  => (/\ \A r \in m.voted :
;;                            /\ VotedForIn(m.from, r.bal, r.slot, r.val)
;;                            /\ \A b \in r.bal + 1..m.bal - 1, v \in Values :
;;                                  ~VotedForIn(m.from, b, r.slot, v)
;;                      /\ \A s \in Nat, b \in 0..m.bal - 1, v \in Values :
;;                            VotedForIn(m.from, b, s, v)
;;                            => (\E r \in m.voted : r.slot = s /\ r.bal >= b))
;;               /\ m.type = "2a"
;;                  => (/\ \A d \in m.decrees : SafeAt(m.bal, d.slot, d.val)
;;                      /\ \A d1, d2 \in m.decrees :
;;                            d1.slot = d2.slot => d1 = d2
;;                      /\ \A ma \in sent :
;;                            ma.type = "2a" /\ ma.bal = m.bal => ma = m)
;;               /\ m.type = "2b"
;;                  => (/\ \E ma \in sent :
;;                            /\ ma.type = "2a"
;;                            /\ ma.bal = m.bal
;;                            /\ \E d \in ma.decrees :
;;                                  d.slot = m.slot /\ d.val = m.val)) ,
;;        Next \/ ?h4fd5f73954dc53af536c1c75068837 = vars ,
;;        NEW CONSTANT a \in Acceptors,
;;        \E m \in sent,
;;           m2 \in {m \in sent : m.type \in {"1b", "2b"} /\ m.from = a} :
;;           /\ m.type \in {"1a", "2a"}
;;           /\ m2.bal > m.bal
;;           /\ \A m3
;;                 \in {m_1 \in sent :
;;                        m_1.type \in {"1b", "2b"} /\ m_1.from = a} :
;;                 m2.bal >= m3.bal
;;           /\ ?sent#prime
;;              = sent
;;                \cup {[type |-> "preempt", to |-> m.from, bal |-> m2.bal]} ,
;;        TypeOK
;;        => (\A a_1 \in Acceptors :
;;               (\E m \in sent,
;;                   m2
;;                   \in {m \in sent : m.type \in {"1b", "2b"} /\ m.from = a_1} :
;;                   /\ m.type \in {"1a", "2a"}
;;                   /\ m2.bal > m.bal
;;                   /\ \A m3
;;                         \in {m_1 \in sent :
;;                                m_1.type \in {"1b", "2b"} /\ m_1.from = a_1} :
;;                         m2.bal >= m3.bal
;;                   /\ ?sent#prime
;;                      = sent
;;                        \cup {[type |-> "preempt", to |-> m.from,
;;                               bal |-> m2.bal]})
;;               => (\A aa \in Acceptors, bb \in Nat, vv \in Values, ss \in Nat :
;;                      VotedForIn(aa, bb, ss, vv)
;;                      <=> ?h03062837f0f10c4714e0f53023b1a7(aa, bb, ss, vv))) ,
;;        TypeOK
;;        /\ (\A m \in sent :
;;               /\ m.type = "1b"
;;                  => (/\ \A r \in m.voted :
;;                            /\ VotedForIn(m.from, r.bal, r.slot, r.val)
;;                            /\ \A b \in r.bal + 1..m.bal - 1, v \in Values :
;;                                  ~VotedForIn(m.from, b, r.slot, v)
;;                      /\ \A s \in Nat, b \in 0..m.bal - 1, v \in Values :
;;                            VotedForIn(m.from, b, s, v)
;;                            => (\E r \in m.voted : r.slot = s /\ r.bal >= b))
;;               /\ m.type = "2a"
;;                  => (/\ \A d \in m.decrees : SafeAt(m.bal, d.slot, d.val)
;;                      /\ \A d1, d2 \in m.decrees :
;;                            d1.slot = d2.slot => d1 = d2
;;                      /\ \A ma \in sent :
;;                            ma.type = "2a" /\ ma.bal = m.bal => ma = m)
;;               /\ m.type = "2b"
;;                  => (/\ \E ma \in sent :
;;                            /\ ma.type = "2a"
;;                            /\ ma.bal = m.bal
;;                            /\ \E d \in ma.decrees :
;;                                  d.slot = m.slot /\ d.val = m.val))
;;        /\ Next
;;        => (\A b \in Nat, s \in Nat, v \in Values :
;;               SafeAt(b, s, v) => ?hd4a7fa801d94bc2a9c69d39a405ea2(b, s, v)) ,
;;        \A m2 \in ?sent#prime \ sent : m2.type \notin {"1b", "2b", "2a"} 
;; PROVE  \A m \in ?sent#prime :
;;           /\ m.type = "1b"
;;              => (/\ \A r \in m.voted :
;;                        /\ ?h03062837f0f10c4714e0f53023b1a7(m.from, r.bal,
;;                                                            r.slot, r.val)
;;                        /\ \A b \in r.bal + 1..m.bal - 1, v \in Values :
;;                              ~?h03062837f0f10c4714e0f53023b1a7(m.from, b,
;;                                                                r.slot, v)
;;                  /\ \A s \in Nat, b \in 0..m.bal - 1, v \in Values :
;;                        ?h03062837f0f10c4714e0f53023b1a7(m.from, b, s, v)
;;                        => (\E r \in m.voted : r.slot = s /\ r.bal >= b))
;;           /\ m.type = "2a"
;;              => (/\ \A d \in m.decrees :
;;                        ?hd4a7fa801d94bc2a9c69d39a405ea2(m.bal, d.slot, d.val)
;;                  /\ \A d1, d2 \in m.decrees : d1.slot = d2.slot => d1 = d2
;;                  /\ \A ma \in ?sent#prime :
;;                        ma.type = "2a" /\ ma.bal = m.bal => ma = m)
;;           /\ m.type = "2b"
;;              => (/\ \E ma \in ?sent#prime :
;;                        /\ ma.type = "2a"
;;                        /\ ma.bal = m.bal
;;                        /\ \E d \in ma.decrees :
;;                              d.slot = m.slot /\ d.val = m.val)
(set-logic AUFNIRA)
(declare-sort str 0)
(declare-sort tla_Field 0)
(declare-sort u 0)
;; Declaration of terms, predicates and strings
(declare-fun Acceptors () u)
(declare-fun Next () u)
(declare-fun SafeAt (u u u) u)
(declare-fun TypeOK () u)
(declare-fun Values () u)
(declare-fun VotedForIn (u u u u) u)
(declare-fun a () u)
(declare-fun a_h03062837f0f10c4714e0f53023b1a7a (u u u u) u)
(declare-fun a_h4fd5f73954dc53af536c1c75068837a () u)
(declare-fun a_hd4a7fa801d94bc2a9c69d39a405ea2a (u u u) u)
(declare-fun a_senthash_primea () u)
(declare-fun a_skcunde_ma () u)
(declare-fun f__bal () tla_Field)
(declare-fun f__decrees () tla_Field)
(declare-fun f__from () tla_Field)
(declare-fun f__slot () tla_Field)
(declare-fun f__to () tla_Field)
(declare-fun f__type () tla_Field)
(declare-fun f__val () tla_Field)
(declare-fun f__voted () tla_Field)
(declare-fun int2u (Int) u)
(declare-fun isFldOf (tla_Field u) Bool)
(declare-fun sent () u)
(declare-fun str2u (str) u)
(declare-fun str_a_1aa () str)
(declare-fun str_a_1ba () str)
(declare-fun str_a_2aa () str)
(declare-fun str_a_2ba () str)
(declare-fun str_preempt () str)
(declare-fun tla_dot_u (u tla_Field) u)
(declare-fun tla_in (u u) Bool)
(declare-fun tla_leq (u u) Bool)
(declare-fun tla_lt (u u) Bool)
(declare-fun tla_minus (u u) u)
(declare-fun tla_plus (u u) u)
(declare-fun u2bool (u) Bool)
(declare-fun vars () u)
;; Axioms
(assert (forall ((M_3 Int) (N_4 Int)) 
		(! (= (tla_plus (int2u M_3) (int2u N_4)) (int2u (+ M_3 N_4))) :pattern ((tla_plus (int2u M_3) (int2u N_4))))))
(assert (forall ((M_3 Int) (N_4 Int)) 
		(! (= (tla_minus (int2u M_3) (int2u N_4)) (int2u (- M_3 N_4))) :pattern ((tla_minus (int2u M_3) (int2u N_4))))))
(assert (forall ((M_3 Int) (N_4 Int)) 
		(! (= (tla_lt (int2u M_3) (int2u N_4)) (< M_3 N_4)) :pattern ((tla_lt (int2u M_3) (int2u N_4))))))
(assert (forall ((M_3 Int) (N_4 Int)) 
		(! (= (tla_leq (int2u M_3) (int2u N_4)) (<= M_3 N_4)) :pattern ((tla_leq (int2u M_3) (int2u N_4))))))
(assert (forall ((X_5 Int) (Y_6 Int)) 
		(=> (= (int2u X_5) (int2u Y_6)) (= X_5 Y_6))))
(assert (forall ((X_5 str) (Y_6 str)) 
		(=> (= (str2u X_5) (str2u Y_6)) (= X_5 Y_6))))
(assert (forall ((M_3 tla_Field) (X_5 u) (Y_6 u)) 
		(=> (and (isFldOf M_3 Y_6) (= X_5 Y_6)) (isFldOf M_3 X_5))))
(assert (distinct str_a_1aa str_a_1ba str_a_2aa str_a_2ba str_preempt))
;; Conclusion
(assert (not (and (=> (= (tla_dot_u a_skcunde_ma f__type) (str2u str_a_1ba)) 
		(and (forall ((r u)) 
		(=> (tla_in r (tla_dot_u a_skcunde_ma f__voted)) 
		(and (u2bool (a_h03062837f0f10c4714e0f53023b1a7a (tla_dot_u a_skcunde_ma f__from) (tla_dot_u r f__bal) (tla_dot_u r f__slot) (tla_dot_u r f__val))) 
	(forall ((b Int) (v u)) 
		(=> (and true 
	(tla_leq (tla_plus (tla_dot_u r f__bal) (int2u 1)) (int2u b)) 
	(tla_leq (int2u b) (tla_minus (tla_dot_u a_skcunde_ma f__bal) (int2u 1))) 
	(tla_in v Values)) 
		(not (u2bool (a_h03062837f0f10c4714e0f53023b1a7a (tla_dot_u a_skcunde_ma f__from) (int2u b) (tla_dot_u r f__slot) v)))))))) 
	(forall ((s Int) (b Int) (v u)) 
		(=> (and true 
	(<= 0 s) 
	true 
	(<= 0 b) 
	(tla_leq (int2u b) (tla_minus (tla_dot_u a_skcunde_ma f__bal) (int2u 1))) 
	(tla_in v Values) 
	(u2bool (a_h03062837f0f10c4714e0f53023b1a7a (tla_dot_u a_skcunde_ma f__from) (int2u b) (int2u s) v))) 
		(exists ((r u)) 
		(and (tla_in r (tla_dot_u a_skcunde_ma f__voted)) 
	(= (tla_dot_u r f__slot) (int2u s)) 
	(tla_leq (int2u b) (tla_dot_u r f__bal)))))))) 
	(=> (= (tla_dot_u a_skcunde_ma f__type) (str2u str_a_2aa)) 
		(and (forall ((d u)) 
		(=> (tla_in d (tla_dot_u a_skcunde_ma f__decrees)) 
		(u2bool (a_hd4a7fa801d94bc2a9c69d39a405ea2a (tla_dot_u a_skcunde_ma f__bal) (tla_dot_u d f__slot) (tla_dot_u d f__val))))) 
	(forall ((a_d1a u) (a_d2a u)) 
		(=> (and (tla_in a_d1a (tla_dot_u a_skcunde_ma f__decrees)) 
	(tla_in a_d2a (tla_dot_u a_skcunde_ma f__decrees)) 
	(= (tla_dot_u a_d1a f__slot) (tla_dot_u a_d2a f__slot))) 
		(= a_d1a a_d2a))) 
	(forall ((ma u)) 
		(=> (and (tla_in ma a_senthash_primea) 
	(= (tla_dot_u ma f__type) (str2u str_a_2aa)) 
	(= (tla_dot_u ma f__bal) (tla_dot_u a_skcunde_ma f__bal))) 
		(= ma a_skcunde_ma))))) 
	(=> (= (tla_dot_u a_skcunde_ma f__type) (str2u str_a_2ba)) 
		(exists ((ma u)) 
		(and (tla_in ma a_senthash_primea) 
	(= (tla_dot_u ma f__type) (str2u str_a_2aa)) 
	(= (tla_dot_u ma f__bal) (tla_dot_u a_skcunde_ma f__bal)) 
	(exists ((d u)) 
		(and (tla_in d (tla_dot_u ma f__decrees)) 
	(= (tla_dot_u d f__slot) (tla_dot_u a_skcunde_ma f__slot)) 
	(= (tla_dot_u d f__val) (tla_dot_u a_skcunde_ma f__val))))))))))
;; Main assertions from the proof obligation
(assert (u2bool TypeOK))
(assert (forall ((m u)) 
		(=> (tla_in m sent) 
		(and (=> (= (tla_dot_u m f__type) (str2u str_a_1ba)) 
		(and (forall ((r u)) 
		(=> (tla_in r (tla_dot_u m f__voted)) 
		(and (u2bool (VotedForIn (tla_dot_u m f__from) (tla_dot_u r f__bal) (tla_dot_u r f__slot) (tla_dot_u r f__val))) 
	(forall ((b Int) (v u)) 
		(=> (and true 
	(tla_leq (tla_plus (tla_dot_u r f__bal) (int2u 1)) (int2u b)) 
	(tla_leq (int2u b) (tla_minus (tla_dot_u m f__bal) (int2u 1))) 
	(tla_in v Values)) 
		(not (u2bool (VotedForIn (tla_dot_u m f__from) (int2u b) (tla_dot_u r f__slot) v)))))))) 
	(forall ((s Int) (b Int) (v u)) 
		(=> (and true 
	(<= 0 s) 
	true 
	(<= 0 b) 
	(tla_leq (int2u b) (tla_minus (tla_dot_u m f__bal) (int2u 1))) 
	(tla_in v Values) 
	(u2bool (VotedForIn (tla_dot_u m f__from) (int2u b) (int2u s) v))) 
		(exists ((r u)) 
		(and (tla_in r (tla_dot_u m f__voted)) 
	(= (tla_dot_u r f__slot) (int2u s)) 
	(tla_leq (int2u b) (tla_dot_u r f__bal)))))))) 
	(=> (= (tla_dot_u m f__type) (str2u str_a_2aa)) 
		(and (forall ((d u)) 
		(=> (tla_in d (tla_dot_u m f__decrees)) 
		(u2bool (SafeAt (tla_dot_u m f__bal) (tla_dot_u d f__slot) (tla_dot_u d f__val))))) 
	(forall ((a_d1a u) (a_d2a u)) 
		(=> (and (tla_in a_d1a (tla_dot_u m f__decrees)) 
	(tla_in a_d2a (tla_dot_u m f__decrees)) 
	(= (tla_dot_u a_d1a f__slot) (tla_dot_u a_d2a f__slot))) 
		(= a_d1a a_d2a))) 
	(forall ((ma u)) 
		(=> (and (tla_in ma sent) 
	(= (tla_dot_u ma f__type) (str2u str_a_2aa)) 
	(= (tla_dot_u ma f__bal) (tla_dot_u m f__bal))) 
		(= ma m))))) 
	(=> (= (tla_dot_u m f__type) (str2u str_a_2ba)) 
		(exists ((ma u)) 
		(and (tla_in ma sent) 
	(= (tla_dot_u ma f__type) (str2u str_a_2aa)) 
	(= (tla_dot_u ma f__bal) (tla_dot_u m f__bal)) 
	(exists ((d u)) 
		(and (tla_in d (tla_dot_u ma f__decrees)) 
	(= (tla_dot_u d f__slot) (tla_dot_u m f__slot)) 
	(= (tla_dot_u d f__val) (tla_dot_u m f__val)))))))))))
(assert (or (u2bool Next) 
	(= a_h4fd5f73954dc53af536c1c75068837a vars)))
(assert (tla_in a Acceptors))
(assert (exists ((m u) (a_m2a u)) 
		(and (tla_in m sent) 
	(tla_in a_m2a sent) 
	(or (= (tla_dot_u a_m2a f__type) (str2u str_a_1ba)) 
	(= (tla_dot_u a_m2a f__type) (str2u str_a_2ba))) 
	(= (tla_dot_u a_m2a f__from) a) 
	(or (= (tla_dot_u m f__type) (str2u str_a_1aa)) 
	(= (tla_dot_u m f__type) (str2u str_a_2aa))) 
	(tla_lt (tla_dot_u m f__bal) (tla_dot_u a_m2a f__bal)) 
	(forall ((a_m3a u)) 
		(=> (and (tla_in a_m3a sent) 
	(or (= (tla_dot_u a_m3a f__type) (str2u str_a_1ba)) 
	(= (tla_dot_u a_m3a f__type) (str2u str_a_2ba))) 
	(= (tla_dot_u a_m3a f__from) a)) 
		(tla_leq (tla_dot_u a_m3a f__bal) (tla_dot_u a_m2a f__bal)))) 
	(forall ((a_v1a u)) 
		(= (tla_in a_v1a a_senthash_primea) (or (tla_in a_v1a sent) 
	(and (isFldOf f__type a_v1a) 
	(isFldOf f__to a_v1a) 
	(isFldOf f__bal a_v1a) 
	(= (tla_dot_u a_v1a f__type) (str2u str_preempt)) 
	(= (tla_dot_u a_v1a f__to) (tla_dot_u m f__from)) 
	(= (tla_dot_u a_v1a f__bal) (tla_dot_u a_m2a f__bal)))))))))
(assert (forall ((a_aunde_1a u)) 
		(=> (and (tla_in a_aunde_1a Acceptors) 
	(exists ((m u) (a_m2a u)) 
		(and (tla_in m sent) 
	(tla_in a_m2a sent) 
	(or (= (tla_dot_u a_m2a f__type) (str2u str_a_1ba)) 
	(= (tla_dot_u a_m2a f__type) (str2u str_a_2ba))) 
	(= (tla_dot_u a_m2a f__from) a_aunde_1a) 
	(or (= (tla_dot_u m f__type) (str2u str_a_1aa)) 
	(= (tla_dot_u m f__type) (str2u str_a_2aa))) 
	(tla_lt (tla_dot_u m f__bal) (tla_dot_u a_m2a f__bal)) 
	(forall ((a_m3a u)) 
		(=> (and (tla_in a_m3a sent) 
	(or (= (tla_dot_u a_m3a f__type) (str2u str_a_1ba)) 
	(= (tla_dot_u a_m3a f__type) (str2u str_a_2ba))) 
	(= (tla_dot_u a_m3a f__from) a_aunde_1a)) 
		(tla_leq (tla_dot_u a_m3a f__bal) (tla_dot_u a_m2a f__bal)))) 
	(forall ((a_v2a u)) 
		(= (tla_in a_v2a a_senthash_primea) (or (tla_in a_v2a sent) 
	(and (isFldOf f__type a_v2a) 
	(isFldOf f__to a_v2a) 
	(isFldOf f__bal a_v2a) 
	(= (tla_dot_u a_v2a f__type) (str2u str_preempt)) 
	(= (tla_dot_u a_v2a f__to) (tla_dot_u m f__from)) 
	(= (tla_dot_u a_v2a f__bal) (tla_dot_u a_m2a f__bal))))))))) 
		(forall ((aa u) (bb Int) (vv u) (ss Int)) 
		(=> (and (tla_in aa Acceptors) 
	true 
	(<= 0 bb) 
	(tla_in vv Values) 
	true 
	(<= 0 ss)) 
		(= (u2bool (VotedForIn aa (int2u bb) (int2u ss) vv)) (u2bool (a_h03062837f0f10c4714e0f53023b1a7a aa (int2u bb) (int2u ss) vv))))))))
(assert (=> (u2bool Next) 
		(forall ((b Int) (s Int) (v u)) 
		(=> (and true 
	(<= 0 b) 
	true 
	(<= 0 s) 
	(tla_in v Values) 
	(u2bool (SafeAt (int2u b) (int2u s) v))) 
		(u2bool (a_hd4a7fa801d94bc2a9c69d39a405ea2a (int2u b) (int2u s) v))))))
(assert (forall ((a_m2a u)) 
		(=> (and (tla_in a_m2a a_senthash_primea) 
	(not (tla_in a_m2a sent))) 
		(not (or (= (tla_dot_u a_m2a f__type) (str2u str_a_1ba)) 
	(= (tla_dot_u a_m2a f__type) (str2u str_a_2ba)) 
	(= (tla_dot_u a_m2a f__type) (str2u str_a_2aa)))))))
(assert (tla_in a_skcunde_ma a_senthash_primea))
(check-sat)
(exit)