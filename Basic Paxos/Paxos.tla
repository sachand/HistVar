------------------------------- MODULE PaxosLam -------------------------------
(***************************************************************************)
(* This is a TLA+ specification of the Paxos Consensus algorithm,          *)
(* described in                                                            *)
(*                                                                         *)
(*  Paxos Made Simple:                                                     *)
(*   http://research.microsoft.com/en-us/um/people/lamport/pubs/pubs.html#paxos-simple *)
(*                                                                         *)
(* and a TLAPS-checked proof of its correctness.  This was mostly done as  *)
(* a test to see how the SMT backend of TLAPS is now working.              *)
(***************************************************************************)
EXTENDS Integers, TLAPS, NaturalsInduction

CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Ballots == Nat

VARIABLES sent

vars == <<sent>>

Send(m) == sent' = sent \cup {m}

None == CHOOSE v : v \notin Values

Init == sent = {}

(***************************************************************************)
(* Phase 1a: A leader selects a ballot number b and sends a 1a message     *)
(* with ballot b to a majority of acceptors.  It can do this only if it    *)
(* has not already sent a 1a message for ballot b.                         *)
(***************************************************************************)
Phase1a(b) == Send([type |-> "1a", bal |-> b])
              
(***************************************************************************)
(* Phase 1b: If an acceptor receives a 1a message with ballot b greater    *)
(* than that of any 1a message to which it has already responded, then it  *)
(* responds to the request with a promise not to accept any more proposals *)
(* for ballots numbered less than b and with the highest-numbered ballot   *)
(* (if any) for which it has voted for a value and the value it voted for  *)
(* in that ballot.  That promise is made in a 1b message.                  *)
(***************************************************************************)
accepted(a) == LET 2bs == {m \in sent: m.type = "2b" /\ m.acc = a}
               IN IF 2bs # {} THEN {m \in 2bs: \A m2 \in 2bs: m.bal >= m2.bal}
                  ELSE {[bal |-> -1, val |-> None]}

Phase1b(a) ==
  \E m \in sent, r \in accepted(a):
     /\ m.type = "1a"
     /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal > m2.bal
     /\ Send([type |-> "1b", bal |-> m.bal,
              maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a])
        
(***************************************************************************)
(* Phase 2a: If the leader receives a response to its 1b message (for      *)
(* ballot b) from a quorum of acceptors, then it sends a 2a message to all *)
(* acceptors for a proposal in ballot b with a value v, where v is the     *)
(* value of the highest-numbered proposal among the responses, or is any   *)
(* value if the responses reported no proposals.  The leader can send only *)
(* one 2a message for any ballot.                                          *)
(***************************************************************************)
Phase2a(b) ==
  /\ ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b) 
  /\ \E v \in Values: \E Q \in Quorums: \E S:
       /\ S = {m \in sent: m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
       /\ \A a \in Q: \E m \in S : m.acc = a
       /\ \/ \A m \in S: m.maxVBal = -1
          \/ \E m \in S: /\ v = m.maxVal
                         /\ \A m2 \in S: m2.maxVBal < m.maxVBal
       /\ Send([type |-> "2a", bal |-> b, val |-> v])

Phase2a1(b) ==
  /\ ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b) 
  /\ \E v \in Values :
       /\ \E Q \in Quorums :
            \E S \in SUBSET {m \in sent : (m.type = "1b") /\ (m.bal = b)} :
               /\ \A a \in Q : \E m \in S : m.acc = a
               /\ \/ \A m \in S : m.maxVBal = -1
                  \/ \E c \in 0..(b-1) : 
                        /\ \A m \in S : m.maxVBal =< c
                        /\ \E m \in S : /\ m.maxVBal = c
                                        /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])

(***************************************************************************)
(* Phase 2b: If an acceptor receives a 2a message for a ballot numbered    *)
(* b, it votes for the message's value in ballot b unless it has already   *)
(* responded to a 1a request for a ballot number greater than or equal to  *)
(* b.                                                                      *)
(***************************************************************************)
Phase2b(a) == 
  \E m \in sent :
    /\ m.type = "2a" 
    /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal >= m2.bal
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])

Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a) 

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* How a value is chosen:                                                  *)
(*                                                                         *)
(* This spec does not contain any actions in which a value is explicitly   *)
(* chosen (or a chosen value learned).  Wnat it means for a value to be    *)
(* chosen is defined by the operator Chosen, where Chosen(v) means that v  *)
(* has been chosen.  From this definition, it is obvious how a process     *)
(* learns that a value has been chosen from messages of type "2b".         *)
(***************************************************************************)
VotedForIn(a, v, b) == \E m \in sent : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

(***************************************************************************)
(* The consistency condition that a consensus algorithm must satisfy is    *)
(* the invariance of the following state predicate Consistency.            *)
(***************************************************************************)
Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => (v1 = v2)
-----------------------------------------------------------------------------
(***************************************************************************)
(* This section of the spec defines the invariant Inv.                     *)
(***************************************************************************)
Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOK == sent \in SUBSET Messages

MsgInv ==
  \A m \in sent : 
    /\ m.type = "1b" =>
         /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
         /\ m.maxVBal < m.bal
         /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
    /\ m.type = "2a" =>
         /\ \E Q \in Quorums: \E S:
              /\ S = {m2 \in sent: m2.type = "1b" /\ m2.acc \in Q /\ m2.bal = m.bal}
              /\ \A a \in Q: \E m2 \in S : m2.acc = a
              /\ \/ \A m2 \in S: m2.maxVBal = -1
                 \/ \E m2 \in S: /\ m.val = m2.maxVal
                                 /\ \A m3 \in S: m3.maxVBal =< m2.maxVBal
         /\ \A ma \in sent : (ma.type = "2a") /\ (ma.bal = m.bal)
                                => (ma = m)
    /\ m.type = "2b" =>
         /\ \E ma \in sent : /\ ma.type = "2a"
                             /\ ma.bal  = m.bal
                             /\ ma.val  = m.val

DerivedInv ==
  \A m \in sent: m.type = "2b" =>
    /\ \E Q \in Quorums, S \in SUBSET {m2 \in sent: m2.type = "1b" /\ m2.bal = m.bal}:
          /\ \A a \in Q: \E m2 \in S: m2.acc = a
          /\ \/ \A m2 \in S: /\ m2.maxVBal = -1
                             /\ \A b \in 0..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
             \/ \E m2 \in S: /\ m.val = m2.maxVal
                             /\ \A m3 \in S: m3.maxVBal =< m2.maxVBal
                             /\ m2.maxVBal < m.bal
                             /\ VotedForIn(m2.acc, m2.maxVal, m2.maxVBal)
                             /\ \A b \in m2.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)

DerivedInv2 ==
  \A a \in Acceptors, b \in Ballots, v \in Values: VotedForIn(a, v, b) =>
    /\ \E Q \in Quorums, S \in SUBSET {m2 \in sent: m2.type = "1b" /\ m2.bal = b}:
          /\ \A a2 \in Q: \E m2 \in S: m2.acc = a2
          /\ \/ \A m2 \in S: /\ m2.maxVBal = -1
                             /\ \A b2 \in 0..b-1: ~\E v2 \in Values: VotedForIn(m2.acc, v2, b2)
             \/ \E m2 \in S: /\ v = m2.maxVal
                             /\ \A m3 \in S: m3.maxVBal =< m2.maxVBal
                             /\ m2.maxVbal < b
                             /\ VotedForIn(m2.acc, v, m2.maxVBal)
                             /\ \A b2 \in m2.maxVBal+1..b-1: ~\E v2 \in Values: VotedForIn(m2.acc, v2, b2)

DerivedInv3 ==
  \A a \in Acceptors, b \in Ballots, v \in Values: VotedForIn(a, v, b) =>
    /\ \E Q \in Quorums:
          \/ \A a2 \in Q: \A b2 \in 0..b-1, v2 \in Values: ~VotedForIn(a2, v2, b2)
          \/ \E a2 \in Acceptors, b2 \in Ballots:
                          /\ b2 < b
                          /\ VotedForIn(a2, v, b2)
                          /\ \A a3 \in Q, b3 \in b2+1..b-1, v3 \in Values: ~VotedForIn(a3, v3, b3)

THEOREM TypeOK /\ MsgInv => DerivedInv3
  <1> SUFFICES ASSUME TypeOK /\ MsgInv,
                      NEW a \in Acceptors, NEW b \in Ballots, NEW v \in Values,
                      NEW m \in sent,
                      /\ m.type = "2b"
                      /\ m.val  = v
                      /\ m.bal  = b
                      /\ m.acc  = a
               PROVE  \E Q \in Quorums:
                            \/ \A a2 \in Q: \A b2 \in 0..b-1, v2 \in Values: ~VotedForIn(a2, v2, b2)
                            \/ \E a2 \in Acceptors, b2 \in Ballots:
                                            /\ b2 < b
                                            /\ VotedForIn(a2, v, b2)
                                            /\ \A a3 \in Q, b3 \in b2+1..b-1, v3 \in Values: ~VotedForIn(a3, v3, b3)
    BY DEF DerivedInv3, VotedForIn
  <1> USE DEF Ballots
  <1>1. PICK m2a \in sent: m2a.type = "2a" /\ m2a.bal = b /\ m2a.val = v
    BY DEF MsgInv
  <1>2. PICK Q \in Quorums, S \in SUBSET {m2 \in sent: m2.type = "1b" /\ m2.bal = m2a.bal}:
              /\ \A a2 \in Q: \E m2 \in S: m2.acc = a2
              /\ \/ \A m2 \in S: m2.maxVBal = -1
                 \/ \E m2 \in S: /\ m2a.val = m2.maxVal
                                 /\ \A m3 \in S: m3.maxVBal =< m2.maxVBal
    BY <1>1 DEF MsgInv
  <1>3. CASE \A m2 \in S: m2.maxVBal = -1
    <2>1. \A m2 \in S: /\ m2.bal = m2a.bal
                       /\ m2.maxVBal = -1
                       /\ VotedForIn(m2.acc, m2.maxVal, m2.maxVBal) \/ m2.maxVBal = -1
                       /\ m2.maxVBal < m2.bal
                       /\ \A b2 \in m2.maxVBal+1..m2.bal-1: ~\E v2 \in Values: VotedForIn(m2.acc, v2, b2)
      BY <1>3, <1>2 DEF MsgInv
    <2>2. \A m2 \in S: \A b2 \in 0..b-1: ~\E v2 \in Values: VotedForIn(m2.acc, v2, b2)
      BY <2>1, <1>1
    <2> QED BY <1>2, <2>2, QuorumAssumption DEF TypeOK, Messages
  <1>4. CASE \E m2 \in S: /\ m2a.val = m2.maxVal
                          /\ \A m3 \in S: m3.maxVBal =< m2.maxVBal
    <2>1. PICK m2 \in S: /\ m2.bal = m2a.bal
                         /\ m2a.val = m2.maxVal
                         /\ VotedForIn(m2.acc, m2.maxVal, m2.maxVBal) \/ m2.maxVBal = -1
                         /\ m2.maxVBal < m2.bal
                         /\ \A m3 \in S: /\ m3.maxVBal =< m2.maxVBal
                                         /\ \A b2 \in m3.maxVBal+1..m2.bal-1: ~\E v2 \in Values: VotedForIn(m3.acc, v2, b2)
      BY <1>4, <1>2 DEF MsgInv
    <2>2. /\ VotedForIn(m2.acc, v, m2.maxVBal) \/ m2.maxVBal = -1
          /\ m2.maxVBal < b
          /\ \A a3 \in Q, b2 \in m2.maxVBal+1..b-1, v2 \in Values: ~VotedForIn(a3, v2, b2)
      BY <2>1, <1>1, <1>2 DEF TypeOK, Messages
    <2> QED BY <2>2 DEF TypeOK, Messages
  <1> QED BY <1>3, <1>4, <1>2, <1>1

Inv == TypeOK /\ MsgInv /\ DerivedInv3

LEMMA VotedOnce == 
        MsgInv =>  \A a1, a2 \in Acceptors, b \in Ballots, v1, v2 \in Values :
                       VotedForIn(a1, v1, b) /\ VotedForIn(a2, v2, b) => (v1 = v2)
BY DEF MsgInv, VotedForIn

LEMMA NoChosenIn == \A b:
  (\E Q \in Quorums: \A a \in Q, v \in Values: ~VotedForIn(a, v, b))
  =>
  \A v \in Values: ~ChosenIn(v, b)
BY QuorumAssumption DEF ChosenIn

LEMMA VotedChosen ==
  MsgInv => \A a \in Acceptors, v1, v2 \in Values, b \in Ballots:
    VotedForIn(a, v1, b) /\ ChosenIn(v2, b) => v1 = v2
  <1> SUFFICES ASSUME MsgInv,
                      NEW a \in Acceptors, NEW v1 \in Values, NEW v2 \in Values, NEW b \in Ballots,
                      VotedForIn(a, v1, b),
                      NEW Q \in Quorums,
                      \A a2 \in Q : VotedForIn(a2, v2, b)
               PROVE  v1 = v2
    BY DEF ChosenIn
  <1>1. PICK a2 \in Q: VotedForIn(a2, v2, b) BY QuorumAssumption
  <1>2. v1 = v2 BY <1>1, VotedOnce, QuorumAssumption
  <1> QED BY <1>2

Inv5(b) ==
  Inv => \A v1, v2 \in Values, b1, b2 \in 0..b:
           /\ ChosenIn(v1, b1) /\ b1 =< b2
           /\ \E a \in Acceptors: VotedForIn(a, v2, b2)
           => v1 = v2

LEMMA Inv6 ==
  Inv => \A a \in Acceptors, v \in Values, b, b2 \in Ballots:
    (VotedForIn(a, v, b) /\ b2 < b) =>
    (\/ \E Q \in Quorums: \A a2 \in Q, v2 \in Values: ~VotedForIn(a2, v2, b2)
     \/ \E a2 \in Acceptors: VotedForIn(a2, v, b2))
BY NatInduction DEF Inv, DerivedInv3, Ballots
      
LEMMA Inv5_BaseStep ==
  Inv5(0)
  <1> SUFFICES ASSUME Inv,
                      NEW v1 \in Values, NEW v2 \in Values, NEW b1 \in 0..0, NEW b2 \in 0..0,
                      NEW Q \in Quorums,
                      \A a \in Q : VotedForIn(a, v1, b1),
                      b1 =< b2,
                      NEW a \in Acceptors,
                      VotedForIn(a, v2, b2)
               PROVE  v1 = v2
    BY DEF ChosenIn, Inv5
  <1>1. PICK a2 \in Acceptors: a2 \in Q /\ VotedForIn(a2, v1, b1) BY QuorumAssumption
  <1>2. VotedForIn(a2, v1, b1) /\ VotedForIn(a, v2, b2) BY <1>1 DEF Ballots
  <1> QED BY <1>1, <1>2, b1 = b2, VotedOnce, QuorumAssumption DEF Inv, Ballots

LEMMA Inv5_InductiveStep ==
  \A b \in Nat: Inv5(b) => Inv5(b+1)
  <1> SUFFICES ASSUME NEW b \in Nat,
                      Inv5(b),
                      Inv,
                      NEW v1 \in Values, NEW v2 \in Values, NEW b1 \in 0..(b+1), NEW b2 \in 0..(b+1),
                      NEW Q1 \in Quorums,
                      \A a \in Q1 : VotedForIn(a, v1, b1),
                      b1 =< b2,
                      NEW a \in Acceptors,
                      VotedForIn(a, v2, b2)
               PROVE  v1 = v2
    BY DEF ChosenIn, Inv5
  <1> USE DEF Ballots
  <1>1. CASE (b1 \in 0..b /\ b2 \in 0..b)
    BY <1>1, QuorumAssumption DEF Inv5, ChosenIn
  <1>2. CASE (b1 = b+1 /\ b2 = b+1)
    <2>1. PICK a2 \in Acceptors: a2 \in Q1 /\ VotedForIn(a2, v1, b1) BY QuorumAssumption
    <2>2. VotedForIn(a2, v1, b1) /\ VotedForIn(a, v2, b1) BY <1>2, <2>1
    <2> QED BY <2>2, VotedOnce DEF Inv
  <1>3. CASE b2 = b+1 /\ b1 \in 0..b
    <2>1. PICK Q2 \in Quorums:
            \/ \A a2 \in Q2, b3 \in 0..b2-1, v3 \in Values: ~VotedForIn(a2, v3, b3)
            \/ \E a2 \in Q2, b3 \in Ballots:
                 /\ b3 < b2
                 /\ VotedForIn(a2, v2, b3)
                 /\ \A a3 \in Q2, b4 \in b3+1..b2-1, v3 \in Values: ~VotedForIn(a3, v3, b4)
      BY DEF Inv, DerivedInv3
    <2>2. CASE \A a2 \in Q2, b3 \in 0..b2-1, v3 \in Values: ~VotedForIn(a2, v3, b3)
      <3>1. PICK a2 \in Acceptors: a2 \in Q1 \cap Q2 BY QuorumAssumption
      <3>2. VotedForIn(a2, v1, b1) BY <3>1
      <3>3. \A v3 \in Values: ~VotedForIn(a2, v3, b1) BY <1>3, <2>2, <3>1
      <3> QED BY <3>2, <3>3
    <2>3. CASE \E a2 \in Q2, b3 \in Ballots:
                 /\ b3 < b2
                 /\ VotedForIn(a2, v2, b3)
                 /\ \A a3 \in Q2, b4 \in b3+1..b2-1, v3 \in Values: ~VotedForIn(a3, v3, b4)
      <3> SUFFICES ASSUME NEW a2 \in Q2, NEW b3 \in Ballots,
                          b3 < b2, VotedForIn(a2, v2, b3),
                          \A a3 \in Q2, b4 \in b3+1..b2-1, v3 \in Values: ~VotedForIn(a3, v3, b4)
                   PROVE  v1 = v2
        BY <2>3
        <3>1. b3 \in 0..b BY <1>3
        <3>2. ChosenIn(v1, b1) BY DEF ChosenIn
        <3>3. b1 =< b3 BY <1>3, b1 > b3 => b1 \in b3+1..b2-1, <3>2, NoChosenIn
      <3> QED BY <1>3, <3>1, <3>2, <3>3, QuorumAssumption DEF Inv5
    <2> QED BY <2>1, <2>2, <2>3
  <1> QED BY <1>1, <1>2, <1>3

LEMMA Inv5_Always == \A b \in Ballots: Inv5(b)
BY Inv5_BaseStep, Inv5_InductiveStep, NatInduction DEF Ballots

LEMMA Consistent4 == Inv => Consistency
BY QuorumAssumption, Inv5_Always DEF Ballots, Consistency, Chosen, ChosenIn, Inv5

-----------------------------------------------------------------------------
THEOREM Invariant == Spec => []Inv
<1> USE DEF Ballots, accepted
<1>1. Init => Inv
  BY DEF Init, Inv, TypeOK, MsgInv, VotedForIn
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, Next
               PROVE  Inv'
    BY DEF vars, Inv, TypeOK, MsgInv, VotedForIn
  <2> USE DEF Inv
  <2>1. TypeOK'
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b) PROVE TypeOK'
      BY <3>1 DEF TypeOK, Phase1a, Send, Messages
    <3>2. ASSUME NEW b \in Ballots, Phase2a(b) PROVE TypeOK'
      <4>1. PICK v \in Values :
               Send([type |-> "2a", bal |-> b, val |-> v])
        BY <3>2 DEF Phase2a
      <4>. QED
        BY <4>1 DEF TypeOK, Send, Messages
    <3>3. ASSUME NEW a \in Acceptors, Phase1b(a) PROVE TypeOK'
      <4>. PICK m \in sent, r \in accepted(a): Phase1b(a)!(m, r)
        BY <3>3 DEF Phase1b
      <4>. QED
        BY DEF Send, TypeOK, Messages
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a) PROVE TypeOK'
      <4>. PICK m \in sent : Phase2b(a)!(m)
        BY <3>4 DEF Phase2b
      <4>. QED 
        BY DEF Send, TypeOK, Messages
    <3>. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>3. MsgInv'
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b)
          PROVE  MsgInv'
        BY <3>1, QuorumAssumption DEF Phase1a, MsgInv, TypeOK, Messages, Send, VotedForIn
    <3>2. ASSUME NEW a \in Acceptors, Phase1b(a)
          PROVE  MsgInv'
      <4> SUFFICES ASSUME NEW m \in sent'
                   PROVE  (/\ m.type = "1b" =>
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                                /\ m.maxVBal < m.bal
                                /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
                           /\ m.type = "2a" =>
                                /\ \E Q \in Quorums: \E S:
                                     /\ S = {m2 \in sent: m2.type = "1b" /\ m2.bal = m.bal /\ m2.acc \in Q}
                                     /\ \A a_1 \in Q: \E m2 \in S: m2.acc = a_1
                                     /\ \/ \A m2 \in S: m2.maxVBal = -1
                                        \/ \E m2 \in S: /\ m.val = m2.maxVal
                                                        /\ \A m3 \in S: m3.maxVBal =< m2.maxVBal
                                /\ \A ma \in sent : (ma.type = "2a") /\ (ma.bal = m.bal)
                                                       => (ma = m)
                           /\ m.type = "2b" =>
                                /\ \E ma \in sent : /\ ma.type = "2a"
                                                    /\ ma.bal  = m.bal
                                                    /\ ma.val  = m.val)'
        BY DEF MsgInv
      <4>. PICK m4 \in sent, r \in accepted(a): Phase1b(a)!(m4, r)
        BY <3>2 DEF Phase1b
      <4>0. \A a2,v2,b2 : VotedForIn(a2,v2,b2)' <=> VotedForIn(a2,v2,b2)
        BY DEF Send, VotedForIn
      <4>5. \/ VotedForIn(a, r.val, r.bal)
            \/ r.bal = -1
        BY DEF TypeOK, Messages, VotedForIn
      <4>6. \A c \in (r.bal+1)..(m4.bal-1), v \in Values : ~VotedForIn(a, v, c)
        BY DEF TypeOK, Messages, VotedForIn, Send
      <4>1. (m.type = "1b" =>
               /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
               /\ m.maxVBal < m.bal
               /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b))'
        BY <4>5, <4>6, <4>0 DEF MsgInv, TypeOK, Messages, Send
      <4>2. (m.type = "2a" =>
               /\ \E Q \in Quorums: \E S:
                    /\ S = {m2 \in sent: m2.type = "1b" /\ m2.bal = m.bal /\ m2.acc \in Q}
                    /\ \A a_1 \in Q: \E m2 \in S: m2.acc = a_1
                    /\ \/ \A m2 \in S: m2.maxVBal = -1
                       \/ \E m2 \in S: /\ m.val = m2.maxVal
                                       /\ \A m3 \in S: m3.maxVBal =< m2.maxVBal
               /\ \A ma \in sent : (ma.type = "2a") /\ (ma.bal = m.bal)
                                      => (ma = m))'
        BY \A m5 \in sent' \ sent: m5.type = "1b" DEF MsgInv, TypeOK, Messages, Send
      <4>3. (m.type = "2b" =>
               /\ \E ma \in sent : /\ ma.type = "2a"
                                   /\ ma.bal  = m.bal
                                   /\ ma.val  = m.val)'
        BY \A m5 \in sent' \ sent: m5.type = "1b" DEF MsgInv, TypeOK, Messages, Send
      <4>4. QED
        BY <4>1, <4>2, <4>3
      (*
      
      
      <4> HIDE DEF accepted
      <4> QED BY <4>5, <4>6, <4>0, <4>7, \A m5 \in sent' \ sent: m2.type = "1b" DEF MsgInv, TypeOK, Messages, Send*)
    <3>3. ASSUME NEW b \in Ballots, Phase2a(b)
          PROVE  MsgInv'
      <4>1. ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b)
        BY <3>3 DEF Phase2a
      <4>2. \E Q \in Quorums: \E S:
              /\ S = {m2 \in sent : m2.type = "1b" /\ m2.acc \in Q /\ m2.bal = b}
              /\ \A a \in Q : \E m \in S : m.acc = a
        BY <3>3 DEF Phase2a
      <4>3. \A m \in sent' \ sent: m.type = "2a" BY <3>3 DEF Send, Phase2a
      <4>6. \A m,ma \in sent' : m.type = "2a" /\ ma.type = "2a" /\ ma.bal = m.bal
                                => ma = m
        BY <4>1, Isa DEF MsgInv
      <4>8. (\A m \in sent : m.type = "2b" =>
               \E m2 \in sent: m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val)'
        BY <4>3, \A m \in sent': sent.type = "2b" => m \in sent DEF MsgInv, TypeOK, Messages, Send
      <4>. QED
         BY QuorumAssumption, <4>3, <4>2, <4>6, <4>8 DEF MsgInv, TypeOK, Messages, Send
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a)
          PROVE  MsgInv'
      <4>. PICK m \in sent : Phase2b(a)!(m)
        BY <3>4 DEF Phase2b
      <4>1. \A aa, vv, bb : VotedForIn(aa,vv,bb) => VotedForIn(aa,vv,bb)'
        BY DEF VotedForIn, Send
      <4>2. \A mm \in sent : mm.type = "1b"
               => \A v \in Values, c \in (mm.maxVBal+1) .. (mm.bal-1) :
                     ~ VotedForIn(mm.acc, v, c) => ~ VotedForIn(mm.acc, v, c)'
        BY DEF Send, VotedForIn, MsgInv, TypeOK, Messages
      <4>. QED
        BY <4>1, <4>2, <2>1 DEF MsgInv, Send, TypeOK, Messages
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>4. QED
    BY <2>1, <2>3 DEF Inv
(* old:
  <2>3. MsgInv'
    <3>1. ASSUME NEW b \in Ballots, Phase1a(b)
          PROVE  MsgInv'
        BY <3>1, QuorumAssumption DEF Phase1a, MsgInv, TypeOK, Messages, Send, VotedForIn
    <3>2. ASSUME NEW a \in Acceptors, Phase1b(a)
          PROVE  MsgInv'
      <4> SUFFICES ASSUME NEW m \in sent'
                   PROVE  (/\ m.type = "1b" =>
                                /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                                /\ m.maxVBal < m.bal
                                /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
                           /\ m.type = "2a" =>
                                /\ \E Q \in Quorums, S \in SUBSET {m2 \in sent: m2.type = "1b" /\ m2.bal = m.bal}:
                                     /\ \A a_1 \in Q: \E m2 \in S: m2.acc = a_1
                                     /\ \/ \A m2 \in S: m2.maxVBal = -1
                                        \/ \E m2 \in S: /\ m.val = m2.maxVal
                                                        /\ \A m3 \in S: m3.maxVBal =< m2.maxVBal
                                /\ \A ma \in sent : (ma.type = "2a") /\ (ma.bal = m.bal)
                                                       => (ma = m)
                           /\ m.type = "2b" =>
                                /\ \E ma \in sent : /\ ma.type = "2a"
                                                    /\ ma.bal  = m.bal
                                                    /\ ma.val  = m.val)'
        BY DEF MsgInv
      <4>. PICK m4 \in sent, r \in accepted(a): Phase1b(a)!(m4, r)
        BY <3>2 DEF Phase1b
      <4>0. \A a2,v2,b2 : VotedForIn(a2,v2,b2)' <=> VotedForIn(a2,v2,b2)
        BY DEF Send, VotedForIn
      <4>5. \/ VotedForIn(a, r.val, r.bal)
            \/ r.bal = -1
        BY DEF TypeOK, Messages, VotedForIn
      <4>6. \A c \in (r.bal+1)..(m4.bal-1), v \in Values : ~VotedForIn(a, v, c)
        BY DEF TypeOK, Messages, VotedForIn, Send
      <4>1. (m.type = "1b" =>
               /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
               /\ m.maxVBal < m.bal
               /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b))'
        BY <4>5, <4>6, <4>0 DEF MsgInv, TypeOK, Messages, Send
      <4>2. (m.type = "2a" =>
               /\ \E Q \in Quorums, S \in SUBSET {m2 \in sent: m2.type = "1b" /\ m2.bal = m.bal}:
                    /\ \A a_1 \in Q: \E m2 \in S: m2.acc = a_1
                    /\ \/ \A m2 \in S: m2.maxVBal = -1
                       \/ \E m2 \in S: /\ m.val = m2.maxVal
                                       /\ \A m3 \in S: m3.maxVBal =< m2.maxVBal
               /\ \A ma \in sent : (ma.type = "2a") /\ (ma.bal = m.bal)
                                      => (ma = m))'
        BY \A m5 \in sent' \ sent: m5.type = "1b" DEF MsgInv, TypeOK, Messages, Send
      <4>3. (m.type = "2b" =>
               /\ \E ma \in sent : /\ ma.type = "2a"
                                   /\ ma.bal  = m.bal
                                   /\ ma.val  = m.val)'
        BY \A m5 \in sent' \ sent: m5.type = "1b" DEF MsgInv, TypeOK, Messages, Send
      <4>4. QED
        BY <4>1, <4>2, <4>3
      (*
      
      
      <4> HIDE DEF accepted
      <4> QED BY <4>5, <4>6, <4>0, <4>7, \A m5 \in sent' \ sent: m2.type = "1b" DEF MsgInv, TypeOK, Messages, Send*)
    <3>3. ASSUME NEW b \in Ballots, Phase2a(b)
          PROVE  MsgInv'
      <4>1. ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b)
        BY <3>3 DEF Phase2a
      <4>2. \E Q \in Quorums, S \in SUBSET {m \in sent : (m.type = "1b") /\ (m.bal = b)} :
              \A a \in Q : \E m \in S : m.acc = a
        BY <3>3 DEF Phase2a
      <4>3. \A m \in sent' \ sent: m.type = "2a" BY <3>3 DEF Send, Phase2a
      <4>6. \A m,ma \in sent' : m.type = "2a" /\ ma.type = "2a" /\ ma.bal = m.bal
                                => ma = m
        BY <4>1, Isa DEF MsgInv
      <4>8. (\A m \in sent : m.type = "2b" =>
               \E m2 \in sent: m2.type = "2a" /\ m2.bal = m.bal /\ m2.val = m.val)'
        BY <4>3, \A m \in sent': sent.type = "2b" => m \in sent DEF MsgInv, TypeOK, Messages, Send
      <4>. QED
         BY QuorumAssumption, <4>3, <4>2, <4>6 DEF MsgInv, TypeOK, Messages, Send
    <3>4. ASSUME NEW a \in Acceptors, Phase2b(a)
          PROVE  MsgInv'
      <4>. PICK m \in sent : Phase2b(a)!(m)
        BY <3>4 DEF Phase2b
      <4>1. \A aa, vv, bb : VotedForIn(aa,vv,bb) => VotedForIn(aa,vv,bb)'
        BY DEF VotedForIn, Send
      <4>2. \A mm \in sent : mm.type = "1b"
               => \A v \in Values, c \in (mm.maxVBal+1) .. (mm.bal-1) :
                     ~ VotedForIn(mm.acc, v, c) => ~ VotedForIn(mm.acc, v, c)'
        BY DEF Send, VotedForIn, MsgInv, TypeOK, Messages
      <4>. QED
        BY <4>1, <4>2, <2>1 DEF MsgInv, Send, TypeOK, Messages
    <3>5. QED
      BY <3>1, <3>2, <3>3, <3>4 DEF Next
  <2>4. QED
    BY <2>1, <2>3 DEF Inv
*)
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Consistent == Spec => []Consistency
BY Invariant, Consistent4, PTL DEF Ballots
=============================================================================
\* Modification History
\* Last modified Tue Nov 21 19:12:25 EST 2017 by saksh
\* Last modified Fri Nov 28 10:39:17 PST 2014 by lamport
\* Last modified Sun Nov 23 14:45:09 PST 2014 by lamport
\* Last modified Mon Nov 24 02:03:02 CET 2014 by merz
\* Last modified Sat Nov 22 12:04:19 CET 2014 by merz
\* Last modified Fri Nov 21 17:40:41 PST 2014 by lamport
\* Last modified Tue Mar 18 11:37:57 CET 2014 by doligez
\* Last modified Sat Nov 24 18:53:09 GMT-03:00 2012 by merz
\* Created Sat Nov 17 16:02:06 PST 2012 by lamport
