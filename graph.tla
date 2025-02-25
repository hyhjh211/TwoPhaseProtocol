------------------------------- MODULE graph -------------------------------
EXTENDS Integers,
         Sequences, TLC, FiniteSets
CONSTANT NODES  \* The set of nodes in the system

VARIABLES
  rmState,       \* rmState[r, transactionNumber] is the state of node r for transcation transactionNumber.

  msgs,
  localTransactionHistory,\*  localTransactionHistory[nodes] is the transcation history graph for the corresponding node 
                          \* localTransactionHistory[nodes][transactionNumber]["committed"] is the set of local committed transactions
                          \* localTransactionHistory[nodes][transactionNumber]["prepared"]is the set of local prepared transactions
  transactionNumbers \* all transcations happened in the system
 

\*msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r]}

GRAPHTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [transactionNumbers -> [NODES -> {"follower", "leader"}]]
 GRAPHConsistency ==
  (*************************************************************************)
  (* A state predicate asserting that two nodes have not arrived at          *)
  (* conflicting decisions.  It is an invariant of the specification.      *)
  (*************************************************************************)
\*  \A r1, r2 \in NODES, t \in transactionNumbers : ~ /\ rmState[r1, transactionNumbers] = "aborted"
\*                       /\ rmState[r2, transactionNumbers] = "committed"
\*  




\*    IF \E r \in NODES, t \in transactionNumbers: rmState[r, t] = "committed" 
\*        THEN
\*        Cardinality({r \in NODES : rmState[r, t] = "committed"}) > Cardinality(NODES) \div 2
\*        ELSE
\*        FALSE


\*
\*  LET hasCommitted == \E t \in transactionNumbers : \E r \in NODES : rmState[r, t] = "committed"
\*  IN
\*    IF hasCommitted
\*    THEN \E t \in transactionNumbers : Cardinality({r \in NODES : rmState[r, t] = "committed"}) > Cardinality(NODES) \div 2
\*    ELSE FALSE


  
     \A r \in NODES, t \in transactionNumbers: rmState[r, t] = "committed"  => Cardinality({rr \in NODES : rmState[rr, t] = "committed"}) > Cardinality(NODES) \div 2
 Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the node indicated by the message's rm field to the leader.       *)
  (* Messages of type "Commit" and "Abort" are broadcast by the corresponding leader, to be  *)
  (* received by all nodes.  The set msgs contains just a single copy of     *)
  (* such a message.                                                       *)
  (*************************************************************************)
  [type : {"responsePhase2"}, prepareN:  transactionNumbers, dependency : SUBSET transactionNumbers,  rm : NODES, val:{"prepared", "aborted"} ]  \cup  [type : {"Commit", "Abort"}, tn: transactionNumbers]
  \cup [type : {"Prepared"}, prepareN:  transactionNumbers, dependency : SUBSET transactionNumbers,  leader : NODES]
  \cup [type: {"aborted"}, tn : transactionNumbers]
  \cup [type: {"committed"}, tn: transactionNumbers]
  
  GraphInit ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [r \in NODES, y \in Int |-> "follower"]
  /\ msgs = {}
  
  ParticipantPrepare(r, prepareInfo, depdencyInfo) == 
  (*************************************************************************)
  (* participant r send prepare message                                    *)
  (*************************************************************************)
  /\ rmState[r, prepareInfo] = "working"
  /\ rmState' = [rmState EXCEPT ![r, prepareInfo] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "responsePhase2", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r, val |-> "prepared"]}
  
  /\ UNCHANGED <<transactionNumbers>>
  
  
 LeaderPrepare(prepareInfo, depdencyInfo, s, r) == 
  (*************************************************************************)
  (* leader i send prepare message to follower j                           *)
  (*************************************************************************)
  /\ rmState[prepareInfo][s] = "leader"
  /\ rmState[prepareInfo][r] = "follower"
  /\ transactionNumbers' = <<Head(transactionNumbers) + 1>> \o transactionNumbers
  /\ msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, leadr |-> 0]}
  /\ UNCHANGED <<rmState>>
  
  
  
  ParticipantChooseToAbort(r,s,abortInfo, depdencyInfo) ==
  (*************************************************************************)
  (* node r spontaneously decides to abort.                                *)
  (*************************************************************************)
  /\ rmState[abortInfo][s] = "follower"
  /\ rmState[abortInfo][r] = "leader"
  /\ msgs' = msgs \cup {[type |-> "responsePhase2", prepareN |->abortInfo, dependency |-> depdencyInfo, rm |-> r, val |-> "aborted"]}
  /\ UNCHANGED << rmState>>
  
  
  
  ParticipantRecvPhase1(r, s, tnInfo, depdencyInfo) == 
  (*************************************************************************)
  (* node r receive message from leader s                                  *)
  (*************************************************************************)
  IF depdencyInfo \subseteq localTransactionHistory[r]["committed"] \cup localTransactionHistory[r]["prepared"]
  THEN
     ParticipantPrepare(r, tnInfo, depdencyInfo)
  ELSE
     ParticipantChooseToAbort(r, s, tnInfo, depdencyInfo)
  
  
  ParticipantRecvAbort(r, s, tnInfo, depdencyInfo) ==
   /\ rmState[tnInfo][r] = "follower"
   /\ rmState[tnInfo][s] = "leader"
   /\ localTransactionHistory[r]["prepared"]' = localTransactionHistory[r]["prepared"] \ {tnInfo}
  
  
  ParticipantRcvCommittMsg(r, s, tnInfo) == 
  /\ rmState[tnInfo][r] = "follower"
  /\ rmState[tnInfo][s] = "leader"
  /\ localTransactionHistory[r]["prepared"]' =  localTransactionHistory[r]["prepared"] \ {tnInfo}
  /\ localTransactionHistory[r]["committed"]' = localTransactionHistory[r]["committed"] \cup {tnInfo}
\*  /\ UNCHANGED <<tmState, 
  
\*  ParticipantRecvPhase2(r, tn) == 
  
  
  
=============================================================================
\* Modification History
\* Last modified Tue Feb 25 23:41:54 CST 2025 by junhaohu
\* Created Sun Feb 16 22:23:24 CST 2025 by junhaohu
