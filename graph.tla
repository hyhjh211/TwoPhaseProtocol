------------------------------- MODULE graph -------------------------------
EXTENDS Integers,
         Sequences, TLC, FiniteSets
CONSTANT NODES  \* The set of nodes in the system

VARIABLES
  rmState,       \* rmState[r, transcationNumber] is the state of node r for transcation transcationNumber.
  tmState,       \* The state of the leader.
  tmPrepared,    \* The set of nodes from which the leader has received "Prepared"
                 \* messages.
  leaders,        \* leaders[transcationNumber] is the leader in the system for transcation transcationNumber.
  msgs,
  localTransactionHistory,\*  localTransactionHistory[nodes] is the transcation history graph for the corresponding node 
  transactionNumbers \* all transcations happened in the system
 

\*msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r]}

GRAPHTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [NODES -> {"working", "prepared", "committed", "aborted"}]
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
  [type : {"Prepared"}, prepareN:  transactionNumbers, dependency : SUBSET transactionNumbers,  rm : NODES ]  \cup  [type : {"Commit", "Abort"}, tn: transactionNumbers]
  \cup [type : {"Prepared"}, prepareN:  transactionNumbers, dependency : SUBSET transactionNumbers,  leader : NODES]
  
  GraphInit ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [r \in NODES, y \in Int |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared   = {}
  /\ msgs = {}
  
  ParticipantPrepare(r, prepareInfo, depdencyInfo) == 
  (*************************************************************************)
  (* participant r send prepare message                                    *)
  (*************************************************************************)
  /\ rmState[r, prepareInfo] = "working"
  /\ rmState' = [rmState EXCEPT ![r, prepareInfo] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r]}
  
  /\ UNCHANGED <<tmState, tmPrepared, transactionNumbers>>
  
  
 LeaderPrepare(prepareInfo, depdencyInfo) == 
  (*************************************************************************)
  (* leader send prepare message                                    *)
  (*************************************************************************)
  /\ tmState = "working"
  /\ tmState' = "prepared"
  /\ transactionNumbers' = <<Head(transactionNumbers) + 1>> \o transactionNumbers
  /\ msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, leadr |-> 0]}
  /\ UNCHANGED <<rmState, tmPrepared, transactionNumbers>>
  
  
  
  ParticipantChooseToAbort(r, abortInfo) ==
  (*************************************************************************)
  (* node r spontaneously decides to abort.  As noted above, r *)
  (* does not send any message in our simplified spec.                     *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r, abortInfo] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>
=============================================================================
\* Modification History
\* Last modified Thu Feb 20 14:41:51 CST 2025 by junhaohu
\* Created Sun Feb 16 22:23:24 CST 2025 by junhaohu
