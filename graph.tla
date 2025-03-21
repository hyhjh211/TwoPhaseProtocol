------------------------------- MODULE graph -------------------------------
EXTENDS Integers,
         Sequences, TLC, FiniteSets
CONSTANT NODES,  \* The set of nodes in the system,
        transactionNumbers, \* all transcations happened in the system
        transactionsDependency \* all transcations happened in the system

VARIABLES
  rmState,       \* rmState[r, transactionNumber] is the state of node r for transcation transactionNumber "leader" or "follower".

  msgs,
  localTransactionHistory,\*  localTransactionHistory[nodes] is the transcation history graph for the corresponding node 
                          \* localTransactionHistory[nodes]["committed"] is the set of local committed transactions
                          \* localTransactionHistory[nodes]["prepared"]is the set of local prepared transactions
  
  localNodesGraph \* localNodesGraph[nodes] is a graph

\*msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r]}


Vertex == [NodeID|-> Int, neighbours |->{}]
Graph == {Vertex}
   


OperationSet == 
   [Type: "edges", Operation: {"add", "remove"}, sourceVertex: Int, desVertex: Int] \cup 
   [Type: "nodes", Operation: {"add", "remove"}, sourceVertex: Int]



GRAPHTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [transactionNumbers -> [NODES -> {"follower", "leader"}]]
 GRAPHConsistency ==
  (*************************************************************************)
  (* A state predicate asserting that two nodes have not arrived at        *)
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
  (* Messages of type "Commit" and "Abort" are sent by the corresponding leader, to be  *)
  (* received by participants.  The set msgs contains just a single copy of     *)
  (* such a message.                                                       *)
  (*************************************************************************)
  [type : {"responsePhase2"}, prepareN:  transactionNumbers, dependency : SUBSET transactionNumbers,  rm : NODES, val:{"prepared", "aborted"} ]  \cup  [type : {"Commit", "Abort"}, tn: transactionNumbers, operations: Seq(OperationSet)]
  \cup [type : {"Prepared"}, prepareN:  transactionNumbers, dependency : SUBSET transactionNumbers,  leader : NODES, operations: Seq(OperationSet)]
  \cup [type: {"aborted"}, tn : transactionNumbers, rm: NODES, operations: Seq(OperationSet)]
  \cup [type: {"committed"}, tn: transactionNumbers, rm: NODES, operations: Seq(OperationSet)]
  
  Quorum == {i \in SUBSET(NODES) : Cardinality(i) * 2 > Cardinality(NODES)}
  
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
  /\ rmState[r, prepareInfo] = "follower"
\*  /\ rmState' = [rmState EXCEPT ![r, prepareInfo] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "responsePhase2", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r, val |-> "prepared"]}
  
  /\ UNCHANGED <<transactionNumbers>>
  
  
  
  
  ApplyOp(op, G) ==
    CASE op.Type = "nodes" /\ op.Operation = "add"   -> G \union { [NodeID |-> op.sourceVertex, neighbours |-> {}]}
    [] op.type = "nodes" /\ op.Operation = "remove"   -> 
    LET 
          G1 == G \  {[NodeID |-> op.sourceVertex, neighbours |->  (CHOOSE v \in G : v[op.sourceVertex] = op.sourceVertex).neighbours]} \* Remove the node itself
\*          G2 == [ v \in DOMAIN G1 |-> v.neighbours \ {op.sourceVertex} ] \* Remove it from neighbors
          GraphWithRemovedNodes == { v \in G1 :  op.sourceVertex \in v.neighbours}
          GraphWithoutRemovedNodes == { v \in G1 :  op.sourceVertex \notin v.neighbours}
          Gtemp == { [NodeID |-> v1.NodeID, neighbours |-> v1.neighbours \ {op.sourceVertex}] : v1 \in GraphWithRemovedNodes }
          G2 == Gtemp \union GraphWithoutRemovedNodes
    IN 
          G2
    [] op.type = "edges" /\ op.Operation = "add" ->
    { v \in G : IF v.NodeID = op.sourceVertex THEN 
                               [NodeID |-> v.NodeID, neighbours |-> v.neighbours \union {op.desVertex}]
                             ELSE v }
    [] op.type = "edges" /\ op.Operation = "remove" -> 
    LET
\*        connectedNode == {CHOOSE v \in G : v[op.sourceVertex] = op.sourceVertex}
\*        G1  == G \ connectedNode
\*        G2 == G1 \union {[[NodeID |-> connectedNode.NodeID, neighbours |-> connectedNode.neighbours \ {desVertex}]}
        G1 == { v \in G : IF v.NodeID = op.sourceVertex THEN 
                               [NodeID |-> v.NodeID, neighbours |-> v.neighbours \ {op.desVertex}]
                             ELSE v }
     IN 
         G1
        
 RECURSIVE ApplyOperations(_, _, _)
 ApplyOperations(ops, nodeID, G) ==    
    IF ops = <<>> THEN G
    ELSE ApplyOperations(Tail(ops), nodeID,  ApplyOp(Head(ops),G))
    
 Apply(ops, nodeID, G) ==
 G' = ApplyOperations(ops, nodeID, G)
  
  
 LeaderPrepare(prepareInfo, depdencyInfo, s, r) == 
  (*************************************************************************)
  (* leader s send prepare message to follower r                           *)
  (*************************************************************************)
  /\ rmState[prepareInfo][s] = "leader"
  /\ rmState[prepareInfo][r] = "follower"
  /\ msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, leadr |-> 0]}
  /\ UNCHANGED <<rmState>>
  
  
  LeaderCommit(tnInfo, s, r) == 
  (*************************************************************************)
  (* leader s send prepare message to follower r                           *)
  (*************************************************************************)
  /\ rmState[tnInfo][s] = "leader"
  /\ rmState[tnInfo][r] = "follower"
  /\ {x \in NODES: tnInfo \in localTransactionHistory[x]["prepared"]} \in Quorum
  /\ msgs' = msgs \cup {[type: {"committed"}, tn: transactionNumbers, rm:r]}
  
  
  
  LeaderAbort(tnInfo, s, r) ==
  (*********************************************************************************)
  (* leader s spontaneously aborts the transaction and send the abort message to r.*)
  (*********************************************************************************)
  /\ rmState[tnInfo][s] = "leader"
  /\ rmState[tnInfo][r] = "follower"
  /\ msgs' = msgs \cup {[type: {"aborted"}, tn: transactionNumbers, rm:r]}
  
  ParticipantChooseToAbort(r,s,abortInfo, depdencyInfo) ==
  (*************************************************************************)
  (* node r spontaneously decides to abort.                                *)
  (*************************************************************************)
  /\ rmState[abortInfo][s] = "follower"
  /\ rmState[abortInfo][r] = "leader"
  /\ msgs' = msgs \cup {[type |-> "responsePhase2", prepareN |->abortInfo, dependency |-> depdencyInfo, rm |-> r, val |-> "aborted"]}
  /\ UNCHANGED << rmState>>
  
  UpdateSets(prepareSet, commitSet, depdencyInfo)  ==
  LET commonElements == prepareSet \intersect depdencyInfo
  IN
    /\ prepareSet' = prepareSet \ commonElements
    /\ commitSet' = commitSet \union commonElements
  
  ParticipantRecvPhase1(r, s, tnInfo, depdencyInfo, operations) == 
  (*************************************************************************)
  (* node r receive message from leader s                                  *)
  (*************************************************************************)
  IF depdencyInfo \subseteq localTransactionHistory[r]["committed"] \cup localTransactionHistory[r]["prepared"]
  THEN
     LET 
        targetNodes == {op.sourceVertex : op \in operations}
     IN
     /\ UpdateSets(localTransactionHistory[r]["prepared"],localTransactionHistory[r]["committed"], depdencyInfo)
     /\ ParticipantPrepare(r, tnInfo, depdencyInfo)
  ELSE
     ParticipantChooseToAbort(r, s, tnInfo, depdencyInfo)
  
  
  ParticipantRecvAbort(r, s, tnInfo, depdencyInfo) ==
   /\ rmState[tnInfo][r] = "follower"
   /\ rmState[tnInfo][s] = "leader"
   /\ [type |-> "aborted", tn |-> tnInfo, rm |-> r] \in msgs
   /\ localTransactionHistory[r]["prepared"]' = localTransactionHistory[r]["prepared"] \ {tnInfo}
  
  
  ParticipantRcvCommittMsg(r, s, tnInfo, operations) == 
  /\ rmState[tnInfo][r] = "follower"
  /\ rmState[tnInfo][s] = "leader"
  /\ [type |-> "committed", tn |-> tnInfo, rm |-> r] \in msgs
  /\ localTransactionHistory[r]["prepared"]' =  localTransactionHistory[r]["prepared"] \ {tnInfo}
  /\ localTransactionHistory[r]["committed"]' = localTransactionHistory[r]["committed"] \cup {tnInfo}
  /\ Apply(operations, r, localNodesGraph[r])
\*  /\ UNCHANGED <<tmState, 


  ClientRequest(i, tnInfo, depdencyInfo) == 
  /\ rmState[tnInfo][i] = "follower"
  /\ rmState[tnInfo][i]'= "leader"
  
 




  
  
    
\*  ParticipantRecvPhase2(r, tn) == 
  
  
  
=============================================================================
\* Modification History
\* Last modified Fri Mar 21 11:26:52 CST 2025 by junhaohu
\* Created Sun Feb 16 22:23:24 CST 2025 by junhaohu
