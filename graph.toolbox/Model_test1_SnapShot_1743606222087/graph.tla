------------------------------- MODULE graph -------------------------------
EXTENDS Integers,
         Sequences, TLC, FiniteSets
CONSTANT NODES,  \* The set of nodes in the system,
        transactionNumbers, \* all transcations happened in the system
        transactions \* transactions[transactionNumber] is the set of operations for transaction identified by transactionNumber 

VARIABLES
  rmState,       \* rmState[r, transactionNumber] is the state of node r for transcation transactionNumber "leader" or "follower".

  msgs,
  clientRequests, \* clientRequests[r] is the set of requests coming from a clietn at node r
  localTransactionHistory,\*  localTransactionHistory[nodes] is the transcation history graph for the corresponding node 
                          \* localTransactionHistory[nodes]["committed"] is the set of local committed transactions
                           \* localTransactionHistory[nodes]["recentCommitted"] is the set of most recent local committed transactions
                          \* localTransactionHistory[nodes]["prepared"]is the set of local prepared transactions
  
  localNodesGraph, \* localNodesGraph[nodes] is a graph
  transactionOperation, \* transactionOperation[transactionNumber].op is the set of operations associated with the transaction identified by transactionNumber 
                       \* transactionOperation[transactionNumber].dependency is the recorded dependency information
                     
  acceptedTransactions, \* acceptedTransactions[tn] is the set of nodes that have sent accept for transaction tn
  rejectedTransactions,  \* rejectedTransactions[tn] is the set of nodes that have sent reject for transaction tn
  pendingTransactions \* set of transactions to be executed 
  
\*msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r]}


Vertex == [NodeID|-> Int, neighbours |->{}]
Graph == {Vertex}
   


OperationSet == 
   [type: "edges", Operation: {"add", "remove"}, sourceVertex: Int, desVertex: Int] \cup 
   [type: "nodes", Operation: {"add", "remove"}, sourceVertex: Int]



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
  [type : {"preparedResponsePhase1", "abortedResponsePhase1"}, tn:  transactionNumbers, src : NODES, dst : NODES, operations: Seq(OperationSet)]  
  \cup [type : {"prepared"}, tn:  transactionNumbers, dependency : SUBSET transactionNumbers, src: NODES, dst: NODES, operations: Seq(OperationSet)]
  \cup [type: {"aborted", "committed"}, tn : transactionNumbers, dependency : SUBSET transactionNumbers, src: NODES, dst: NODES, operations: Seq(OperationSet)]
  \cup [type: {"clientRequest"}, tn: transactionNumbers, operations: Seq(OperationSet) ]
  
  
  
  
  
  Quorum == {i \in SUBSET(NODES) : Cardinality(i) * 2 > Cardinality(NODES)}
  
  
  
  

  
  
  ParticipantPrepare(r, s, tnInfo, depdencyInfo) == 
  (*************************************************************************)
  (* participant s sends prepare message                                    *)
  (*************************************************************************)
  /\ rmState[s, tnInfo] = "follower"
\*  /\ rmState' = [rmState EXCEPT ![r, prepareInfo] = "prepared"]
  /\ msgs[r][s]' = Append(msgs[r][s], [type |-> "preparedResponsePhase1", tn |->tnInfo, rm |-> r])
  
  /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, localTransactionHistory, localNodesGraph, transactionOperation, 
    acceptedTransactions, rejectedTransactions, pendingTransactions>>
  
  
  
  
  
  
  
  ApplyOp(op, G) ==
    CASE op.type = "nodes" /\ op.Operation = "add"   -> G \union { [NodeID |-> op.sourceVertex, neighbours |-> {}]}
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
    LET 
        addEdge(v) == 
            IF v.NodeID = op.sourceVertex THEN 
                    [NodeID |-> v.NodeID, neighbours |-> v.neighbours \union {op.desVertex}]
                ELSE IF v.NodeID = op.desVertex THEN             
                    [NodeID |-> v.NodeID, neighbours |-> v.neighbours \union {op.sourceVertex}]
                ELSE v
    IN
    {addEdge(v) : v \in G}
    [] op.type = "edges" /\ op.Operation = "remove" -> 
    LET
        removeEdge(v) ==
            IF v.NodeID = op.sourceVertex THEN 
                               [NodeID |-> v.NodeID, neighbours |-> v.neighbours \ {op.desVertex}]
                          ELSE IF v.NodeID = op.desVertex THEN
                               [NodeID |-> v.NodeID, neighbours |-> v.neighbours \ {op.sourceVertex}]
                             ELSE v
\*        connectedNode == {CHOOSE v \in G : v[op.sourceVertex] = op.sourceVertex}
\*        G1  == G \ connectedNode
\*        G2 == G1 \union {[[NodeID |-> connectedNode.NodeID, neighbours |-> connectedNode.neighbours \ {desVertex}]}
        
     IN 
         { removeEdge(v): v \in G }
        
 RECURSIVE ApplyOperations(_, _, _)
 ApplyOperations(ops, nodeID, G) ==    
    IF ops = <<>> THEN G
    ELSE ApplyOperations(Tail(ops), nodeID,  ApplyOp(Head(ops),G))
    
 Apply(ops, nodeID, G) ==
  ApplyOperations(ops, nodeID, G)
  
  
 LeaderPrepare(tnInfo, s, r, depdencyInfo, tnOperations) == 
  (*************************************************************************)
  (* leader s sends prepare message to follower r                           *)
  (*************************************************************************)
  IF s # r
  THEN 
  /\ rmState[tnInfo, s] = "leader"
  /\ rmState[tnInfo, r] = "follower" 
  /\ transactionOperation' = [transactionOperation EXCEPT ![tnInfo] = [op |-> tnOperations, dependency |-> depdencyInfo]]
  /\ msgs' = [msgs EXCEPT! [r][s] = Append(msgs[r][s], [type |-> "prepared", tn |->tnInfo, dependency |-> depdencyInfo, src |-> s, dst |-> r, operations |-> tnOperations])]
  ELSE
  /\ rmState[tnInfo, s] = "leader"
  /\ rmState[tnInfo, r] = "leader"

  
  LeaderSendPrepares(tnInfo, s, tnOperations) ==
  (*************************************************************************)
  (* leader s sends prepare message to all followers                        *)
  (*************************************************************************) 
  /\ rmState[tnInfo, s] = "leader"
  /\ \A r \in NODES : LeaderPrepare(tnInfo, s, r, localTransactionHistory[s]["recentCommitted"] , tnOperations)
  /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, localTransactionHistory, localNodesGraph, 
    acceptedTransactions, rejectedTransactions, pendingTransactions>>
  
  
  
  LeaderCommit(tnInfo, r, s, depdencyInfo, tnOperations) == 
  (*************************************************************************)
  (* leader s sends prepare message to follower r                           *)
  (*************************************************************************)
  /\ rmState[tnInfo, s] = "leader"
  /\ rmState[tnInfo, r] = "follower"
\*  /\ {x \in NODES: tnInfo \in localTransactionHistory[x]["prepared"]} \in Quorum
  /\ msgs[r][s]' = Append(msgs[r][s], [type |-> "committed", tn |-> tnInfo, dependency |-> depdencyInfo, src |-> s, dst |-> r, operations |-> tnOperations])
  
  
  LeaderSendCommit(tnInfo, s, depdencyInfo, tnOperations) == 
  (*************************************************************************)
  (* leader s sends commit message to all followers                         *)
  (*************************************************************************) 
  /\ rmState[tnInfo, s] = "leader"
  /\ \A r \in NODES : LeaderCommit(tnInfo, r, s, depdencyInfo , tnOperations)
  /\ UNCHANGED <<rmState, transactionNumbers, clientRequests, localTransactionHistory, localNodesGraph, 
    acceptedTransactions, rejectedTransactions, pendingTransactions>>
  
  
  
  LeaderAbort(tnInfo, r, s, depdencyInfo, tnOperations) ==
  (*********************************************************************************)
  (* leader s spontaneously aborts the transaction and send the abort message to r.*)
  (*********************************************************************************)
  /\ rmState[tnInfo, s] = "leader"
  /\ rmState[tnInfo, r] = "follower"
  /\ msgs[r][s]' = Append(msgs[r][s], [type |-> "aborted", tn|-> tnInfo, src |-> s, dst |-> r, operations |-> tnOperations])
  
  
  LeaderSendAbort(tnInfo, s, depdencyInfo, tnOperations) ==
  /\ rmState[tnInfo][s] = "leader"
  /\ \A r \in NODES : LeaderAbort(tnInfo, r, s, depdencyInfo , tnOperations)
  /\ UNCHANGED <<rmState, transactionNumbers, clientRequests, localTransactionHistory, localNodesGraph, 
    acceptedTransactions, rejectedTransactions, pendingTransactions>>
  
  ParticipantChooseToAbort(tnInfo, r, s, depdencyInfo, tnOperations) ==
  (*************************************************************************)
  (* node s spontaneously decides to abort.                                *)
  (*************************************************************************)
  /\ rmState[tnInfo, s] = "follower"
  /\ rmState[tnInfo, r] = "leader"
  /\ msgs[r][s]' = Append(msgs[r][s], [type |-> "abortedResponsePhase1", tn |->tnInfo, src |-> s, dst |-> r, operations |-> tnOperations])
  /\ UNCHANGED <<rmState, transactionNumbers, clientRequests, localTransactionHistory, localNodesGraph, 
    acceptedTransactions, rejectedTransactions, pendingTransactions>>
  
  UpdateSets(prepareSet, commitSet, depdencyInfo)  ==
  LET commonElements == prepareSet \intersect depdencyInfo
  IN
    /\ prepareSet' = prepareSet \ commonElements
    /\ commitSet' = commitSet \union commonElements
  
  
  ConflictDetect(tnInfo, i, tnOperations) ==
    LET 
      targetNodes == {op.sourceVertex : op \in tnOperations}
      preparedTx == localTransactionHistory[i]["prepared"]
      f(x) == {transactionOperation[x].op[j].sourceVertex : j \in 1..Len(transactionOperation[x].op)}
      operatedNodes == { f(x) : x \in preparedTx }
      hasIntersection == \E x \in operatedNodes : targetNodes \cap x # {}
      
\*      operatedNodes == 
            
    IN
      hasIntersection
  
  strictSubset(depdencyInfo, nodeID) == 
    depdencyInfo \subseteq localTransactionHistory[nodeID]["recentCommitted"] /\  ~(depdencyInfo = localTransactionHistory[nodeID]["recentCommitted"])
  
  ParticipantRecvPhase1(tnInfo, r, s, depdencyInfo, tnOperations) == 
  (*************************************************************************)
  (* node r receives message from leader s                                  *)
  (*************************************************************************)
  IF depdencyInfo \subseteq localTransactionHistory[r]["committed"] \cup localTransactionHistory[r]["prepared"]
     /\ ~ConflictDetect(tnInfo, r, tnOperations) /\ ~(strictSubset(depdencyInfo, r))
      THEN
         /\ UpdateSets(localTransactionHistory[r]["prepared"],localTransactionHistory[r]["committed"], depdencyInfo)
         /\ ParticipantPrepare(r, s, tnInfo, depdencyInfo)
      ELSE
         ParticipantChooseToAbort(r, s, tnInfo, depdencyInfo, tnOperations)
  
  
  ParticipantRecvAbortMsg(r, s, tnInfo, tnOperations) ==
   /\ rmState[tnInfo][r] = "follower"
   /\ rmState[tnInfo][s] = "leader"
\*   /\ [type |-> "aborted", tn |-> tnInfo, src |-> s, dst |-> r, operations |-> tnOperations ] \in msgs[r]
   /\ localTransactionHistory[r]["prepared"]' = localTransactionHistory[r]["prepared"] \ {tnInfo}
   /\ UNCHANGED <<rmState, transactionNumbers, clientRequests, localNodesGraph, 
    acceptedTransactions, rejectedTransactions, pendingTransactions>>
  
  
  ParticipantRcvCommitMsg(r, s, tnInfo, depdencyInfo, tnOperations) == 
  /\ rmState[tnInfo][r] = "follower"
  /\ rmState[tnInfo][s] = "leader"
\*  /\ [type |-> "committed",tn |-> tnInfo, src |-> s, dst |-> r, operations |-> tnOperations] \in msgs[r]
  /\ localTransactionHistory[r]["prepared"]' =  localTransactionHistory[r]["prepared"] \ {tnInfo}
  /\ localTransactionHistory[r]["committed"]' = localTransactionHistory[r]["committed"] \cup {tnInfo}
  /\ localTransactionHistory[r]["recentCommitted"]' = (localTransactionHistory[r]["recentCommitted"] \ depdencyInfo) \union tnInfo
  /\ localNodesGraph[r]' = Apply(tnOperations, r, localNodesGraph[r])
  /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, 
    acceptedTransactions, rejectedTransactions, pendingTransactions>>
\*  /\ UNCHANGED <<tmState, 

  LeaderHandleParticipantRes(tnInfo, r, s, msg) ==
    /\ rmState[tnInfo][r] = "leader" 
    /\ IF Len(acceptedTransactions[tnInfo]) + Len(rejectedTransactions[tnInfo] + 1) = Cardinality(NODES)
        THEN
          IF (Len(acceptedTransactions[tnInfo]) + 1) * 2 > Cardinality(NODES)
           THEN 
                LeaderSendCommit(tnInfo, r, transactionOperation[tnInfo].dependency, transactionOperation[tnInfo].op)
           ELSE 
                LeaderSendAbort(tnInfo, r, transactionOperation[tnInfo].dependency, transactionOperation[tnInfo].op)    
        ELSE 
           IF msg.type = "preparedResponsePhase1" 
                THEN       
                    /\ acceptedTransactions[tnInfo]' = Append(acceptedTransactions[tnInfo], s)
                    /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, localTransactionHistory, localNodesGraph, transactionOperation, 
                        rejectedTransactions, pendingTransactions>>
                    
                ELSE
                    /\ rejectedTransactions[tnInfo]' = Append(rejectedTransactions[tnInfo], s)
                    /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, localTransactionHistory, localNodesGraph, transactionOperation, 
                        acceptedTransactions, pendingTransactions>>
            
       
            
            
\*    /\ \E MS \in Quorum :    
\*            /\ \A ac \in MS : 
\*                \E msg \in msgs[ac][r]:
\*                    /\ msg.type = "preparedResponsePhase1"
\*                    /\ msg.tn = tnInfo
\*                    /\ msg.src = ac
\*                    /\ msg.dst = r
\*                    /\ msg.operations = transactionOperation[tnInfo].op
\*             
\*            /\ LeaderSendCommit(tnInfo, r, transactionOperation[tnInfo].dependency, transactionOperation[tnInfo].op)
            
  
  ClientRequest(i) == 
\*  LET 
\*    setNodes == [n \in NODES |-> IF n = i THEN "leader" ELSE "follower"]
\*  IN
\*    rmState[tnInfo]' = setNodes
    LET 
       nextExecuteTx == Head(pendingTransactions)
    IN
    /\ Len(pendingTransactions) > 0
    /\ rmState' = [rmState EXCEPT ![nextExecuteTx,i] = "leader"]
    /\ clientRequests' = [clientRequests EXCEPT ![i] = Append(clientRequests[i], nextExecuteTx)]
    /\ pendingTransactions' = Tail(pendingTransactions)
    /\ UNCHANGED <<transactionNumbers, msgs, localTransactionHistory, 
        localNodesGraph, transactionOperation, acceptedTransactions, rejectedTransactions>>
    
    
  Receive(r, s) == 
   /\ Len(msgs[r][s]) > 0
   /\
     \/ 
       /\ Head(msgs[r][s]).type = "prepared" 
    \*      (tnInfo, r, s, depdencyInfo, tnOperations)
       /\ ParticipantRecvPhase1(msgs[r][s].tn, r, s, msgs.dependency, msgs.operations)
     \/
       /\ (Head(msgs[r][s]).type = "preparedResponsePhase1" \/ Head(msgs[r][s]).type = "abortedResponsePhase1")
       /\ LeaderHandleParticipantRes(msgs[r][s].tn, r, s, msgs[r][s])
         
   /\ msgs[r][s]' = Tail(msgs[r][s])
   
   
  
  ReceiveClient(i) ==
    LET 
        clientRequest == Head(clientRequests[i])
    IN
        /\ Len(clientRequests[i]) > 0
        /\ LeaderSendPrepares(clientRequest, i, transactions[clientRequest])

        /\ clientRequests' = [clientRequests EXCEPT ![i] = Tail(clientRequests[i])]

       /\ UNCHANGED <<transactionNumbers, msgs, localTransactionHistory, 
        localNodesGraph, transactionOperation, acceptedTransactions, rejectedTransactions, pendingTransactions, rmState>>
           
        
        
 Init ==   
   LET 
        tSet == { transactionNumbers[i] : i \in DOMAIN transactionNumbers }
   IN 
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [r \in tSet, y \in NODES |-> "follower"]
  /\ msgs = [r \in NODES |-> [s \in NODES |-> <<>>]]
  /\ transactionOperation = [tn \in tSet |-> [op |-> <<>>, dependency |-> {}]]
  /\ pendingTransactions = transactionNumbers
  /\ clientRequests = [r \in NODES |-> <<>>]
  /\ localNodesGraph = [r \in NODES |-> {}]
  /\ localTransactionHistory = [r \in NODES |-> 
        [ 
            i \in {"committed","recentCommitted","prepared" } |-> {}
        ]
    ]
  /\ acceptedTransactions = [tn \in tSet |-> {}]
  /\ rejectedTransactions = [tn \in tSet |-> {}]
  
  Next ==
\*      \/ \E i,j \in NODES : Receive(i, j)
      \/ \E i \in NODES : ClientRequest(i)
\*      \/ \E i \in NODES : ReceiveClient(i)
         
      
  
 




  
  
    
\*  ParticipantRecvPhase2(r, tn) == 
  
  
  
=============================================================================
\* Modification History
\* Last modified Wed Apr 02 23:03:36 CST 2025 by junhaohu
\* Created Sun Feb 16 22:23:24 CST 2025 by junhaohu