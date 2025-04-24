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
                     
  acceptedTransactions, \* acceptedTransactions[tn] is the set of nodes that have sent accept for transaction tn
  rejectedTransactions,  \* rejectedTransactions[tn] is the set of nodes that have sent reject for transaction tn
  pendingTransactions, \* set of transactions to be executed 
  tnState,
  test

  
\*msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r]}


Vertex == [NodeID|-> Int, neighbours |->{}]
Graph == {Vertex}
   
   
   
   
   
   
ValidMessage ==
    { m \in DOMAIN msgs : msgs[m] > 0 }

WithMessage(m, messages) ==
    IF m \in DOMAIN msgs THEN
        [messages EXCEPT ![m] = messages[m] + 1]
    ELSE
        messages @@ (m :> 1)
    
Send(m) == msgs' = WithMessage(m, msgs)



ExistMsg(r, msgType) ==
    Cardinality({m \in ValidMessage: m.dst = r /\ m.type = msgType})




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


  
     \A r \in NODES, t \in transactionNumbers: rmState[r, t] = "committed"  => Cardinality({rr \in NODES : rmState[rr, t] = "committed"}) > Cardinality(NODES) \div 2
     
     
 TnStateInvariant ==
  \A r \in transactionNumbers:
    \A t \in NODES:
      tnState[r][t] \in {"unknown", "sendCommit", "sendAbort", "sendPrepared", "sendPreparedResponsePhase1", "sendAbortedResponsePhase1", "aborted", "committed"}    
     
     
     
 Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the node indicated by the message's rm field to the leader.       *)
  (* Messages of type "Commit" and "Abort" are sent by the corresponding leader, to be  *)
  (* received by participants.  The set msgs contains just a single copy of     *)
  (* such a message.                                                       *)
  (*************************************************************************)
  [type : {"preparedResponsePhase1", "abortedResponsePhase1", "prepared","aborted", "committed"}, tn:  transactionNumbers, dependency : SUBSET transactionNumbers, src : NODES, dst : NODES, operations: Seq(OperationSet)]  
  \cup [type: {"clientRequest"}, tn: transactionNumbers, operations: Seq(OperationSet) ]
  
  
  
  
  
  Quorum == {i \in SUBSET(NODES) : Cardinality(i) * 2 > Cardinality(NODES)}
  
  
  
  
  
  
  
  ApplyOp(op, G) ==
    CASE op.type = "nodes" /\ op.Operation = "add"   -> G \union { [NodeID |-> op.sourceVertex, neighbours |-> {}]}
    [] op.type = "nodes" /\ op.Operation = "remove"   -> 
    LET 
          G1 == G \  {[NodeID |-> op.sourceVertex, neighbours |->  (CHOOSE v \in G : v.NodeID = op.sourceVertex).neighbours]} \* Remove the node itself
\*          G2 == [ v \in DOMAIN G1 |-> v.neighbours \ {op.sourceVertex} ] \* Remove it from neighbors
          GraphWithRemovedNodes == { v \in G1 :  op.sourceVertex \in v.neighbours}
          GraphWithoutRemovedNodes == { v \in G1 :  op.sourceVertex \notin v.neighbours}
          Gtemp == { [NodeID |-> v1.NodeID, neighbours |-> v1.neighbours \ {op.sourceVertex}] : v1 \in GraphWithRemovedNodes }
          G2 == Gtemp \union GraphWithoutRemovedNodes
    IN  
          IF Cardinality({v \in G : v.NodeID = op.sourceVertex}) > 0 
          THEN G2
          ELSE G
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
  
  
\* LeaderPrepare(tnInfo, s, r, depdencyInfo, tnOperations) == 
\*  (*************************************************************************)
\*  (* leader s sends prepare message to follower r                           *)
\*  (*************************************************************************)
\*  /\ rmState[tnInfo, s] = "leader"
\*  /\ rmState[tnInfo, r] = "follower" 
\*  /\ Len(msgs[r][s]) \geq 0
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(@, [type |-> "prepared", tn |->tnInfo, dependency |-> depdencyInfo, src |-> s, dst |-> r, operations |-> tnOperations])]
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(msgs[r][s], "aaa")]

 
  LeaderSendPrepares(tnInfo, s, tnOperations) ==
  (*************************************************************************)
  (* leader s sends prepare message to all followers                       *)
  (*************************************************************************) 
        /\ rmState[tnInfo, s] = "leader"
        /\ Send([type |-> "prepared", 
                tn |->tnInfo, 
                dependency |-> localTransactionHistory[s]["recentCommitted"], 
                src |-> s, 
                dst |-> -1, 
                operations |-> tnOperations])
        /\ tnState' = [tnState EXCEPT ![tnInfo, s] = "sendPrepared"]
        

  
  
  
\*  LeaderCommit(tnInfo, r, s, depdencyInfo, tnOperations) == 
\*  (*************************************************************************)
\*  (* leader s sends commit message to follower r                           *)
\*  (*************************************************************************)
\*  /\ rmState[tnInfo, s] = "leader"
\*  /\ rmState[tnInfo, r] = "follower"
\*\*  /\ {x \in NODES: tnInfo \in localTransactionHistory[x]["prepared"]} \in Quorum
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(msgs[r][s], [type |-> "committed", tn |-> tnInfo, dependency |-> depdencyInfo, src |-> s, dst |-> r, operations |-> tnOperations])]
\*  
  
  
  LeaderSendCommit(tnInfo, s, depdencyInfo, tnOperations) == 
  (*************************************************************************)
  (* leader s sends commit message to all followers                        *)
  (*************************************************************************) 
  /\ rmState[tnInfo, s] = "leader"
  /\ Send([type |-> "committed", 
            tn |-> tnInfo, 
            dependency |-> depdencyInfo, 
            src |-> s, 
            dst |-> -1, 
            operations |-> tnOperations
     ])
  /\ tnState' = [tnState EXCEPT ![tnInfo, s] = "sendCommit"]

    
  
  
  
  
  
\*  LeaderAbort(tnInfo, r, s, depdencyInfo, tnOperations) ==
\*  (*********************************************************************************)
\*  (* leader s spontaneously aborts the transaction and send the abort message to r.*)
\*  (*********************************************************************************)
\*  /\ rmState[tnInfo, s] = "leader"
\*  /\ rmState[tnInfo, r] = "follower"
\*  /\ msgs[r][s]' = Append(msgs[r][s], [type |-> "aborted", tn|-> tnInfo, src |-> s, dst |-> r, operations |-> tnOperations])
  
  
  LeaderSendAbort(tnInfo, s, depdencyInfo, tnOperations) ==
  (*********************************************************************************)
  (* leader s sends the abort message to everyone.*)
  (*********************************************************************************)
  /\ rmState[tnInfo, s] = "leader"
  /\ Send([type |-> "aborted", 
           tn|-> tnInfo, 
           dependency |-> depdencyInfo, 
           src |-> s, 
           dst |-> -1, 
           operations |-> tnOperations
   ])
   /\ tnState' = [tnState EXCEPT ![tnInfo, s] = "sendAbort"]


  
  

  
  
  ConflictDetect(tnInfo, i, tnOperations) ==
    LET 
      targetNodes == {tnOperations[op].sourceVertex : op \in 1..Len(tnOperations)}
      preparedTx == localTransactionHistory[i]["prepared"]
      f(x) == {transactions[x][j].sourceVertex : j \in 1..Len(transactions[x])}
      operatedNodes == { f(x) : x \in preparedTx }
      hasIntersection == \E x \in operatedNodes : targetNodes \cap x # {}
      
\*      operatedNodes == 
        aaa == FALSE
            
    IN
      hasIntersection

        
  
  strictSubset(depdencyInfo, nodeID) == 
    depdencyInfo \subseteq localTransactionHistory[nodeID]["recentCommitted"] /\  ~(depdencyInfo = localTransactionHistory[nodeID]["recentCommitted"])
  
RecvPhase1(tnInfo, r, s, depdencyInfo, tnOperations) == 
  (*************************************************************************)
  (* node r receives message from leader s                                 *)
  (*************************************************************************)
  LET 
        commonElements == localTransactionHistory[r]["prepared"] \intersect depdencyInfo
       
  IN
      IF depdencyInfo \subseteq localTransactionHistory[r]["committed"] \cup localTransactionHistory[r]["prepared"]
         /\ ~ConflictDetect(tnInfo, r, tnOperations) /\ ~(strictSubset(depdencyInfo, r))
         
          THEN
\*             /\ rmState[tnInfo, r] = "follower"
             /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![r]["prepared"] =  (localTransactionHistory[r]["prepared"]\ commonElements) \union {tnInfo},
                                                                           ![r]["committed"] =  localTransactionHistory[r]["committed"] \union commonElements                          
                                                                                                                             ]
            
            
\*             /\ ParticipantPrepare(r, s, tnInfo, depdencyInfo)
            
            
            /\ Send([type |-> "preparedResponsePhase1",
                     tn |->  tnInfo, 
                     dependency |-> depdencyInfo, 
                     src |-> r, 
                     dst |-> s, 
                     operations |-> tnOperations
                ])
            /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "sendPreparedResponsePhase1"]
            /\ test' = test + 1
            /\ UNCHANGED <<transactionNumbers, 
            localNodesGraph, acceptedTransactions, rejectedTransactions, clientRequests, pendingTransactions, rmState>>
                
          ELSE
          
          /\ Send([type |-> "abortedResponsePhase1", 
                   tn |->  tnInfo, 
                   dependency |-> depdencyInfo, 
                   src |-> r, 
                   dst |-> s, 
                   operations |-> tnOperations
              ])
          /\ tnState' = [tnState EXCEPT ![tnInfo, s] = "sendAbortedResponsePhase1"]
          /\ test' = test + 1
          /\ UNCHANGED <<transactionNumbers, 
            localNodesGraph, acceptedTransactions, rejectedTransactions, clientRequests, pendingTransactions, rmState, localTransactionHistory, test>>
               
  
  
  RcvAbortMsg(r, s, tnInfo, tnOperations) ==
  (*************************************************************************)
  (* node r receives aborted message from leader s                       *)
  (*************************************************************************)
   /\ rmState[tnInfo, s] = "leader"
   /\ localTransactionHistory' = [ localTransactionHistory EXCEPT  ![r]["prepared"] = localTransactionHistory[r]["prepared"]  \ {tnInfo}]
   /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "aborted"]
   /\ UNCHANGED <<rmState, msgs, transactionNumbers, clientRequests, localNodesGraph, 
    acceptedTransactions, rejectedTransactions, pendingTransactions, test>>
  
  
  
  RcvCommitMsg(r, s, tnInfo, depdencyInfo, tnOperations) == 
  (*************************************************************************)
  (* node r receives committed message from leader s                       *)
  (*************************************************************************)
  /\ rmState[tnInfo, s] = "leader"
  
  /\ localTransactionHistory' =  [ localTransactionHistory   EXCEPT ![r]["prepared"] = localTransactionHistory[r]["prepared"] \ {tnInfo}
                                                                           ,![r]["committed"] =  localTransactionHistory[r]["committed"] \cup {tnInfo}
                                                                           ,![r]["recentCommitted"] = (localTransactionHistory[r]["recentCommitted"] \ depdencyInfo) \union {tnInfo}]                                                                        
  /\ localNodesGraph' = [localNodesGraph EXCEPT! [r] = Apply(tnOperations, r, localNodesGraph[r])]
  /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "committed"]
  /\ UNCHANGED <<transactionNumbers, msgs, rmState, clientRequests, 
    acceptedTransactions, rejectedTransactions, pendingTransactions, test>>
\*  /\ UNCHANGED <<tmState, 



  LeaderHandleCommit(tnInfo, r, msg) ==
    /\ rmState[tnInfo, r] = "leader"             
    /\ \E MS \in Quorum :    
        LET 
            
            mset == {m \in ValidMessage : /\ m.type = "preparedResponsePhase1"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                                  /\ m.src  \in MS}
            
            
        IN  /\ \A ac \in MS : \E m \in mset : m.src = ac
            /\ LeaderSendCommit(tnInfo, r, msg.dependency, msg.operations)
     
     /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, localTransactionHistory, localNodesGraph, 
                        rejectedTransactions, pendingTransactions, acceptedTransactions, clientRequests, localNodesGraph, localTransactionHistory, pendingTransactions, rejectedTransactions, rmState, test>>
 
            
            
            
            
            
  LeaderHandleAbort(tnInfo, r, msg) ==
    /\ rmState[tnInfo, r] = "leader"             
    /\ \E MS \in Quorum :    
        LET 
            
            mset == {m \in ValidMessage : /\ m.type = "abortedResponsePhase1"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                                  /\ m.src  \in MS}
            
            
        IN  /\ \A ac \in MS : \E m \in mset : m.src = ac
            /\ LeaderSendAbort(tnInfo, r, msg.dependency, msg.operations)
     /\ test' = FALSE
     /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, localTransactionHistory, localNodesGraph, 
                        rejectedTransactions, pendingTransactions, acceptedTransactions, clientRequests, localNodesGraph, localTransactionHistory, pendingTransactions, rejectedTransactions>>           
            
       
            
            
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
            
  
    

       
\*         
\*   /\ msgs[r][s]' = Tail(msgs[r][s])
  RecvPrepared(r, msg) ==
   /\ msg.type = "prepared" 
   /\  
       \/tnState[msg.tn, r] = "unknown"
       \/tnState[msg.tn, r] = "sendPrepared"
    \*      (tnInfo, r, s, depdencyInfo, tnOperations)
   /\ RecvPhase1(msg.tn, r, msg.src, msg.dependency, msg.operations)
   
            
            
  RecvPreparedResponsePhase1(msg) ==
   /\ msg.type = "preparedResponsePhase1" 
   /\ tnState[msg.tn, msg.dst] # "sendCommit"
   /\ tnState[msg.tn, msg.dst] # "sendAbort"
   /\ tnState[msg.tn, msg.dst] # "committed"
   /\ tnState[msg.tn, msg.dst] # "aborted"
   /\ LeaderHandleCommit(msg.tn, msg.dst, msg)
   
  
  RecvAbortedResponsePhase1(msg) ==
   /\ msg.type = "abortedResponsePhase1"
   /\ tnState[msg.tn, msg.dst] = "sendPrepared"
   /\ LeaderHandleAbort(msg.tn, msg.dst, msg)
  
  
   
   
  RecvCommit(r, msg) ==
   /\ msg.type = "committed"
   /\ tnState[msg.tn, r] = "sendPreparedResponsePhase1"
   /\ RcvCommitMsg(r, msg.src, msg.tn, msg.dependency,  msg.operations)
   
   
  RecvAbort(r,msg) ==
  /\ msg.type = "aborted"
  /\ 
      \/ tnState[msg.tn, r] = "sendPreparedResponsePhase1" 
      \/ tnState[msg.tn, r] = "sendAbortedResponsePhase1"
  /\ RcvAbortMsg(r, msg.src, msg.tn, msg.operations)
   
   
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
        localNodesGraph, acceptedTransactions, rejectedTransactions, tnState, test>>
   
   
   
   
   
  ReceiveClient(i) ==
    LET 
        clientRequest == Head(clientRequests[i])
    IN
        /\ Len(clientRequests[i]) > 0
        /\ LeaderSendPrepares(clientRequest, i, transactions[clientRequest])
        /\ clientRequests' = [clientRequests EXCEPT ![i] = Tail(clientRequests[i])]
        
       /\ UNCHANGED <<transactionNumbers, localTransactionHistory, 
        localNodesGraph, acceptedTransactions, rejectedTransactions, pendingTransactions, rmState, test>>
           
        
        
 Init ==   
   LET 
        tSet == { transactionNumbers[i] : i \in DOMAIN transactionNumbers }
   IN 
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [r \in tSet, y \in NODES |-> "follower"]
  /\ msgs = [m \in {} |-> 0]
  /\ pendingTransactions = transactionNumbers
  /\ clientRequests = [r \in NODES |-> <<>>]
  /\ localNodesGraph = [r \in NODES |-> {}]
  /\ localTransactionHistory = [r \in NODES |-> 
        [
            i \in {"committed","recentCommitted","prepared" } |-> {}
        ]
    ]
  /\ acceptedTransactions = [tn \in tSet |-> <<>>]
  /\ rejectedTransactions = [tn \in tSet |-> <<>>]
  /\ tnState = [r \in tSet, t \in NODES |-> "unknown"]
  /\ test = 0
  
  
  Next ==
\*      \/ \E i,j \in NODES : Receive(i, j)


      \/ \E i \in NODES, m \in ValidMessage :  RecvPrepared(i,m)
\*      \/ \E i \in NODES, m \in ValidMessage : RecvCommit(i,m)
\*      \/ \E m \in ValidMessage : RecvPreparedResponsePhase1(m)
\*      \/ \E m \in ValidMessage : RecvAbortedResponsePhase1(m)
\*      \/ \E i \in NODES, m \in ValidMessage : RecvAbort(i,m)
      \/ \E i \in NODES : ClientRequest(i)
      \/ \E i \in NODES : ReceiveClient(i)
       
   
      
      
 DummyInvariant == 
 /\
   \/  (Cardinality(localTransactionHistory[1]["prepared"])) = 0
   \/  (Cardinality(localTransactionHistory[1]["prepared"])) = 1
  /\
    ~(Cardinality(localTransactionHistory[1]["prepared"]) = 2)
  /\
   ~(Cardinality(localTransactionHistory[2]["prepared"]) = 2)
  /\  ~(Cardinality(localTransactionHistory[3]["prepared"]) = 2)
  /\ 
    \/Cardinality(localNodesGraph[1]) = 0 
    \/Cardinality(localNodesGraph[1]) = 1
    \/Cardinality(localNodesGraph[1]) = 2
    
 DummyInvariant2 == 
    test < 10 /\ Cardinality(DOMAIN(msgs)) < 15
    
\*Spec == Init /\ [][Next]_<<localNodesGraph>>
\*THEOREM Spec => <> (Cardinality(localNodesGraph[1]) = 1)

LivenessDummy == <> (Cardinality(localNodesGraph[1]) = 1)
  
\*
    
\*    \/ Cardinality(localTransactionHistory[1]["prepared"]) = 1) /\
\*     ~(Cardinality(localTransactionHistory[1]["prepared"]) = 2)
    
\*   /\Cardinality(localTransactionHistory[2]["prepared"]) = 0 \/ Cardinality(localTransactionHistory[2]["prepared"]) = 2
\*   /\Cardinality(localTransactionHistory[3]["prepared"]) = 0 \/ Cardinality(localTransactionHistory[3]["prepared"]) = 2





  
  
    
\*  ParticipantRecvPhase2(r, tn) == 
  
  
  
=============================================================================
\* Modification History
\* Last modified Thu Apr 24 13:51:31 CST 2025 by junhaohu
\* Created Sun Feb 16 22:23:24 CST 2025 by junhaohu