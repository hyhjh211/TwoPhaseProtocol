------------------------------ MODULE graph ------------------------------

EXTENDS Integers,
         Sequences, TLC, FiniteSets
         
         
CONSTANT NODES,  \* The set of nodes in the system,
        transactionNumbers, \* all transcations happened in the system
        transactions, \* transactions[transactionNumber] is the set of operations for transaction identified by transactionNumber 
        transactionShards, \* transactionShards[transactionNumber] is the set of shards involved in the transaction identified by transactionNumber
        ShardNodeMapping, \* [shard2 |-> {nodeID1, nodeID2}
        Shard \* The set of shards (e.g. {s1, s2))
        
        



VARIABLES
  rmState,       \* rmState[transactionNumber, r, shard] is the state of node r for transcation transactionNumber "leader" or "follower" or "primaryLeader".
                 \* rmState[transactionNumber, r, -1] to check whether the node is the primary leader
                 
  msgs,          \* inter shards communication
  msgsShards,    \* intra shards communication
  
  clientRequests, \* clientRequests[r] is the set of requests coming from a clietn at node r
  localTransactionHistory,\*  localTransactionHistory[nodes] is the transcation history graph for the corresponding node 
                          \* localTransactionHistory[nodes]["committed"] is the set of local committed transactions
                           \* localTransactionHistory[nodes]["recentCommitted"] is the set of most recent local committed transactions
                          \* localTransactionHistory[nodes]["prepared"]is the set of local prepared transactions
                          \* localTransactionHistory[nodes]["aborted"]is the set of aborted transactions
                          \* localTransactionHistory[nodes]["heuristic"]is the set of heuristic transactions
  localTransactionalGraph,                        
  localNodesGraph, \* localNodesGraph[nodes] is a graph
  
                     
  pendingTransactions, \* set of transactions to be executed 
  test

  
\*msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r]}


Vertex == [NodeID|-> Int, neighbours |->{}]
Graph == {Vertex}
   
   
   
   
   
   
ValidMessage(messages) ==
    { m \in DOMAIN messages : messages[m] > 0 }

WithMessage(m, messages) ==
    IF m \in DOMAIN messages THEN
        [messages EXCEPT ![m] = messages[m] + 1]
    ELSE
        messages @@ (m :> 1)
        
MsgExist(m, messages) ==
    m \in DOMAIN messages
    
NoMsgsExist(ms, messages) ==
    \A m \in ms: ~MsgExist(m, messages)
    
Send(m) == msgs' = WithMessage(m, msgs)



SendShardMsg(m) == msgsShards' = WithMessage(m, msgsShards)



ExistMsg(r, msgType) ==
    Cardinality({m \in ValidMessage(msgs): m.dst = r /\ m.type = msgType})




OperationSet == 
   [type: "edges", Operation: {"add", "remove"}, sourceVertex: Int, desVertex: Int, shard: Shard] \cup 
   [type: "nodes", Operation: {"add", "remove"}, sourceVertex: Int, shard: Shard]



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
     
     
 
     
     
     
 Messages ==
  (*************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the node indicated by the message's rm field to the leader.       *)
  (* Messages of type "Commit" and "Abort" are sent by the corresponding leader, to be  *)
  (* received by participants.  The set msgs contains just a single copy of     *)
  (* such a message.                                                       *)
  (*************************************************************************)
  [type : {"prepare"}, tn:  transactionNumbers, dependency : SUBSET transactionNumbers, src : NODES, dst : NODES, operations: Seq(OperationSet), shard: Shard, shards: SUBSET Shard]
  \cup [type : {"committedResponse"}, tn:  transactionNumbers, src : NODES, dst : NODES, shard: Shard, shards: SUBSET Shard]
  \cup [type : {"INCOMPATIBLE", "committed", "aborted", "prepared"}, tn: transactionNumbers, src : NODES, dst : NODES, leadingEdge: SUBSET transactionNumbers]
  \cup [type : {"commit", "abort"}, tn:  transactionNumbers, src : NODES, dst : NODES, operations: Seq(OperationSet), shard: Shard, shards: SUBSET Shard]
  \* below are message type for inter shard communication
  \cup [type : { "preparedResponse", "abortedResponse", "prepared","aborted", "committed", "committedResponse"}, tn:  transactionNumbers, src : NODES, dst : NODES,  shard: Shard, shards: SUBSET Shard ]  
  \cup [type : {"prepared"}, tn:  transactionNumbers, operations: Seq(OperationSet), src : NODES, dst : NODES,  shard: Shard, shards: SUBSET Shard ]  
  \cup [type: {"clientRequest"}, tn: transactionNumbers, operations: Seq(OperationSet),  shards: Shard]
  
  
  
  
  
  Quorum(shardInfo) == {i \in SUBSET(NODES) : Cardinality(i) * 2 > Cardinality(ShardNodeMapping[shardInfo])}
  
  
  
  
  
  
  
  ApplyOp(op, nodeID, G) ==
    IF nodeID \in ShardNodeMapping[op.shard]
    THEN
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
\*                    ELSE IF v.NodeID = op.desVertex THEN             
\*                        [NodeID |-> v.NodeID, neighbours |-> v.neighbours \union {op.sourceVertex}]
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
    ELSE
        G
        
 RECURSIVE ApplyOperations(_, _, _)
 ApplyOperations(ops, nodeID, G) ==    
    IF ops = <<>> THEN G
    ELSE ApplyOperations(Tail(ops), nodeID,  ApplyOp(Head(ops), nodeID, G))
    
 Apply(ops, nodeID, G) ==
  
  ApplyOperations(ops, nodeID, G)
  
\*  
\*  deleteMsg(m) ==
\*  IF m.src = m.dst 
\*  THEN
\*    \*don't delete
  
  
  ConflictDetect(tnInfo, i, tnOperations) ==
    LET 
      targetNodes == {tnOperations[op].sourceVertex : op \in 1..Len(tnOperations)}
      preparedTx == localTransactionHistory[i]["prepared"]
      f(x) == {transactions[x][j].sourceVertex : j \in 1..Len(transactions[x])}
      operatedNodes == { f(x) : x \in preparedTx }
      hasIntersection == \E x \in operatedNodes : targetNodes \cap x # {}
      
\*      operatedNodes == 
            
    IN
      hasIntersection  
\* LeaderPrepare(tnInfo, s, r, depdencyInfo, tnOperations) == 
\*  (*************************************************************************)
\*  (* leader s sends prepare message to follower r                           *)
\*  (*************************************************************************)
\*  /\ rmState[tnInfo, s] = "leader"
\*  /\ rmState[tnInfo, r] = "follower" 
\*  /\ Len(msgs[r][s]) \geq 0
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(@, [type |-> "prepared", tn |->tnInfo, dependency |-> depdencyInfo, src |-> s, dst |-> r, operations |-> tnOperations])]
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(msgs[r][s], "aaa")]

 
  InterposedCoordinatorSendPrepares(tnInfo, s, tnOperations, shardsInfo, shardInfo) ==
  (*************************************************************************)
  (* leader s sends prepare message to all followers                       *)
  (*************************************************************************) 
  LET
    constructMsg(msgOneType, msgTwoType) ==
                [ m \in {[type |-> msgOneType, 
                    tn |->tnInfo, 
                    dependency |-> localTransactionHistory[s]["recentCommitted"], 
                    src |-> s, 
                    dst |-> -1, 
                    operations |-> tnOperations,
                    shard |-> shardInfo, 
                    shards |-> shardsInfo
                   ] ,
                   [
                    type |-> msgTwoType,
                    tn |->  tnInfo, 
                    src |-> s, 
                    dst |-> s, 
                    shards |-> shardsInfo,
                    shard |-> shardInfo,
                    leadingEdge |-> localTransactionHistory[s]["recentCommitted"]
                   ]
                     } |-> 1
                  ]
                      
    
    prepareMsg ==  constructMsg("prepare", "prepared")
                
    prepareAndVoteAbort == constructMsg("prepare", "aborted")
                
                 
   IN 
        IF tnInfo \in DOMAIN localTransactionalGraph[s]
        THEN
            /\ ~MsgExist([type |-> "prepare", 
                tn |->tnInfo, 
                dependency |-> localTransactionalGraph[s][tnInfo], 
                src |-> s, 
                dst |-> -1, 
                operations |-> tnOperations,
                shard |-> shardInfo, 
                shards |-> shardsInfo
                ], msgs)
            /\ Send([type |-> "prepare", 
                tn |->tnInfo, 
                dependency |-> localTransactionalGraph[s][tnInfo], 
                src |-> s, 
                dst |-> -1, 
                operations |-> tnOperations,
                shard |-> shardInfo, 
                shards |-> shardsInfo
                ])
                
        ELSE         
        
        \/  
            
            /\ ~ConflictDetect(tnInfo, s, tnOperations)
            /\ msgs' = msgs @@ prepareMsg
            /\ localTransactionalGraph' =  [localTransactionalGraph EXCEPT ![s] = @ @@ [i \in {tnInfo} |-> localTransactionHistory[s]["recentCommitted"]]]
            /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![s]["prepared"] =  @ \union {tnInfo}]
            
        \/  
            /\ ConflictDetect(tnInfo, s, tnOperations)
            /\ msgs' = msgs @@ prepareAndVoteAbort
            /\ localTransactionalGraph' =  [localTransactionalGraph EXCEPT ![s] = @ @@ [i \in {tnInfo} |-> localTransactionHistory[s]["recentCommitted"]]] 
            /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![s]["aborted"] =  @ \union {tnInfo}]

        

  
  
  
\*  LeaderCommit(tnInfo, r, s, depdencyInfo, tnOperations) == 
\*  (*************************************************************************)
\*  (* leader s sends commit message to follower r                           *)
\*  (*************************************************************************)
\*  /\ rmState[tnInfo, s] = "leader"
\*  /\ rmState[tnInfo, r] = "follower"
\*\*  /\ {x \in NODES: tnInfo \in localTransactionHistory[x]["prepared"]} \in Quorum
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(msgs[r][s], [type |-> "committed", tn |-> tnInfo, dependency |-> depdencyInfo, src |-> s, dst |-> r, operations |-> tnOperations])]
\*  
  
  
  LeaderSendCommit(tnInfo, s, shardsInfo, shardInfo) == 
  (*************************************************************************)
  (* leader s sends commit message to all followers                        *)
  (*************************************************************************) 
  LET 
       constructCommitMsg == 
            [ m \in {[type |-> "commit", 
                tn |-> tnInfo, 
                src |-> s, 
                dst |-> -1, 
                operations |-> transactions[tnInfo],
                shards |-> shardsInfo,
                shard |-> shardInfo
                ] ,
              [type |-> "committedResponse", 
                 tn |->  tnInfo, 
                src |-> s, 
                dst |-> s, 
             shards |-> shardsInfo,
              shard |-> shardInfo]
             } |-> 1 ]
       sendCommit ==
       /\ rmState[tnInfo, s, shardInfo] = "leader"
       /\ ~MsgExist([type |-> "commit", 
                tn |-> tnInfo, 
                src |-> s, 
                dst |-> -1, 
                operations |-> transactions[tnInfo],
                shards |-> shardsInfo,
                shard |-> shardInfo
         ], msgs)
      
      /\ localNodesGraph' = [localNodesGraph EXCEPT! [s] = Apply(transactions[tnInfo], s, localNodesGraph[s])]
      /\ msgs' = constructCommitMsg @@ msgs
       
  IN
     /\ sendCommit
     /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![s]["heuristic"] =  @ \union {tnInfo},
                                                                   ![s]["prepared"] = localTransactionHistory[s]["prepared"] \ {tnInfo}]
       


 primaryLeader(tnInfo) == CHOOSE n \in NODES : rmState[tnInfo, n, -1] = "primaryLeader"
 
 
 InterposedCoordinatorCommitResponseHandle(tnInfo, r, shardsInfo, shardInfo) ==    
       
       /\ \E MS \in Quorum(shardInfo):    
        LET 
            
            mset == {m \in ValidMessage(msgs) : 
                                  /\ m.type = "committedResponse"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                                  /\ m.shard = shardInfo
                                  /\ m.shards = shardsInfo
                                  /\ m.src  \in MS}
            
            
        IN 
            /\ \A ac \in MS : \E m \in mset : m.src = ac
            /\ ~MsgExist([type |-> "committedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo),
                            shards |-> shardsInfo,
                            shard |-> shardInfo], msgsShards)
            /\ SendShardMsg([type |-> "committedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo),
                            shards |-> shardsInfo,
                            shard |-> shardInfo])
  
  InterposedCoordinatorRecvCommitResponse(r, m) == 
    /\ rmState[m.tn, r, m.shard] = "leader"
    /\ InterposedCoordinatorCommitResponseHandle(m.tn, r, m.shards, m.shard)
    /\ test' = test + 1
    /\ UNCHANGED <<transactionNumbers, localTransactionHistory, 
        localNodesGraph  , pendingTransactions, rmState, msgs, clientRequests, localTransactionalGraph, clientRequests>>
  
  
  
                            
  CoordinatorCommitResponseHandle(tnInfo, r, shardsInfo) == 
      LET 
           mset == {m \in ValidMessage(msgsShards) : /\ m.type = "committedResponse"
                                      /\ m.dst = r
                                      /\ m.tn  = tnInfo
                   }
      IN   
          /\ tnInfo \in localTransactionHistory[r]["heuristic"]
          /\ Cardinality(mset) = Cardinality(shardsInfo)
          /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![r]["heuristic"] =  @ \{tnInfo},
                                                                        ![r]["recentCommitted"] = @ \union {tnInfo},
                                                                        ![r]["committed"] = @ \union {tnInfo}]
  CoordinatorRecvCommitResponse(r, m) ==
       /\ m.type = "committedResponse"
       /\ rmState[m.tn, r, -1] = "primaryLeader"
       /\ CoordinatorCommitResponseHandle(m.tn, r, m.shards)
       /\ test' = test + 1
       /\ UNCHANGED <<transactionNumbers, 
        localNodesGraph,  clientRequests, msgsShards , pendingTransactions, rmState, msgs, localTransactionalGraph>>
               
        
  
  
  
  
  
\*  LeaderAbort(tnInfo, r, s, depdencyInfo, tnOperations) ==
\*  (*********************************************************************************)
\*  (* leader s spontaneously aborts the transaction and send the abort message to r.*)
\*  (*********************************************************************************)
\*  /\ rmState[tnInfo, s] = "leader"
\*  /\ rmState[tnInfo, r] = "follower"
\*  /\ msgs[r][s]' = Append(msgs[r][s], [type |-> "aborted", tn|-> tnInfo, src |-> s, dst |-> r, operations |-> tnOperations])
  
  
  LeaderSendAbort(tnInfo, s, shardsInfo, shardInfo) ==
  (*********************************************************************************)
  (* leader s sends the abort message to everyone.*)
  (*********************************************************************************)
      /\ rmState[tnInfo, s, shardInfo] = "leader"
      /\ ~MsgExist([type |-> "abort", 
               tn|-> tnInfo, 
               src |-> s, 
               dst |-> -1, 
               operations |-> transactions[tnInfo],
               shards |-> shardsInfo,
               shard |-> shardInfo
          ], msgs)
      /\ Send([type |-> "abort", 
               tn|-> tnInfo, 
               src |-> s, 
               dst |-> -1, 
               operations |-> transactions[tnInfo],
               shards |-> shardsInfo,
               shard |-> shardInfo
       ])
\*       /\ tnState' = [tnState EXCEPT ![tnInfo, s] = "sendAbort"]


  
  

  
  


 Parents(nodes, dag) ==
  UNION {dag[n] : n \in nodes}      
  
 strictSubset(depdencyInfo, nodeID) == 
    depdencyInfo \subseteq localTransactionHistory[nodeID]["recentCommitted"] /\  ~(depdencyInfo = localTransactionHistory[nodeID]["recentCommitted"])
  
RecvPhase1(tnInfo, r, s, depdencyInfo, tnOperations, shardsInfo, shardInfo) == 
  (*************************************************************************)
  (* node r receives message from leader s                                 *)
  (*************************************************************************)
  LET 
        commonElements == localTransactionHistory[r]["prepared"] \intersect depdencyInfo
        txExistHandler(msgType) ==
            /\ ~MsgExist([type |-> msgType,
                   tn |-> tnInfo,
                   src |-> r,
                   dst |-> s,
                   shards |-> shardsInfo,
                   shard |-> shardInfo,
                   leadingEdge |-> localTransactionalGraph[r][tnInfo]], msgs)
            /\ Send([ type |-> msgType,
                   tn |-> tnInfo,
                   src |-> r,
                   dst |-> s,
                   shards |-> shardsInfo,
                   shard |-> shardInfo,
                   leadingEdge |-> localTransactionalGraph[r][tnInfo]
                ])
        sendResponse(msgType) ==
            Send([type |-> msgType, 
                   tn |->  tnInfo, 
                   src |-> r, 
                   dst |-> s, 
                   shards |-> shardsInfo,
                   shard |-> shardInfo,
                   leadingEdge |-> localTransactionHistory[r]["recentCommitted"]'
              ])
            
         
         
  IN  
      IF tnInfo \in DOMAIN localTransactionalGraph[r]
      THEN
        IF tnInfo \in localTransactionHistory[r]["committed"]
        THEN 
            /\ txExistHandler("committed")
            /\ test' = test + 1
            /\ UNCHANGED<<clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, msgsShards, pendingTransactions, rmState>>
        ELSE IF (tnInfo \in localTransactionHistory[r]["prepared"] \/ tnInfo \in localTransactionHistory[r]["heuristic"])
             THEN
                /\ txExistHandler("prepared")
                /\ test' = test + 1
                /\ UNCHANGED<<clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, msgsShards, pendingTransactions, rmState>>
             ELSE 
                /\ txExistHandler("aborted")
                /\ test' = test + 1
                /\ UNCHANGED<<clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, msgsShards, pendingTransactions, rmState>>
      ELSE
      IF depdencyInfo \subseteq localTransactionHistory[r]["committed"] \cup localTransactionHistory[r]["prepared"]
      THEN   
         
          IF ~ConflictDetect(tnInfo, r, tnOperations) 
         
          THEN
            /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![r]["prepared"] =  (@ \ commonElements) \union {tnInfo},
                                                                           ![r]["committed"] =  @ \union commonElements,
                                                                           ![r]["recentCommitted"] = (@ \ Parents(commonElements, localTransactionalGraph[r])) \union commonElements]                  
            /\ localTransactionalGraph' =  [localTransactionalGraph EXCEPT ![r] = @ @@ [i \in {tnInfo} |-> localTransactionHistory[r]["recentCommitted"]']]

            /\ sendResponse("prepared")
            /\ test' = test + 1
            /\ UNCHANGED <<transactionNumbers, 
                localNodesGraph, clientRequests, pendingTransactions, rmState, msgsShards>>
                
          ELSE
            /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![r]["aborted"] = @ \union {tnInfo} ]
            /\ localTransactionalGraph' =  [localTransactionalGraph EXCEPT ![r] = @ @@ [i \in {tnInfo} |-> localTransactionHistory[r]["recentCommitted"]']]
            /\ sendResponse("aborted")
            /\ test' = test + 1
            /\ UNCHANGED <<transactionNumbers, 
                localNodesGraph, clientRequests, pendingTransactions, rmState, msgsShards>>
      ELSE
         /\ test' = test + 1
          /\ ~MsgExist([type |-> "INCOMPATIBLE", tn |-> tnInfo, src |-> r, dst |-> s,  leadingEdge |-> localTransactionHistory[r]["recentCommitted"]], msgs)
          /\ Send([type |-> "INCOMPATIBLE", tn |-> tnInfo, src |-> r, dst |-> s,  leadingEdge |-> localTransactionHistory[r]["recentCommitted"]])
          /\ UNCHANGED <<clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, msgsShards, pendingTransactions, rmState>>
               
  
  
  RcvAbortMsg(r, s, tnInfo, tnOperations, shardInfo) ==
  (*************************************************************************)
  (* node r receives abort message from leader s                       *)
  (*************************************************************************)
   /\ rmState[tnInfo, s, shardInfo] = "leader"
   /\ tnInfo \in localTransactionHistory[r]["prepared"]
   /\  ~(tnInfo \in localTransactionHistory[r]["aborted"])
   /\ localTransactionHistory' = [ localTransactionHistory EXCEPT  ![r]["prepared"] = localTransactionHistory[r]["prepared"]  \ {tnInfo}
                                                                  ,![r]["aborted"] =  localTransactionHistory[r]["aborted"] \union {tnInfo}]
   /\ test' = test + 1
   
   /\ UNCHANGED <<rmState, msgs, transactionNumbers, clientRequests, localNodesGraph
      ,pendingTransactions, msgsShards, localTransactionalGraph>>
  
  
  
  RcvCommitMsg(r, s, tnInfo, tnOperations, shardsInfo, shardInfo) == 
  (*************************************************************************)
  (* node r receives commit message from leader s                       *)
  (*************************************************************************)
  /\ rmState[tnInfo, s, shardInfo] = "leader"
  /\ tnInfo \in localTransactionHistory[r]["prepared"]
\*  /\ ~(tnInfo \in localTransactionHistory[r]["committed"])
\*  /\ ~(tnInfo \in localTransactionHistory[r]["recentCommitted"])
  /\ localTransactionHistory' =  [ localTransactionHistory   EXCEPT ![r]["prepared"] = localTransactionHistory[r]["prepared"] \ {tnInfo}
                                                                           ,![r]["committed"] =  localTransactionHistory[r]["committed"] \cup {tnInfo}
                                                                           ,![r]["recentCommitted"] = (localTransactionHistory[r]["recentCommitted"] \ localTransactionalGraph[r][tnInfo]) \union {tnInfo}]                                                                        
  /\ localNodesGraph' = [localNodesGraph EXCEPT! [r] = Apply(tnOperations, r, localNodesGraph[r])]
  /\ Send([type |-> "committedResponse", 
             tn |->  tnInfo, 
            src |-> r, 
            dst |-> s, 
         shards |-> shardsInfo,
          shard |-> shardInfo])
\*  /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "committed"]
  /\ test' = test + 1
  /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, 
      pendingTransactions, msgsShards, localTransactionalGraph>>
\*  /\ UNCHANGED <<tmState, 
  
  
  
  
  LeaderFowardSingleShardCommit(tnInfo, r, shardsInfo, shardInfo) ==
       /\ ~MsgExist([type |-> "preparedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo),
                            shards |-> shardsInfo,
                            shard |-> shardInfo], msgsShards)
       /\ SendShardMsg([type |-> "preparedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo),
                            shards |-> shardsInfo,
                            shard |-> shardInfo])
\*       /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "fowardCommitted"]
  
  
  
  
  
  
  LeaderFowardSingleShardAbort(tnInfo, r, shardsInfo, shardInfo) ==
      /\ ~MsgExist([type |-> "abortedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo),
                            shards |-> shardsInfo,
                            shard |-> shardInfo], msgsShards)
      /\ SendShardMsg([type |-> "abortedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo),
                            shards |-> shardsInfo,
                            shard |-> shardInfo])
\*       /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "fowardAborted"]
  
                            


  LeaderHandleCommit(tnInfo, r, msg) ==
  (*******************************************************************************************************************************)
  (*Leader r received prepared from other nodes,                                                                   *)
  (*if majority have votes prepared. then votes commit                                                             *)
  (*******************************************************************************************************************************)
    /\ rmState[tnInfo, r, msg.shard] = "leader"             
    /\ \E MS \in Quorum(msg.shard):    
        LET 
            
            mset == {m \in ValidMessage(msgs) : 
                                  /\ m.type = "prepared"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                                  /\ m.shard = msg.shard
                                  /\ m.shards = msg.shards
                                  /\ msg.leadingEdge \subseteq localTransactionHistory[r]["recentCommitted"]
                                  /\ m.src  \in MS}
            
            
        IN  
            IF msg.leadingEdge \subseteq localTransactionHistory[r]["recentCommitted"]
            THEN 
            /\ \A ac \in MS : \E m \in mset : m.src = ac
\*            /\ LeaderSendCommit(tnInfo, r, msg.dependency, msg.operations)
            /\ LeaderFowardSingleShardCommit(msg.tn, r, msg.shards, msg.shard)
            /\ test' = test + 1
            /\ UNCHANGED <<transactionNumbers, msgs, rmState, clientRequests, localTransactionHistory, localNodesGraph, localTransactionalGraph,
                         pendingTransactions, clientRequests, localNodesGraph, localTransactionHistory, pendingTransactions, rmState>>
            ELSE
            /\ test' = test + 1
            /\ LeaderFowardSingleShardAbort(tnInfo, r, msg.shards, msg.shard)
            /\ UNCHANGED <<clientRequests, msgs, localNodesGraph, localTransactionHistory, localTransactionalGraph, pendingTransactions, rmState>>
 
            
            
            
            
            
  LeaderHandleAbort(tnInfo, r, msg) ==
  (*********************************************************************************)
  (*Leader r received aborted from other nodes,                                    *)
  (*if majority have votes aborted. then votes abort                               *)
  (*********************************************************************************)
    /\ rmState[tnInfo, r, msg.shard] = "leader"             
    /\ \E MS \in Quorum(msg.shard):   
        LET 
            
            mset == {m \in ValidMessage(msgs) : 
                                  /\ m.type = "aborted"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                                  /\ m.shard = msg.shard
                                  /\ m.shards = msg.shards
                                  /\ m.src  \in MS}
            
            
        IN  /\ \A ac \in MS : \E m \in mset : m.src = ac
\*            /\ LeaderSendAbort(tnInfo, r, msg.dependency, msg.operations)
            /\ LeaderFowardSingleShardAbort(tnInfo, r, msg.shards, msg.shard)
            /\ test' = test + 1
     /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, localTransactionHistory, localNodesGraph, localTransactionalGraph,
                         pendingTransactions, clientRequests, localNodesGraph, localTransactionHistory, pendingTransactions, msgs>>           
            
       
            
            
\*    /\ \E MS \in Quorum :    
\*            /\ \A ac \in MS : 
\*                \E msg \in msgs[ac][r]:
\*                    /\ msg.type = "preparedResponsePhase2"
\*                    /\ msg.tn = tnInfo
\*                    /\ msg.src = ac
\*                    /\ msg.dst = r
\*                    /\ msg.operations = transactionOperation[tnInfo].op
\*             
\*            /\ LeaderSendCommit(tnInfo, r, transactionOperation[tnInfo].dependency, transactionOperation[tnInfo].op)
            
  
   PrimaryLeaderHandleCommit(tnInfo, r, msg) ==
   LET 
            
      mset == {m \in ValidMessage(msgsShards) : /\ m.type = "preparedResponse"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                    }
      commitMsg == [ m \in { 
                          [type |-> "committed", 
                            tn |-> tnInfo, 
                            src |-> s, 
                            dst |-> -1, 
                            shards |-> msg.shards,
                            shard |-> s
                          ]
                          : s \in msg.shards
                            } 
                   |-> 1 ]
   IN
       /\ Cardinality(mset) = Cardinality(msg.shards)
       /\ NoMsgsExist({ 
                          [type |-> "committed", 
                            tn |-> tnInfo, 
                            src |-> s, 
                            dst |-> -1, 
                            shards |-> msg.shards,
                            shard |-> s
                          ]
                          : s \in msg.shards
                            } , msgsShards)
       /\ msgsShards' = msgsShards @@ commitMsg
   
   
   
   
   
   PimaryLeaderHandleAbort(tnInfo, r, msg) ==
   LET 
            
      mset == {m \in ValidMessage(msgsShards) : /\ m.type = "abortedResponse"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                    }
      commitMsg == [ m \in { 
                          [type |-> "aborted", 
                            tn |-> tnInfo, 
                            src |-> s, 
                            dst |-> -1, 
                            shards |-> msg.shards,
                            shard |-> s
                          ]
                          : s \in msg.shards
                            } 
                   |-> 1 ]
   IN
       /\ Cardinality(mset) > 0
       /\ NoMsgsExist({[type |-> "aborted", 
                            tn |-> tnInfo, 
                            src |-> s, 
                            dst |-> -1, 
                            shards |-> msg.shards,
                            shard |-> s
                          ]
                          : s \in msg.shards
                           }, msgsShards)
       /\ msgsShards' = msgsShards @@ commitMsg
   
   
   PrimaryLeaderSendPrepares(tnInfo, s, tnOperations, shardsInfo) ==
   LET 
   prepareMsg == [ m \in { 
                          [type |-> "prepared", 
                            tn |-> tnInfo, 
                            src |-> s,
                            dst |-> -1,
                            operations |-> tnOperations,
                            shards |-> shardsInfo,
                            shard |-> sh
                          ]
                          : sh \in shardsInfo
                            } 
                   |-> 1 ]
   IN  
      /\ NoMsgsExist({ [type |-> "prepared", 
                            tn |-> tnInfo, 
                            src |-> s,
                            dst |-> -1,
                            operations |-> tnOperations,
                            shards |-> shardsInfo,
                            shard |-> sh
                          ]
                          : sh \in shardsInfo
                            }, msgsShards)
      /\ msgsShards' = msgsShards @@ prepareMsg
      
      
      
      
   InterposedCoordinatorRecvPrepareMsgFromCoordinator(r, msg) ==
   LET 
       NoLeaderExist == \A x \in ShardNodeMapping[msg.shard], s \in {msg.shard} \union {-1} : rmState[msg.tn, x, s] = "follower" 
   IN 
      /\ r \in ShardNodeMapping[msg.shard]
      /\ 
        \/ 
           /\ NoLeaderExist
            
        \/ 
           /\ rmState[msg.tn, r, -1] = "primaryLeader"
           /\ rmState[msg.tn, r, msg.shard] = "follower"
      
      /\ rmState' = [rmState EXCEPT! [msg.tn, r, msg.shard] = "leader"]
      /\ InterposedCoordinatorSendPrepares(msg.tn, r, msg.operations, msg.shards, msg.shard)
      /\ test' = test + 1
      /\ UNCHANGED << clientRequests, localNodesGraph, msgsShards, pendingTransactions>>
      
      
      
      
   InterposedCoordinatorRecvCommitMsgFromCoordinator(r, msg) ==
   /\ msg.type = "committed"
   /\ rmState[msg.tn, r, msg.shard] = "leader"
\*   /\ 
\*        \/ tnShardState[msg.tn, r] = "fowardCommitted"
\*        \/ tnShardState[msg.tn, r] = "primarySendCommitted"  \*  primary leader should be aboe to recv the commit msg even itself sent out committed
   /\ LeaderSendCommit(msg.tn, r, msg.shards, msg.shard)
   /\ test' = test + 1
   /\ UNCHANGED <<clientRequests, localTransactionalGraph, msgsShards, pendingTransactions, rmState>>
   
   
   InterposedCoodinatorRecvAbortMsgFromCoordinator(r, msg) ==
   /\ msg.type = "aborted"
   /\ rmState[msg.tn, r, msg.shard] = "leader"
   /\ LeaderSendAbort(msg.tn, r, msg.shards, msg.shard)
   /\ test' = test + 1
   /\ UNCHANGED <<clientRequests, localNodesGraph, localTransactionHistory, msgsShards, pendingTransactions, rmState, localTransactionalGraph>>
   
   
   
   PimaryLeaderRecvLeaderCommitResponse(msg) ==
   /\ msg.type = "preparedResponse"
   /\ rmState[msg.tn, msg.dst, -1] = "primaryLeader"
   /\ PrimaryLeaderHandleCommit(msg.tn, msg.dst, msg)
   /\ test' = test + 1
   /\ UNCHANGED <<clientRequests, localNodesGraph, localTransactionHistory, msgs, pendingTransactions, localTransactionalGraph, rmState>>
   
   
   
   PrimaryLeaderRecvLeaderAbortResponse(msg) ==
   /\ msg.type = "abortedResponse"
   /\ rmState[msg.tn, msg.dst, -1] = "primaryLeader"
   /\ PimaryLeaderHandleAbort(msg.tn, msg.dst, msg) 
   /\ test' = test + 1
   /\ UNCHANGED <<clientRequests, localNodesGraph, localTransactionHistory, msgs, pendingTransactions, rmState, localTransactionalGraph>> 
      
       
   
\*   ReceiveClient(i) ==
\*    LET 
\*        clientRequest == Head(clientRequests[i])
\*    IN
\*        /\ Len(clientRequests[i]) > 0
\*        /\ LeaderSendPrepares(clientRequest, i, transactions[clientRequest])
\*        /\ clientRequests' = [clientRequests EXCEPT ![i] = Tail(clientRequests[i])]
\*        
\*       /\ UNCHANGED <<transactionNumbers, localTransactionHistory, 
\*        localNodesGraph, acceptedTransactions,  , pendingTransactions, rmState, test>>    
       


  RecvPrepare(r, msg) ==
   /\ msg.type = "prepare" 
   /\ r \in ShardNodeMapping[msg.shard]
\*   /\  
\*       \/tnState[msg.tn, r] = "unknown"   \*   other ndoes didn't know the new transaction 
\*       \/tnState[msg.tn, r] = "sendPrepared"   \*   the node sent out send prepared should still able to recv its own prepare message 
    \*      (tnInfo, r, s, depdencyInfo, tnOperations)
   /\ RecvPhase1(msg.tn, r, msg.src, msg.dependency, msg.operations, msg.shards, msg.shard)
 
            
            
  RecvPrepared(msg) ==
   /\ msg.type = "prepared" 
   /\ msg.dst \in ShardNodeMapping[msg.shard]
   /\ LeaderHandleCommit(msg.tn, msg.dst, msg)
   
  
  RecvAborted(msg) ==
   /\ msg.type = "aborted"
   /\ msg.dst \in ShardNodeMapping[msg.shard]
   /\ LeaderHandleAbort(msg.tn, msg.dst, msg)
  
    
    
    
   RecvCommit(r, msg) ==
   /\ msg.type = "commit"
   /\ r \in ShardNodeMapping[msg.shard]
   /\ RcvCommitMsg(r, msg.src, msg.tn, msg.operations, msg.shards, msg.shard)
   
   
  RecvAbort(r,msg) ==
  /\ msg.type = "abort"
  /\ r \in ShardNodeMapping[msg.shard]
  /\ RcvAbortMsg(r, msg.src, msg.tn, msg.operations, msg.shard)
   
   
   ClientRequest(i) == 
    LET 
       nextExecuteTx == Head(pendingTransactions)
    IN
    /\ Len(pendingTransactions) > 0
    /\ i \in UNION{ShardNodeMapping[sh] : sh \in transactionShards[nextExecuteTx]}
    /\ rmState' = [rmState EXCEPT ![nextExecuteTx,i,-1] = "primaryLeader"]
    /\ clientRequests' = [clientRequests EXCEPT ![i] = Append(clientRequests[i], nextExecuteTx)]
    /\ pendingTransactions' = Tail(pendingTransactions)
    /\ UNCHANGED <<transactionNumbers, msgs, localTransactionHistory, 
        localNodesGraph, msgsShards, test, localTransactionalGraph>>
   
   
   
   
   
  ReceiveClient(i) ==
    LET 
        clientRequest == Head(clientRequests[i])
    IN
        /\ Len(clientRequests[i]) > 0
        /\ PrimaryLeaderSendPrepares(clientRequest, i, transactions[clientRequest], transactionShards[clientRequest])
        /\ clientRequests' = [clientRequests EXCEPT ![i] = Tail(clientRequests[i])]
        
       /\ UNCHANGED <<transactionNumbers, localTransactionHistory, 
        localNodesGraph  , pendingTransactions, rmState, msgs, test, localTransactionalGraph>>
           
        
        
 Init ==   
   LET 
        tSet == { transactionNumbers[i] : i \in DOMAIN transactionNumbers }
   IN 
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [r \in tSet, y \in NODES, s \in Shard \union {-1} |-> "follower"]
  /\ msgs = [m \in {} |-> 0]
  /\ msgsShards = [m \in {} |-> 0]
  /\ pendingTransactions = transactionNumbers
  /\ clientRequests = [r \in NODES |-> <<>>]
  /\ localNodesGraph = [r \in NODES |-> {}]
  /\ localTransactionHistory = [r \in NODES |-> 
        [
            i \in {"committed","recentCommitted","prepared", "aborted", "heuristic" } |-> {}
        ]
    ]
\*  /\ tnState = [r \in tSet, t \in NODES |-> "unknown"]
  /\ localTransactionalGraph = [n \in NODES |->[ m \in {-1} |-> {}]]
  /\ test = 0
  
  
  Next ==
\*      \/ \E i,j \in NODES : Receive(i, j)


      \/ \E i \in NODES, m \in ValidMessage(msgs) :  RecvPrepare(i,m)
      \/ \E i \in NODES, m \in ValidMessage(msgs) : RecvCommit(i,m)
      \/ \E m \in ValidMessage(msgs) : RecvPrepared(m)
      \/ \E m \in ValidMessage(msgs) : RecvAborted(m)
      \/ \E i \in NODES, m \in ValidMessage(msgs) : RecvAbort(i,m)
      \/ \E i \in NODES : ClientRequest(i)
      \/ \E i \in NODES : ReceiveClient(i)
      \/ \E i \in NODES, m \in ValidMessage(msgsShards) : InterposedCoordinatorRecvPrepareMsgFromCoordinator(i, m)
      \/ \E i \in NODES, m \in ValidMessage(msgsShards) : InterposedCoordinatorRecvCommitMsgFromCoordinator(i, m)
      \/ \E i \in NODES, m \in ValidMessage(msgsShards) : InterposedCoodinatorRecvAbortMsgFromCoordinator(i, m) 
      \/ \E m \in ValidMessage(msgsShards) : PimaryLeaderRecvLeaderCommitResponse(m)
      \/ \E m \in ValidMessage(msgsShards) : PrimaryLeaderRecvLeaderAbortResponse(m)
      \/ \E i \in NODES, m \in ValidMessage(msgsShards) : CoordinatorRecvCommitResponse(i, m)
      \/\/ \E i \in NODES, m \in ValidMessage(msgsShards) : InterposedCoordinatorRecvCommitResponse(i, m)
   
      
      
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
    test < 20 /\ Cardinality(DOMAIN(msgs)) < 35 /\ Cardinality(DOMAIN(msgsShards)) < 35
    
  DummyInvariant3 == 
    Cardinality(localNodesGraph[1]) = 0 
    
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
\* Last modified Tue May 27 20:44:39 CST 2025 by junhaohu
\* Created Tue May 06 23:51:09 CST 2025 by junhaohu
