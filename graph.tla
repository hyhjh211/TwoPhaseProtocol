------------------------------ MODULE graph ------------------------------

EXTENDS Integers,
         Sequences, TLC, FiniteSets, FiniteSetsExt, Sequences, SequencesExt, TLC, TLCExt
         
         
CONSTANT NODES,  \* The set of nodes in the system,
        transactionNumbers, \* all transcations happened in the system
        transactions, \* transactions[transactionNumber] is the set of operations for transaction identified by transactionNumber 
        transactionShards, \* transactionShards[transactionNumber] is the set of shards involved in the transaction identified by transactionNumber
        ShardNodeMapping, \* [shard2 |-> {nodeID1, nodeID2}
        Shard, \* The set of shards (e.g. {s1, s2))
        \* The variables below serve to model failures.
        NumFailedNodes,
        NumLostMsg \* not sure whether to model this
        



VARIABLES
  rmState,       \* rmState[transactionNumber, r, shard, term] is the state of node r for transcation transactionNumber "coordinator" or "follower" or "primaryLeader".
                 
                 
  msgs,          \* intra shards communication
  msgsShards,    \* inter shards communication
  
  clientRequests, \* clientRequests[r] is the set of requests coming from a clietn at node r
  localTransactionHistory,\*  localTransactionHistory[nodes] is the transcation history graph for the corresponding node 
                          \* localTransactionHistory[nodes]["committed"] is the set of local committed transactions
                           \* localTransactionHistory[nodes]["leadingEdge"] is the set of most recent local committed transactions
                          \* localTransactionHistory[nodes]["prepared"]is the set of local prepared transactions
                          \* localTransactionHistory[nodes]["aborted"]is the set of aborted transactions
                          \* localTransactionHistory[nodes]["heuristic"]is the set of heuristic transactions
  localTransactionalGraph,                        
  localNodesGraph, \* localNodesGraph[nodes] is a graph
\*  primaryCoordinatorID,  \* primaryCoordinatorID[nodes] = {} set of known primary coordinator
  primaryCoordinatorTerm, \* each time a new server becomes the primary coordinator it will increment this and send this message along with the prepare to other nodes                   
  currentTerm,
  pendingTransactions, \* set of transactions to be executed 
  catchUpID, \* to identify different catch-up requests catchUpID[nodes] 
  failedNodesCount,
  failedNodes,
  lostMsgCount,
  test

  
\*msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r]}


Vertex == [NodeID|-> Int, neighbours |->{}]
Graph == {Vertex}
   
localNodesGraphType == [r \in NODES |-> {}]   
   
   
   
   
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


 ServerShard(server) ==  CHOOSE sh \in DOMAIN ShardNodeMapping : server \in ShardNodeMapping[sh]


ExistMsg(r, msgType) ==
    Cardinality({m \in ValidMessage(msgs): m.dst = r /\ m.type = msgType})


convertNodeIDtoShard(nodeID) ==
     CHOOSE s \in Shard : nodeID \in ShardNodeMapping[s]


Max2(a, b) == IF a >= b THEN a ELSE b

OperationSet == 
   [type: "edges", Operation: {"add", "remove"}, sourceVertex: Int, desVertex: Int, shard: Shard] \cup 
   [type: "nodes", Operation: {"add", "remove"}, sourceVertex: Int, shard: Shard]

setFromSeq(s) == { s[i] : i \in DOMAIN s }

RECURSIVE AllAncestors(_,_,_)
AllAncestors(n, ReverseDag, depth) ==
    IF Assert(depth < 5, "all ancestor error")
    THEN
        IF ReverseDag[n] = {} THEN {} 
        ELSE ReverseDag[n] \cup UNION { AllAncestors(p, ReverseDag, depth + 1) : p \in ReverseDag[n] }
    ELSE FALSE
         
 
 
RECURSIVE Descendants(_,_,_) 
Descendants(graph, n, depth) ==
  IF Assert(depth < 5, "Descendants error")
  THEN
      LET children == graph[n]
      IN children \cup UNION {Descendants(graph, ch, depth + 1) : ch \in children}
  ELSE FALSE

AllDescendants(graph, starts) ==
  UNION {Descendants(graph, start, 0) : start \in starts}

GRAPHTypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [transactionNumbers -> [NODES -> {"follower", "coordinator"}]]
  
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
  [type : {"prepare"}, tn:  transactionNumbers, dependency : SUBSET transactionNumbers, src : NODES, dst : NODES, operations: Seq(OperationSet), shard: Shard, shards: SUBSET Shard, currentServerTerm: Int]
  \cup [type : {"committedResponse"}, tn:  transactionNumbers, src : NODES, dst : NODES, shard: Shard, shards: SUBSET Shard]
  \cup [type : {"INCOMPATIBLE", "committed", "aborted", "prepared"}, tn: transactionNumbers, src : NODES, dst : NODES, leadingEdge: SUBSET transactionNumbers]
  \cup [type : {"commit", "abort"}, tn:  transactionNumbers, src : NODES, dst : NODES, operations: Seq(OperationSet), shard: Shard, shards: SUBSET Shard]
  \cup [type : {"catchUp"}, src : NODES, ID: Int, shard: Shard, leadingEdge : SUBSET transactionNumbers, leader : NODES]
  \cup [type : {"catchUpResponse"}, src : NODES, dst : NODES, transactions: Seq(SUBSET transactionNumbers),ID: Int, subGraph: localNodesGraphType]
  \cup [type : {"finCatUp"}, src : NODES, dst : NODES, ID : Int]
  \* below are message type for inter shard communication
  \cup [type : { "preparedResponse", "abortedResponse", "prepared","aborted", "committed", "committedResponse"}, tn:  transactionNumbers, src : NODES, dst : NODES,  shard: Shard, shards: SUBSET Shard ]  
  \cup [type : {"prepare"}, tn:  transactionNumbers, operations: Seq(OperationSet), src : NODES, dst : NODES,  shard: Shard, shards: SUBSET Shard, primaryCoordinatorTerm: Int ]  
\*  \cup [type: {"clientRequest"}, tn: transactionNumbers, operations: Seq(OperationSet),  shards: Shard]
  
  
  
  
  
  
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
        
 RECURSIVE ApplyOperations(_, _, _, _)
 ApplyOperations(ops, nodeID, G, depth) ==   
    IF Assert(depth < 5, "ApplyOperationsError")
    THEN
        IF ops = <<>> THEN G
        ELSE ApplyOperations(Tail(ops), nodeID,  ApplyOp(Head(ops), nodeID, G), depth + 1)
   ELSE 
        FALSE
    
    
 Apply(ops, nodeID, G) == 
  ApplyOperations(ops, nodeID, G, 0)
  
  
    
    
    
    RECURSIVE ApplyOps(_,_,_,_)
 ApplyOps(txSequence, nodeID, G, depth) ==
    IF Assert(depth < 5, "ApplyOpsError")
    THEN
        IF txSequence = <<>> THEN G
        ELSE IF Head(txSequence) \in localTransactionHistory[nodeID]["committed"]
        THEN
        ApplyOps(Tail(txSequence), nodeID, G, depth + 1)
        ELSE
        ApplyOps(Tail(txSequence), nodeID, ApplyOperations(transactions[Head(txSequence)], nodeID, G, 0), depth + 1)
    ELSE
        FALSE
        
        
        
 ApplyOpsquence(txSequence, nodeID, G) == 
    ApplyOps(txSequence, nodeID, G, 0)
    
    
    
 
\*  
\*  deleteMsg(m) ==
\*  IF m.src = m.dst 
\*  THEN
\*    \*don't delete
  
  ConflictDetect(tnInfo, i, tnOperations, newComm) ==
    LET 
      targetNodes == {tnOperations[op].sourceVertex : op \in 1..Len(tnOperations)}
      preparedTx == localTransactionHistory[i]["prepared"] \ newComm
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
\*  /\ rmState[tnInfo, s] = "coordinator"
\*  /\ rmState[tnInfo, r] = "follower" 
\*  /\ Len(msgs[r][s]) \geq 0
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(@, [type |-> "prepared", tn |->tnInfo, dependency |-> depdencyInfo, src |-> s, dst |-> r, operations |-> tnOperations])]
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(msgs[r][s], "aaa")]

  InterposedCoordinatorSendPrepares(tnInfo, s, tnOperations, shardsInfo, shardInfo, currentServerTermInfo) ==
  (*************************************************************************)
  (* interposed coordinator s sends prepare message to all followers                       *)
  (*************************************************************************) 
  LET
    constructMsg(msgTwoType) ==
                [ m \in {[type |-> "prepare", 
                    tn |->tnInfo, 
                    dependency |-> localTransactionHistory[s]["leadingEdge"], 
                    src |-> s, 
                    dst |-> -1, 
                    operations |-> tnOperations,
                    shard |-> shardInfo, 
                    shards |-> shardsInfo,
                    currentServerTerm |-> currentServerTermInfo
                   ] ,
                   [
                    type |-> msgTwoType,
                    tn |->  tnInfo, 
                    src |-> s, 
                    dst |-> s, 
                    shards |-> shardsInfo,
                    shard |-> shardInfo,
                    leadingEdge |-> localTransactionHistory[s]["leadingEdge"]
                   ]
                     } |-> 1
                  ]
                  
                  
                  
    constructAbortMsg(msgTwoType) ==
               [ m \in {[type |-> "prepare", 
                    tn |->tnInfo, 
                    dependency |-> localTransactionHistory[s]["leadingEdge"], 
                    src |-> s, 
                    dst |-> -1, 
                    operations |-> tnOperations,
                    shard |-> shardInfo, 
                    shards |-> shardsInfo,
                    currentServerTerm |-> currentServerTermInfo
                   ] ,
                   [
                    type |-> msgTwoType,
                    tn |->  tnInfo, 
                    src |-> s, 
                    dst |-> s, 
                    shards |-> shardsInfo,
                    shard |-> shardInfo,
                    leadingEdge |-> localTransactionHistory[s]["leadingEdge"]
                   ],
                   [type |-> "abort", 
                       tn|-> tnInfo, 
                       src |-> s, 
                       dst |-> -1, 
                       operations |-> transactions[tnInfo],
                       shards |-> shardsInfo,
                       shard |-> shardInfo
                   ]
                     } |-> 1
                  ]                 
    
    prepareMsg ==  constructMsg("prepared")
                
    prepareAndVoteAbort == constructAbortMsg("aborted")
                
                 
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
                shards |-> shardsInfo,
                currentServerTerm |-> currentServerTermInfo
                ], msgs)
            /\ Send([type |-> "prepare", 
                tn |->tnInfo, 
                dependency |-> localTransactionalGraph[s][tnInfo], 
                src |-> s, 
                dst |-> -1, 
                operations |-> tnOperations,
                shard |-> shardInfo, 
                shards |-> shardsInfo,
                currentServerTerm |-> currentServerTermInfo
                ])
             /\ UNCHANGED <<test, localTransactionHistory, localTransactionalGraph, primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, msgsShards, pendingTransactions, catchUpID>>   
        ELSE         
        
        \/  
            
            /\ ~ConflictDetect(tnInfo, s, tnOperations, {})
            /\ msgs' = msgs @@ prepareMsg
            /\ localTransactionalGraph' =  [localTransactionalGraph EXCEPT ![s] = @ @@ [i \in {tnInfo} |-> localTransactionHistory[s]["leadingEdge"]]]
            /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![s]["prepared"] =  @ \union {tnInfo}]
            /\ UNCHANGED <<test, primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, msgsShards, pendingTransactions, catchUpID>>
            
        \/  
            /\ ConflictDetect(tnInfo, s, tnOperations, {})
            /\ msgs' = msgs @@ prepareAndVoteAbort 
            /\ localTransactionalGraph' =  [localTransactionalGraph EXCEPT ![s] = @ @@ [i \in {tnInfo} |-> localTransactionHistory[s]["leadingEdge"]]] 
            /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![s]["aborted"] =  @ \union {tnInfo}]
            /\ UNCHANGED <<test, primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, msgsShards, pendingTransactions, catchUpID>>


        

  
  
  
\*  LeaderCommit(tnInfo, r, s, depdencyInfo, tnOperations) == 
\*  (*************************************************************************)
\*  (* leader s sends commit message to follower r                           *)
\*  (*************************************************************************)
\*  /\ rmState[tnInfo, s] = "coordinator"
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
       /\ rmState[tnInfo, s, shardInfo, currentTerm[tnInfo, s]] = "coordinator"
       /\ ~MsgExist([type |-> "commit", 
                tn |-> tnInfo, 
                src |-> s, 
                dst |-> -1, 
                operations |-> transactions[tnInfo],
                shards |-> shardsInfo,
                shard |-> shardInfo
         ], msgs)
      /\ ~MsgExist([type |-> "abort", 
                tn |-> tnInfo, 
                src |-> s, 
                dst |-> -1, 
                operations |-> transactions[tnInfo],
                shards |-> shardsInfo,
                shard |-> shardInfo
         ], msgs)
      
      
       
  IN
     /\ sendCommit
     /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![s]["heuristic"] =  @ \union {tnInfo},
                                                                   ![s]["prepared"] = localTransactionHistory[s]["prepared"] \ {tnInfo}]
       
      /\ localNodesGraph' = [localNodesGraph EXCEPT! [s] = Apply(transactions[tnInfo], s, localNodesGraph[s])]
      /\ msgs' = constructCommitMsg @@ msgs

 primaryLeader(tnInfo, term) == CHOOSE n \in NODES : rmState[tnInfo, n, -1, term] = "primaryLeader"
 
 
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
                            dst |-> primaryLeader(tnInfo, currentTerm[tnInfo, r]),
                            shards |-> shardsInfo,
                            shard |-> shardInfo], msgsShards)
            /\ SendShardMsg([type |-> "committedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo, currentTerm[tnInfo, r]),
                            shards |-> shardsInfo,
                            shard |-> shardInfo])
            /\ localTransactionHistory' =  [ localTransactionHistory   EXCEPT ![r]["heuristic"] = localTransactionHistory[r]["heuristic"] \ {tnInfo}
                                                                           ,![r]["committed"] =  localTransactionHistory[r]["committed"] \cup {tnInfo}
                                                                           ,![r]["leadingEdge"] = (localTransactionHistory[r]["leadingEdge"] \ localTransactionalGraph[r][tnInfo]) \union {tnInfo}] 
  
  InterposedCoordinatorRecvCommitResponse(r, m) == 
    /\ rmState[m.tn, r, m.shard, currentTerm[m.tn, r]] = "coordinator"
    /\ InterposedCoordinatorCommitResponseHandle(m.tn, r, m.shards, m.shard)
    /\ test' = test + 1
    /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, 
        localNodesGraph  , pendingTransactions, rmState, msgs, clientRequests, localTransactionalGraph, clientRequests, catchUpID>>
  
  
  
                            
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
                                                                        ![r]["leadingEdge"] = @ \union {tnInfo},
                                                                        ![r]["committed"] = @ \union {tnInfo}]
  CoordinatorRecvCommitResponse(r, m) ==
       /\ m.type = "committedResponse"
       /\ rmState[m.tn, r, -1, currentTerm[m.tn, r]] = "primaryLeader"
       /\ CoordinatorCommitResponseHandle(m.tn, r, m.shards)
       /\ test' = test + 1
       /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, 
        localNodesGraph,  clientRequests, msgsShards , pendingTransactions, rmState, msgs, localTransactionalGraph, catchUpID>>
               
        
  
  
  
  
  
\*  LeaderAbort(tnInfo, r, s, depdencyInfo, tnOperations) ==
\*  (*********************************************************************************)
\*  (* leader s spontaneously aborts the transaction and send the abort message to r.*)
\*  (*********************************************************************************)
\*  /\ rmState[tnInfo, s] = "coordinator"
\*  /\ rmState[tnInfo, r] = "follower"
\*  /\ msgs[r][s]' = Append(msgs[r][s], [type |-> "aborted", tn|-> tnInfo, src |-> s, dst |-> r, operations |-> tnOperations])
  
  
  LeaderSendAbort(tnInfo, s, shardsInfo, shardInfo) ==
  (*********************************************************************************)
  (* leader s sends the abort message to everyone.*)
  (*********************************************************************************)
      /\ rmState[tnInfo, s, shardInfo] = "coordinator"
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
    depdencyInfo \subseteq localTransactionHistory[nodeID]["leadingEdge"] /\  ~(depdencyInfo = localTransactionHistory[nodeID]["leadingEdge"])
  
RecvPhase1(tnInfo, r, s, depdencyInfo, tnOperations, shardsInfo, shardInfo) == 
  (*************************************************************************)
  (* node r receives message from leader s                                 *)
  (*************************************************************************)
  LET 
        commonElements == localTransactionHistory[r]["prepared"] \intersect depdencyInfo
        mprepareSet == {m \in ValidMessage(msgs) : /\ m.type = "prepared"
                                      /\ m.dst = s
                                      /\ m.tn  = tnInfo
                                      /\ m.src = r
                   }
        havePrepared == Cardinality(mprepareSet) > 0
        mset == {m \in ValidMessage(msgs) : /\ m.type = "aborted"
                                      /\ m.dst = s
                                      /\ m.tn  = tnInfo
                                      /\ m.src = r
                   }
        haveAborted == Cardinality(mset) > 0
        
        txExistHandler(msgType) ==
            /\ ~MsgExist([type |-> msgType,
                   tn |-> tnInfo,
                   src |-> r,
                   dst |-> s,
                   shards |-> shardsInfo,
                   shard |-> shardInfo,
                   leadingEdge |-> localTransactionalGraph[r][tnInfo]], msgs)
            /\ ~havePrepared
            /\ ~haveAborted
            /\ Send([ type |-> msgType,
                   tn |-> tnInfo,
                   src |-> r,
                   dst |-> s,
                   shards |-> shardsInfo,
                   shard |-> shardInfo,
                   leadingEdge |-> localTransactionalGraph[r][tnInfo]
                ])
        updatedLeadingEdge == (localTransactionHistory[r]["leadingEdge"] \ Parents(commonElements, localTransactionalGraph[r])) \union commonElements
        
        sendResponse(msgType) ==
            Send([type |-> msgType, 
                   tn |->  tnInfo, 
                   src |-> r, 
                   dst |-> s, 
                   shards |-> shardsInfo,
                   shard |-> shardInfo,
                   leadingEdge |-> updatedLeadingEdge
                ])
            
         
         
  IN  
      IF tnInfo \in DOMAIN localTransactionalGraph[r]
      THEN
        IF tnInfo \in localTransactionHistory[r]["committed"]
        THEN 
            /\ txExistHandler("committed")
            /\ ~MsgExist([type |-> "committedResponse", 
                            tn |->  tnInfo, 
                           src |-> r, 
                           dst |-> s, 
                        shards |-> shardsInfo,
                         shard |-> shardInfo], msgs)
            /\ test' = test + 1
            /\ UNCHANGED <<primaryCoordinatorTerm, lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, pendingTransactions, rmState, catchUpID, msgsShards>>
        ELSE IF (tnInfo \in localTransactionHistory[r]["prepared"] \/ tnInfo \in localTransactionHistory[r]["heuristic"])
             THEN
                /\ txExistHandler("prepared")
                /\ test' = test + 1
                /\ UNCHANGED <<primaryCoordinatorTerm, lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, pendingTransactions, rmState, catchUpID, msgsShards>>
             ELSE 
                /\ txExistHandler("aborted")
                /\ test' = test + 1
                /\ UNCHANGED <<primaryCoordinatorTerm, lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, pendingTransactions, rmState, catchUpID, msgsShards>>
      ELSE
      IF depdencyInfo \subseteq localTransactionHistory[r]["committed"] \cup localTransactionHistory[r]["prepared"]
      THEN   
         
          IF ~ConflictDetect(tnInfo, r, tnOperations, commonElements) 
         
          THEN
            /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![r]["prepared"] =  (@ \ commonElements) \union {tnInfo},
                                                                           ![r]["committed"] =  @ \union commonElements,
                                                                           ![r]["leadingEdge"] = (@ \ Parents(commonElements, localTransactionalGraph[r])) \union commonElements]           
            /\ localNodesGraph' = [localNodesGraph EXCEPT ![r] = ApplyOpsquence(SetToSeq(commonElements), r, localNodesGraph[r])]                                                       
            /\ localTransactionalGraph' =  [localTransactionalGraph EXCEPT ![r] = @ @@ [i \in {tnInfo} |-> depdencyInfo]]
\*            /\ localTransactionalGraph' =  [localTransactionalGraph EXCEPT ![r] = @ @@ [i \in {tnInfo} |-> (localTransactionHistory[r]["leadingEdge"] \ Parents(commonElements, localTransactionalGraph[r])) \union commonElements ]]
            /\ ~havePrepared
            /\ ~haveAborted
            /\ sendResponse("prepared")
            /\ test' = test + 1
            /\ UNCHANGED <<primaryCoordinatorTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, 
                 clientRequests, pendingTransactions, rmState, catchUpID, msgsShards>>
                
          ELSE
            /\ sendResponse("aborted")
            /\ ~haveAborted
            /\ test' = test + 1
            /\ UNCHANGED <<primaryCoordinatorTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, 
                localNodesGraph, clientRequests, pendingTransactions, rmState, localTransactionHistory, localTransactionalGraph, catchUpID, msgsShards>>
      ELSE
         /\ test' = test + 1
\*          /\ ~MsgExist([type |-> "aborted", tn |-> tnInfo, src |-> r, dst |-> s, shards |-> shardsInfo, shard |-> shardInfo, leadingEdge |-> localTransactionHistory[r]["leadingEdge"]], msgs)
         /\  ~haveAborted
          /\ Send([type |-> "aborted", tn |-> tnInfo, src |-> r, dst |-> s,  shards |-> shardsInfo, shard |-> shardInfo, leadingEdge |-> localTransactionHistory[r]["leadingEdge"]])
          /\ UNCHANGED <<primaryCoordinatorTerm,lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, pendingTransactions, rmState, catchUpID, msgsShards>>
         
  
  
  
  RcvAbortMsg(r, s, tnInfo, tnOperations, shardInfo) ==
  (*************************************************************************)
  (* node r receives abort message from leader s                       *)
  (*************************************************************************)
   /\ rmState[tnInfo, s, shardInfo] = "coordinator"
   /\ tnInfo \in localTransactionHistory[r]["prepared"]
   /\  ~(tnInfo \in localTransactionHistory[r]["aborted"])
   /\ localTransactionHistory' = [ localTransactionHistory EXCEPT  ![r]["prepared"] = localTransactionHistory[r]["prepared"]  \ {tnInfo}
                                                                  ,![r]["aborted"] =  localTransactionHistory[r]["aborted"] \union {tnInfo}]
   /\ test' = test + 1
   
   /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, rmState, msgs, transactionNumbers, clientRequests, localNodesGraph
      ,pendingTransactions, msgsShards, localTransactionalGraph, catchUpID>>
  
  
  
  
  SendCatchUp(r, shardInfo, txLeader, txID) == 
    LET 
     mset == {m \in ValidMessage(msgs) : /\ m.type = "catchUp"
                                      /\ m.ID = txID
                                      /\ m.shard  = shardInfo
                                      /\ m.src = r
                   }
    IN
\*   /\ ~MsgExist([type|-> "catchUp", src |-> r, ID |-> txID, shard |-> shardInfo, leadingEdge |-> localTransactionHistory[r]["leadingEdge"], leader |-> txLeader], msgs)
   /\ Cardinality(mset) < 1
   /\ Send([type|-> "catchUp", src |-> r, ID |-> txID, shard |-> shardInfo, leadingEdge |-> localTransactionHistory[r]["leadingEdge"], leader |-> txLeader])
   /\ catchUpID' = [catchUpID EXCEPT ![r] = @ + 1]
   
   
   
   
   
  RcvCommitMsg(r, s, tnInfo, tnOperations, shardsInfo, shardInfo) == 
  (*************************************************************************)
  (* node r receives commit message from leader s                          *)
  (*************************************************************************)
  IF tnInfo \in DOMAIN localTransactionalGraph[r]
  THEN
\*  /\ rmState[tnInfo, s, shardInfo] = "coordinator"
  /\ tnInfo \in localTransactionHistory[r]["prepared"]
\*  /\ ~(tnInfo \in localTransactionHistory[r]["committed"])
\*  /\ ~(tnInfo \in localTransactionHistory[r]["leadingEdge"])
  /\ localTransactionHistory' =  [ localTransactionHistory   EXCEPT ![r]["prepared"] = localTransactionHistory[r]["prepared"] \ {tnInfo}
                                                                           ,![r]["committed"] =  localTransactionHistory[r]["committed"] \cup {tnInfo}
                                                                           ,![r]["leadingEdge"] = (localTransactionHistory[r]["leadingEdge"] \ localTransactionalGraph[r][tnInfo]) \union {tnInfo}]                                                                        
  /\ localNodesGraph' = [localNodesGraph EXCEPT! [r] = Apply(tnOperations, r, localNodesGraph[r])]
  /\ ~MsgExist([type |-> "committedResponse", 
             tn |->  tnInfo, 
            src |-> r, 
            dst |-> s, 
         shards |-> shardsInfo,
          shard |-> shardInfo], msgs)
  /\ Send([type |-> "committedResponse", 
             tn |->  tnInfo, 
            src |-> r, 
            dst |-> s, 
         shards |-> shardsInfo,
          shard |-> shardInfo])
\*  /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "committed"]
  /\ test' = test + 1
  /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, rmState, clientRequests, 
      pendingTransactions, msgsShards, localTransactionalGraph, catchUpID>>
  ELSE
    /\ SendCatchUp(r, shardInfo, s , tnInfo)
    /\ test' = test + 1
    /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, rmState, clientRequests, 
      pendingTransactions, msgsShards, localTransactionalGraph, localNodesGraph, localTransactionHistory>>
    
\*  /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,tmState, 



 AppendSetToSeq(set, seq) ==
    SetToSeq(set) \o seq
 
 RECURSIVE TopoSort(_,_,_)
 TopoSort(graph, remaining, depth) ==
  IF Assert(depth < 5, "error topology sort")
  THEN
  IF remaining = {} THEN <<>>
  ELSE
    LET
      ready == { n \in remaining : \A parent \in graph[n] : parent \notin remaining }
      rest == remaining \ ready
    IN
      AppendSetToSeq(ready,TopoSort(graph, rest, depth + 1))
  ELSE
     FALSE






  
  ServeCatchUp(r, s, shardInfo, leadingEdgeR, leadingEdgeS, requestID) ==
  (*************************************************************************)
  (* node r receives catchup message from node s                           *)
  (* newTxDag add -1 as dummy root node    children points to parents      *)
  (* newReverseTxDag parents points to children                            *)
  (*************************************************************************)
   LET
   newTxDag == [n \in (DOMAIN localTransactionalGraph[r] \cap localTransactionHistory[r]["committed"]) |-> IF localTransactionalGraph[r][n] = {} THEN {-1} ELSE (localTransactionalGraph[r][n] \cap localTransactionHistory[r]["committed"])] @@ [i \in {-1} |-> {}]
   newReverseTxDag ==  [n \in DOMAIN newTxDag |-> {m \in DOMAIN newTxDag : n \in newTxDag[m]}]
   AncestorsOfR == UNION {AllAncestors(n, newTxDag, 0) : n \in leadingEdgeR}
   AncestorsOfS == UNION {AllAncestors(n, newTxDag, 0) : n \in (leadingEdgeS \cap localTransactionHistory[r]["committed"])}
   CommonAncestors == AncestorsOfR \cap AncestorsOfS
   CommonLeastAncestors == 
            LET ca == {x \in CommonAncestors : \A y \in newReverseTxDag[x]: y \notin CommonAncestors} 
            IN IF ca = {} THEN ca \union {-1} ELSE ca
   \* to handle the leading empty special case
   SubGraph(ReverseTxDag, TxDag, startNodes) ==
      LET desc == AllDescendants(ReverseTxDag, startNodes) 
      IN [n \in desc |-> TxDag[n]]
   constructedSubGraph == SubGraph(newReverseTxDag, localTransactionalGraph[r], CommonLeastAncestors)
   mset == {m \in ValidMessage(msgs) : /\ m.type = "catchUpResponse"
                                      /\ m.dst = s
                                      /\ m.ID  = requestID
                                      /\ m.src = r
                   }
   IN
   
\*     /\ ~MsgExist([type |-> "catchUpResponse", 
\*                   src |-> r, 
\*                   dst |-> s, 
\*                   transactions |-> TopoSort(localTransactionalGraph[r], DOMAIN constructedSubGraph, 0),
\*                   ID |-> requestID, 
\*                   subGraph |-> constructedSubGraph] 
\*                   , msgs)
     /\ Cardinality(mset) < 1
     /\  Send([type |-> "catchUpResponse", 
                   src |-> r, 
                   dst |-> s, 
                   transactions |-> TopoSort(localTransactionalGraph[r], DOMAIN constructedSubGraph , 0),
                   ID |-> requestID, 
                   subGraph |-> constructedSubGraph])
  
  MergeGraphs(G1, G2) ==
  [ n \in (DOMAIN G1 \cup DOMAIN G2) |->
      IF n \in DOMAIN G1 /\ n \in DOMAIN G2 THEN
        G1[n] \cup G2[n]
      ELSE IF n \in DOMAIN G1 THEN
        G1[n]
      ELSE
        G2[n]
  ]
  
  
  ServeCatchUpResponse(r, s, subGraph,  transactionSequence, requestID) == 
  LET 
    newCommitted == localTransactionHistory[r]["committed"] \union setFromSeq(transactionSequence)
    committedTxDag == [i \in newCommitted |-> MergeGraphs(localTransactionalGraph[r], subGraph)[i] \intersect newCommitted]
    NoneLeaf == UNION { committedTxDag[n] : n \in DOMAIN committedTxDag }
    Leaf == DOMAIN committedTxDag \ NoneLeaf
  IN
     /\ localTransactionalGraph' = [localTransactionalGraph EXCEPT ![r] = MergeGraphs(localTransactionalGraph[r], subGraph)]
     /\ localTransactionHistory' = [localTransactionHistory EXCEPT ![r]["leadingEdge"] = @ \union Leaf,
                                                                   ![r]["aborted"] = @ \ DOMAIN subGraph,
                                                                   ![r]["committed"] = newCommitted ]
     /\ ~MsgExist([type |-> "finCatUp", src |-> r, dst |-> s, ID |-> requestID], msgs)
     /\ Send([type |-> "finCatUp", src |-> r, dst |-> s, ID |-> requestID])
                       
  
  
  
  
  LeaderFowardSingleShardCommit(tnInfo, r, shardsInfo, shardInfo) ==
       /\ ~MsgExist([type |-> "preparedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo, currentTerm[tnInfo, r]),
                            shards |-> shardsInfo,
                            shard |-> shardInfo], msgsShards)
       /\ ~MsgExist([type |-> "abortedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo, currentTerm[tnInfo, r]),
                            shards |-> shardsInfo,
                            shard |-> shardInfo], msgsShards)
       /\ SendShardMsg([type |-> "preparedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo, currentTerm[tnInfo, r]),
                            shards |-> shardsInfo,
                            shard |-> shardInfo])
\*       /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "fowardCommitted"]
  
  
  
  
  
  
  LeaderFowardSingleShardAbort(tnInfo, r, shardsInfo, shardInfo) ==
      /\ ~MsgExist([type |-> "abortedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo, currentTerm[tnInfo, r]),
                            shards |-> shardsInfo,
                            shard |-> shardInfo], msgsShards)
      /\ ~MsgExist([type |-> "preparedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo, currentTerm[tnInfo, r]),
                            shards |-> shardsInfo,
                            shard |-> shardInfo], msgsShards)                      
      /\ SendShardMsg([type |-> "abortedResponse", 
                            tn |-> tnInfo, 
                            src |-> r,
                            dst |-> primaryLeader(tnInfo, currentTerm[tnInfo, r]),
                            shards |-> shardsInfo,
                            shard |-> shardInfo])
\*       /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "fowardAborted"]
  
                            
  
        

  LeaderHandleCommit(tnInfo, r, msg) ==
  (*******************************************************************************************************************************)
  (*Leader r received prepared from other nodes,                                                                   *)
  (*if majority have votes prepared. then votes commit                                                             *)
  (*******************************************************************************************************************************) 
    /\ \E MS \in Quorum(msg.shard):    
        LET 
            
            mset == {m \in ValidMessage(msgs) : 
                                  /\ m.type = "prepared"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                                  /\ m.shard = msg.shard
                                  /\ m.shards = msg.shards
                                  /\ m.leadingEdge \subseteq localTransactionHistory[r]["leadingEdge"]
                                  /\ m.src  \in MS}
        IN  
            IF msg.leadingEdge \subseteq localTransactionHistory[r]["committed"] \/ msg.leadingEdge \subseteq localTransactionHistory[r]["prepared"]
            THEN 
            /\ \A ac \in MS : \E m \in mset : m.src = ac
            /\ LeaderFowardSingleShardCommit(msg.tn, r, msg.shards, msg.shard)
            /\ test' = test + 1
            /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, msgs, rmState, clientRequests, localTransactionHistory, localNodesGraph, localTransactionalGraph,
                         pendingTransactions, clientRequests, localNodesGraph, pendingTransactions, rmState, catchUpID>>
            ELSE
            /\ test' = test + 1
            /\ LeaderFowardSingleShardAbort(tnInfo, r, msg.shards, msg.shard)
            /\ SendCatchUp(r,  msg.shard, r, tnInfo)
            
            /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, pendingTransactions, rmState>>
 
  
  
          
            
            
            
            
  LeaderHandleAbort(tnInfo, r, msg) ==
  (*********************************************************************************)
  (*Leader r received aborted from other nodes,                                    *)
  (*if majority have votes aborted. then votes abort                               *)
  (*********************************************************************************)
    /\ rmState[tnInfo, r, msg.shard] = "coordinator"             
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
            /\ LeaderFowardSingleShardAbort(tnInfo, r, msg.shards, msg.shard)
            /\ test' = test + 1
     /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, rmState, clientRequests, localTransactionHistory, localNodesGraph, localTransactionalGraph,
                         pendingTransactions, clientRequests, localNodesGraph, localTransactionHistory, pendingTransactions, msgs, catchUpID>>           
            
       
            
            
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
\*       /\ NoMsgsExist({[type |-> "aborted", 
\*                            tn |-> tnInfo, 
\*                            src |-> s, 
\*                            dst |-> -1, 
\*                            shards |-> msg.shards,
\*                            shard |-> s
\*                          ]
\*                          : s \in msg.shards
\*                           }, msgsShards)
       /\ msgsShards' = msgsShards @@ commitMsg
   
   
   PrimaryLeaderSendPrepares(tnInfo, s, tnOperations, shardsInfo) ==
   LET 
   prepareMsg == [ m \in { 
                          [type |-> "prepare", 
                            tn |-> tnInfo, 
                            src |-> s,
                            dst |-> -1,
                            operations |-> tnOperations,
                            shards |-> shardsInfo,
                            shard |-> sh,
                            primaryCoordinatorTerm |-> primaryCoordinatorTerm
                          ]
                          : sh \in shardsInfo
                            } 
                   |-> 1 ]
   IN  
\*      /\ NoMsgsExist({ [type |-> "prepare", 
\*                            tn |-> tnInfo, 
\*                            src |-> s,
\*                            dst |-> -1,
\*                            operations |-> tnOperations,
\*                            shards |-> shardsInfo,
\*                            shard |-> sh
\*                          ]
\*                          : sh \in shardsInfo
\*                            }, msgsShards)
      /\ msgsShards' = msgsShards @@ prepareMsg
      /\ primaryCoordinatorTerm' =  primaryCoordinatorTerm + 1
      
      
      
      
   InterposedCoordinatorRecvPrepareMsgFromCoordinator(r, msg) ==
   LET 
       NoLeaderExist ==  /\ \A x \in ShardNodeMapping[msg.shard], s \in ({msg.shard} \union {-1}) : rmState[msg.tn, x, s, msg.primaryCoordinatorTerm] = "follower" 
\*                         /\ ~(ServerShard(r)  =  ServerShard(msg.src))
   IN 
      /\ msg.type = "prepare"
      /\ r \in ShardNodeMapping[msg.shard]
      /\ 
        \/ 
           /\ NoLeaderExist
            
        \/ 
           /\ rmState[msg.tn, r, -1, msg.primaryCoordinatorTerm] = "primaryLeader"
           /\ rmState[msg.tn, r, msg.shard, msg.primaryCoordinatorTerm] = "follower"
      
      /\ rmState' = [rmState EXCEPT! [msg.tn, r, msg.shard, currentTerm[msg.tn, r]] = "coordinator"]
      /\ InterposedCoordinatorSendPrepares(msg.tn, r, msg.operations, msg.shards, msg.shard, msg.primaryCoordinatorTerm)

      
      
      
      
      
   InterposedCoordinatorRecvCommitMsgFromCoordinator(r, msg) ==
   /\ msg.type = "committed"
\*   /\ \E t \in currentTerm[r]: rmState[msg.tn, r, msg.shard, t] = "coordinator"
   /\ rmState[msg.tn, r, msg.shard, currentTerm[msg.tn, r]] = "coordinator"
\*   /\ 
\*        \/ tnShardState[msg.tn, r] = "fowardCommitted"fenjd       s
\*        \/ tnShardState[msg.tn, r] = "primarySendCommitted"  \*  primary leader should be aboe to recv the commit msg even itself sent out committed
   /\ LeaderSendCommit(msg.tn, r, msg.shards, msg.shard)
   /\ test' = test + 1
   /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, clientRequests, localTransactionalGraph, msgsShards, pendingTransactions, rmState, catchUpID>>
   
   
   InterposedCoodinatorRecvAbortMsgFromCoordinator(r, msg) ==
   /\ msg.type = "aborted"
   /\ rmState[msg.tn, r, msg.shard, currentTerm[msg.tn, r]] = "coordinator"
\*   /\ \E t \in currentTerm[r]: rmState[msg.tn, r, msg.shard, t] = "coordinator"
   /\ LeaderSendAbort(msg.tn, r, msg.shards, msg.shard)
   /\ test' = test + 1
   /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, localTransactionHistory, msgsShards, pendingTransactions, rmState, localTransactionalGraph, catchUpID>>
   
   
   
   PimaryLeaderRecvLeaderCommitResponse(msg) ==
   /\ msg.type = "preparedResponse"
\*   /\ rmState[msg.tn, msg.dst, -1, msg.] = "primaryLeader"
   /\ PrimaryLeaderHandleCommit(msg.tn, msg.dst, msg)
   /\ test' = test + 1
   /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, localTransactionHistory, msgs, pendingTransactions, localTransactionalGraph, rmState, catchUpID>>
   
   
   
   PrimaryLeaderRecvLeaderAbortResponse(msg) ==
   /\ msg.type = "abortedResponse"
\*   /\ rmState[msg.tn, msg.dst, -1] = "primaryLeader"
   /\ PimaryLeaderHandleAbort(msg.tn, msg.dst, msg) 
   /\ test' = test + 1
   /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, clientRequests, localNodesGraph, localTransactionHistory, msgs, pendingTransactions, rmState, localTransactionalGraph, catchUpID>> 
      
       
   
\*   ReceiveClient(i) ==
\*    LET 
\*        clientRequest == Head(clientRequests[i])
\*    IN
\*        /\ Len(clientRequests[i]) > 0
\*        /\ LeaderSendPrepares(clientRequest, i, transactions[clientRequest])
\*        /\ clientRequests' = [clientRequests EXCEPT ![i] = Tail(clientRequests[i])]
\*        
\*       /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,transactionNumbers, localTransactionHistory, 
\*        localNodesGraph, acceptedTransactions,  , pendingTransactions, rmState, test>>    
       


  RecvPrepare(r, msg) ==
  LET 
   
   term == IF rmState[msg.tn, r, -1, currentTerm[msg.tn, r]] = "primaryLeader"
           THEN 
            currentTerm[msg.tn, r]
           ELSE   
            msg.currentServerTerm
  IN            
  
   /\ msg.type = "prepare" 
   /\ r \in ShardNodeMapping[msg.shard]
\*   /\  
\*       \/tnState[msg.tn, r] = "unknown"   \*   other ndoes didn't know the new transaction 
\*       \/tnState[msg.tn, r] = "sendPrepared"   \*   the node sent out send prepared should still able to recv its own prepare message 
    \*      (tnInfo, r, s, depdencyInfo, tnOperations)
   /\ currentTerm' =  [currentTerm EXCEPT! [msg.tn, r]  = Max2( term, msg.currentServerTerm)]
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
   
   
\*   ClientRequest(i) == 
\*    LET 
\*       nextExecuteTx == Head(pendingTransactions)
\*    IN
\*    /\ Len(pendingTransactions) > 0
\*    /\ i \in UNION{ShardNodeMapping[sh] : sh \in transactionShards[nextExecuteTx]}
\*    /\ rmState' = [rmState EXCEPT ![nextExecuteTx,i,-1] = "primaryLeader"]
\*    /\ clientRequests' = [clientRequests EXCEPT ![i] = Append(clientRequests[i], nextExecuteTx)]
\*    /\ pendingTransactions' = Tail(pendingTransactions)
\*    /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, msgs, localTransactionHistory, 
\*        localNodesGraph, msgsShards, test, localTransactionalGraph, catchUpID>>
   
   
   
   
\*  ReceiveClient(i) ==
\*    LET 
\*        clientRequest == Head(clientRequests[i])
\*    IN
\*        /\ Len(clientRequests[i]) > 0
\*        /\ PrimaryLeaderSendPrepares(clientRequest, i, transactions[clientRequest], transactionShards[clientRequest])
\*        /\ clientRequests' = [clientRequests EXCEPT ![i] = Tail(clientRequests[i])]
\*        
\*       /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, localTransactionHistory, 
\*        localNodesGraph  , pendingTransactions, rmState, msgs, test, localTransactionalGraph, catchUpID>>
\*  
  
  startTx(i) ==
  LET 
    nextExecuteTx == Head(pendingTransactions)
    IN
    /\ Len(pendingTransactions) > 0
    /\ i \in UNION{ShardNodeMapping[sh] : sh \in transactionShards[nextExecuteTx]}
\*    /\ (i = 1 /\ nextExecuteTx = 1) \/ (i = 1 /\ nextExecuteTx = 2) \/ (i = 3 /\ nextExecuteTx = 3)
\*    /\ i = LeaderMapping[nextExecuteTx]
    /\ PrimaryLeaderSendPrepares(nextExecuteTx, i, transactions[nextExecuteTx], transactionShards[nextExecuteTx])
    /\ pendingTransactions' = Tail(pendingTransactions)
    /\ rmState' = [r \in {nextExecuteTx}, y \in NODES, s \in (Shard \union {-1}), term \in {primaryCoordinatorTerm} |-> IF (y = i /\ s = -1)  THEN "primaryLeader" ELSE "follower"] @@ rmState
    
    /\ UNCHANGED <<currentTerm, lostMsgCount, failedNodesCount, failedNodes, transactionNumbers, 
        localNodesGraph, test, clientRequests, catchUpID,  localTransactionHistory, localTransactionalGraph, msgs>>
        
  RecvCatchUp(r, message) ==     
    /\ message.type = "catchUp"
    /\ r \in ShardNodeMapping[message.shard]
    /\ ServeCatchUp(r, message.src, message.shard, localTransactionHistory[r]["leadingEdge"], message.leadingEdge, message.ID)  
    /\ test' = test + 1
    /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, catchUpID, clientRequests, localNodesGraph, localTransactionHistory, localTransactionalGraph, msgsShards, pendingTransactions, rmState>>
   
   
   
   
  RecvCatchUpResponse(r, message) == 
    /\ message.type = "catchUpResponse"
    /\ r = message.dst
    /\ r # message.src
    /\ ServeCatchUpResponse(r, message.src, message.subGraph,  message.transactions, message.ID)
    /\ test' = test + 1
    /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, failedNodesCount, failedNodes, catchUpID, clientRequests, localNodesGraph, msgsShards, pendingTransactions, rmState>>
 
 
 
  FailNodes(r) ==
    /\ failedNodesCount < NumFailedNodes
    /\ failedNodes' = failedNodes \union {r}
    /\ failedNodesCount' = failedNodesCount + 1
    /\ test' = test + 1
    /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,lostMsgCount, rmState,msgs, clientRequests, localTransactionHistory, localTransactionalGraph,                        
            localNodesGraph, pendingTransactions, catchUpID, msgsShards>>
    
   ShardsMSGLost(m) == 
   /\ m.src \in failedNodes
   /\ msgsShards' = [msgsShards EXCEPT ![m] = 0]
   /\ lostMsgCount < NumLostMsg
   /\ lostMsgCount' = lostMsgCount + 1
   /\ test' = test + 1
   /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,rmState,msgs, clientRequests, localTransactionHistory, localTransactionalGraph,                        
            localNodesGraph, pendingTransactions, failedNodes, failedNodesCount, catchUpID>>
   
   MSGLost(m) == 
   /\ m.src \in failedNodes
   /\ msgs' = [msgs EXCEPT ![m] = 0]
   /\ lostMsgCount < NumLostMsg
   /\ lostMsgCount' = lostMsgCount + 1
   /\ test' = test + 1
   /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,rmState, msgsShards, clientRequests, localTransactionHistory, localTransactionalGraph,                        
            localNodesGraph, pendingTransactions, failedNodes, failedNodesCount, catchUpID>>
 
 
  Retry(r, tn, shard) == 
  /\ tn \in localTransactionHistory[r]["prepared"]
  /\ rmState[tn, r, shard, currentTerm[tn, r]] = "follower"
\*  /\ newCoordinator' = newCoordinator \union {r}
  /\ rmState' = [rmState EXCEPT ![tn, r, shard, currentTerm[tn, r]] = "coordinator"]
  /\ InterposedCoordinatorSendPrepares(tn, r, transactions[tn], {1}, shard, currentTerm[tn, r])
  /\ UNCHANGED <<primaryCoordinatorTerm,currentTerm,catchUpID, clientRequests, failedNodes, failedNodesCount, localNodesGraph, localTransactionHistory, localTransactionalGraph, lostMsgCount, pendingTransactions, test, msgsShards>>
  
  
  PrimaryCoordinatorRetry(r, tn, shard) ==
  /\ tn \in localTransactionHistory[r]["prepared"]
  /\ rmState[tn, r, shard, currentTerm[tn, r]] = "coordinator"
  /\ ~(rmState[tn, r, -1, currentTerm[tn, r]]) = "primaryLeader"
  /\ PrimaryLeaderSendPrepares(tn, r, transactions[tn], transactionShards[tn])
  /\ rmState' = [tx \in {tn}, y \in NODES, s \in (Shard \union {-1}), term \in {primaryCoordinatorTerm} |-> IF (y = r /\ s = -1)  THEN "primaryLeader" ELSE "follower"] @@ rmState
  /\ UNCHANGED <<currentTerm,catchUpID, msgs, localTransactionHistory, localTransactionalGraph, clientRequests, failedNodes, failedNodesCount, localNodesGraph, lostMsgCount, pendingTransactions, test>>

  
  
  
 tSet == { transactionNumbers[i] : i \in DOMAIN transactionNumbers } 
 
 
 Init ==   
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [r \in tSet, y \in NODES, s \in (Shard \union {-1}), term \in {1} |-> "follower"]
  /\ msgs = [m \in {} |-> 0]
  /\ msgsShards = [m \in {} |-> 0]
  /\ pendingTransactions = transactionNumbers
  /\ clientRequests = [r \in NODES |-> <<>>]
  /\ localNodesGraph = [r \in NODES |-> {}]
  /\ localTransactionHistory = [r \in NODES |-> 
        [
            i \in {"committed","leadingEdge","prepared", "aborted", "heuristic" } |-> {}
        ]
     ]
\*  /\ tnState = [r \in tSet, t \in NODES |-> "unknown"]
  /\ localTransactionalGraph = [n \in NODES |->[ m \in {} |-> {}]]
  /\ catchUpID = [n \in NODES |-> 1]
  /\ failedNodesCount = 0
  /\ failedNodes = {}
  /\ lostMsgCount = 0
\*  /\ primaryCoordinatorID = [n \in NODES |-> {}]
  /\ primaryCoordinatorTerm = 1
  /\ currentTerm = [r \in tSet, n \in NODES|-> 1]
  /\ test = 0
  

  
  Next ==
   \/ \E i \in NODES, m \in ValidMessage(msgs) :  
            /\ RecvPrepare(i,m)
            /\ ~(i \in failedNodes)
   \/ \E i \in NODES, m \in ValidMessage(msgs) : 
            /\ RecvCommit(i,m)
            /\ ~(i \in failedNodes)
   \/ \E m \in ValidMessage(msgs) : 
            /\ RecvPrepared(m)
            /\ ~(m.dst \in failedNodes)
   \/ \E m \in ValidMessage(msgs) : 
            /\ RecvAborted(m)
            /\ ~(m.dst \in failedNodes)
   \/ \E i \in NODES, m \in ValidMessage(msgs) : 
            /\ RecvAbort(i,m)
            /\ ~(i \in failedNodes)
   \/ \E i \in NODES : 
            /\ startTx(i)
            /\ ~(i \in failedNodes)
   \/ \E i \in NODES, m \in ValidMessage(msgsShards) : 
            /\ InterposedCoordinatorRecvPrepareMsgFromCoordinator(i, m)
            /\ ~(i \in failedNodes)
   \/ \E i \in NODES, m \in ValidMessage(msgsShards) : 
            /\ InterposedCoordinatorRecvCommitMsgFromCoordinator(i, m)
            /\ ~(i \in failedNodes)
   \/ \E i \in NODES, m \in ValidMessage(msgsShards) : 
            /\ InterposedCoodinatorRecvAbortMsgFromCoordinator(i, m) 
            /\ ~(i \in failedNodes)
   \/ \E m \in ValidMessage(msgsShards) : 
            /\ PimaryLeaderRecvLeaderCommitResponse(m)
            /\ ~(m.dst \in failedNodes)
   \/ \E m \in ValidMessage(msgsShards) : 
            /\ PrimaryLeaderRecvLeaderAbortResponse(m)
            /\ ~(m.dst \in failedNodes)
   \/ \E i \in NODES, m \in ValidMessage(msgsShards) : 
            /\ CoordinatorRecvCommitResponse(i, m)
            /\ ~(i \in failedNodes)
   \/ \E i \in NODES, m \in ValidMessage(msgsShards) : 
            /\ InterposedCoordinatorRecvCommitResponse(i, m)
            /\ ~(i \in failedNodes)
   \/ \E i \in NODES, m \in ValidMessage(msgs) : 
            /\ RecvCatchUp(i, m)
            /\ ~(i \in failedNodes)
   \/ \E i \in NODES, m \in ValidMessage(msgs) : 
            /\ RecvCatchUpResponse(i, m)
            /\ ~(i \in failedNodes)
            
            
   \/ \E i \in NODES : FailNodes(i)
   \/ \E i \in NODES, tn \in tSet: Retry(i, tn, ServerShard(i))
   \/ \E i \in NODES, tn \in tSet: PrimaryCoordinatorRetry(i, tn, ServerShard(i))
   \/ \E m \in ValidMessage(msgsShards) : ShardsMSGLost(m)
   \/ \E m \in ValidMessage(msgs): MSGLost(m)
      
   
      
      
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
    test < 27 /\ Cardinality(DOMAIN(msgs)) < 35 /\ Cardinality(DOMAIN(msgsShards)) < 35
    
  DummyInvariant3 == 
    Cardinality(localNodesGraph[1]) = 0 
 
  LeadingEdgeInvariant ==
  LET 
    newCommitted(r) == localTransactionHistory[r]["committed"] 
    committedTxDag(r) == [i \in newCommitted(r) |-> localTransactionalGraph[r][i] \intersect newCommitted(r)]
  IN
  \A n1, n2 \in NODES :
    localTransactionHistory[n1]["leadingEdge"] = localTransactionHistory[n2]["leadingEdge"] =>
      committedTxDag(n1) = committedTxDag(n2)
      
      
  CommitAbortInvariant ==
   \A m1, m2 \in DOMAIN(msgs) :
      /\ (m1.type = "commit")
      /\ (m2.type = "abort")
      /\ ("tn" \in DOMAIN(m1))
      /\ ("tn" \in DOMAIN(m2))
      => m1.tn # m2.tn
        
    
\*Spec == Init /\ [][Next]_<<localNodesGraph>>
\*THEOREM Spec => <> (Cardinality(localNodesGraph[1]) = 1)

LivenessDummy == <> (Cardinality(localNodesGraph[1]) = 1)

GraphEqual == \A i, j \in NODES : localNodesGraph[i] = localNodesGraph[j]

EventuallyEqualGraph == <>GraphEqual
  
\*
    
\*    \/ Cardinality(localTransactionHistory[1]["prepared"]) = 1) /\
\*     ~(Cardinality(localTransactionHistory[1]["prepared"]) = 2)
    
\*   /\Cardinality(localTransactionHistory[2]["prepared"]) = 0 \/ Cardinality(localTransactionHistory[2]["prepared"]) = 2
\*   /\Cardinality(localTransactionHistory[3]["prepared"]) = 0 \/ Cardinality(localTransactionHistory[3]["prepared"]) = 2





  
  
    
\*  ParticipantRecvPhase2(r, tn) == 
  
  
=============================================================================
