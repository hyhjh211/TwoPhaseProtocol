------------------------------- MODULE graph -------------------------------
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
  
  localNodesGraph, \* localNodesGraph[nodes] is a graph
                     
  acceptedTransactions, \* acceptedTransactions[tn] is the set of nodes that have sent accept for transaction tn
  rejectedTransactions,  \* rejectedTransactions[tn] is the set of nodes that have sent reject for transaction tn
  pendingTransactions, \* set of transactions to be executed 
  tnState, \* intra shard transactions node state mapping 
  tnShardState, \* inter shards transactions node state mapping if receiver or sender is in the other shard
  test

  
\*msgs' = msgs \cup {[type |-> "Prepared", prepareN |->prepareInfo, dependency |-> depdencyInfo, rm |-> r]}


Vertex == [NodeID|-> Int, neighbours |->{}]
Graph == {Vertex}
   
   
   
   
   
   
ValidMessage(messages) ==
    { m \in DOMAIN messages : messages[m] > 0 }

WithMessage(m, messages) ==
    IF m \in DOMAIN msgs THEN
        [messages EXCEPT ![m] = messages[m] + 1]
    ELSE
        messages @@ (m :> 1)
    
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
  [type : {"preparedResponsePhase1", "abortedResponsePhase1", "prepared","aborted", "committed"}, tn:  transactionNumbers, dependency : SUBSET transactionNumbers, src : NODES, dst : NODES, operations: Seq(OperationSet), shard: Shard, shards: SUBSET Shard]  
  \cup [type : { "preparedResponse", "abortedResponse", "prepared","aborted", "committed"}, tn:  transactionNumbers, dependency : SUBSET transactionNumbers, src : NODES, dst : NODES, operations: Seq(OperationSet), shard: Shard, shards: SUBSET Shard ]  
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
  
  
\* LeaderPrepare(tnInfo, s, r, depdencyInfo, tnOperations) == 
\*  (*************************************************************************)
\*  (* leader s sends prepare message to follower r                           *)
\*  (*************************************************************************)
\*  /\ rmState[tnInfo, s] = "leader"
\*  /\ rmState[tnInfo, r] = "follower" 
\*  /\ Len(msgs[r][s]) \geq 0
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(@, [type |-> "prepared", tn |->tnInfo, dependency |-> depdencyInfo, src |-> s, dst |-> r, operations |-> tnOperations])]
\*  /\ msgs' = [msgs EXCEPT ![r][s] = Append(msgs[r][s], "aaa")]

 
  LeaderSendPrepares(tnInfo, s, tnOperations, shardsInfo, shardInfo) ==
  (*************************************************************************)
  (* leader s sends prepare message to all followers                       *)
  (*************************************************************************) 
        /\ Send([type |-> "prepared", 
                tn |->tnInfo, 
                dependency |-> localTransactionHistory[s]["recentCommitted"], 
                src |-> s, 
                dst |-> -1, 
                operations |-> tnOperations,
                shard |-> shardInfo, 
                shards |-> shardsInfo
                ])
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
  
  
  LeaderSendCommit(tnInfo, s, depdencyInfo, tnOperations, shardsInfo, shardInfo) == 
  (*************************************************************************)
  (* leader s sends commit message to all followers                        *)
  (*************************************************************************) 
  /\ rmState[tnInfo, s, shardInfo] = "leader"
  /\ Send([type |-> "committed", 
            tn |-> tnInfo, 
            dependency |-> depdencyInfo, 
            src |-> s, 
            dst |-> -1, 
            operations |-> tnOperations,
            shards |-> shardsInfo,
            shard |-> shardInfo
     ])
  /\ tnState' = [tnState EXCEPT ![tnInfo, s] = "sendCommit"]

    
  
  
  
  
  
\*  LeaderAbort(tnInfo, r, s, depdencyInfo, tnOperations) ==
\*  (*********************************************************************************)
\*  (* leader s spontaneously aborts the transaction and send the abort message to r.*)
\*  (*********************************************************************************)
\*  /\ rmState[tnInfo, s] = "leader"
\*  /\ rmState[tnInfo, r] = "follower"
\*  /\ msgs[r][s]' = Append(msgs[r][s], [type |-> "aborted", tn|-> tnInfo, src |-> s, dst |-> r, operations |-> tnOperations])
  
  
  LeaderSendAbort(tnInfo, s, depdencyInfo, tnOperations, shardsInfo, shardInfo) ==
  (*********************************************************************************)
  (* leader s sends the abort message to everyone.*)
  (*********************************************************************************)
  /\ rmState[tnInfo, s, shardInfo] = "leader"
  /\ Send([type |-> "aborted", 
           tn|-> tnInfo, 
           dependency |-> depdencyInfo, 
           src |-> s, 
           dst |-> -1, 
           operations |-> tnOperations,
           shards |-> shardsInfo,
           shard |-> shardInfo
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
  
RecvPhase1(tnInfo, r, s, depdencyInfo, tnOperations, shardsInfo, shardInfo) == 
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
                     operations |-> tnOperations,
                     shards |-> shardsInfo,
                     shard |-> shardInfo
                ])
            /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "sendPreparedResponsePhase1"]
            /\ acceptedTransactions' = [acceptedTransactions EXCEPT ![tnInfo] = @ \union {r}]
            /\ test' = test + 1
            /\ UNCHANGED <<transactionNumbers, 
            localNodesGraph, rejectedTransactions, clientRequests, pendingTransactions, rmState, msgsShards, tnShardState>>
                
          ELSE
          
          /\ Send([type |-> "abortedResponsePhase1", 
                   tn |->  tnInfo, 
                   dependency |-> depdencyInfo, 
                   src |-> r, 
                   dst |-> s, 
                   operations |-> tnOperations,
                   shards |-> shardsInfo,
                   shard |-> shardInfo
              ])
          /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "sendAbortedResponsePhase1"]
          /\ test' = test + 1
          /\ UNCHANGED <<transactionNumbers, 
            localNodesGraph, acceptedTransactions, rejectedTransactions, clientRequests, pendingTransactions, rmState, localTransactionHistory, msgsShards, tnShardState>>
               
  
  
  RcvAbortMsg(r, s, tnInfo, tnOperations, shardInfo) ==
  (*************************************************************************)
  (* node r receives aborted message from leader s                       *)
  (*************************************************************************)
   /\ rmState[tnInfo, s, shardInfo] = "leader"
   /\ localTransactionHistory' = [ localTransactionHistory EXCEPT  ![r]["prepared"] = localTransactionHistory[r]["prepared"]  \ {tnInfo}]
   /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "aborted"]
   /\ test' = test + 1
   /\ UNCHANGED <<rmState, msgs, transactionNumbers, clientRequests, localNodesGraph, 
    acceptedTransactions, rejectedTransactions, pendingTransactions, msgsShards, tnShardState>>
  
  
  
  RcvCommitMsg(r, s, tnInfo, depdencyInfo, tnOperations, shardInfo) == 
  (*************************************************************************)
  (* node r receives committed message from leader s                       *)
  (*************************************************************************)
  /\ rmState[tnInfo, s, shardInfo] = "leader"
  /\ r \in acceptedTransactions[tnInfo]
  /\ localTransactionHistory' =  [ localTransactionHistory   EXCEPT ![r]["prepared"] = localTransactionHistory[r]["prepared"] \ {tnInfo}
                                                                           ,![r]["committed"] =  localTransactionHistory[r]["committed"] \cup {tnInfo}
                                                                           ,![r]["recentCommitted"] = (localTransactionHistory[r]["recentCommitted"] \ depdencyInfo) \union {tnInfo}]                                                                        
  /\ localNodesGraph' = [localNodesGraph EXCEPT! [r] = Apply(tnOperations, r, localNodesGraph[r])]
  /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "committed"]
  /\ test' = test + 1
  /\ UNCHANGED <<transactionNumbers, msgs, rmState, clientRequests, 
    acceptedTransactions, rejectedTransactions, pendingTransactions, msgsShards, tnShardState>>
\*  /\ UNCHANGED <<tmState, 
  
  
  
  
  LeaderFowardSingleShardCommit(tnInfo, r, dependencyInfo, tnOperations, shardsInfo, shardInfo) ==
   LET 
       primaryLeader == CHOOSE n \in NODES : rmState[tnInfo, n, -1] = "primaryLeader"
   IN
       /\ SendShardMsg([type |-> "preparedResponse", 
                            tn |-> tnInfo, 
                            dependency |-> dependencyInfo,
                            src |-> r,
                            dst |-> primaryLeader,
                            operations |-> tnOperations,
                            shards |-> shardsInfo,
                            shard |-> shardInfo])
       /\ tnShardState' = [tnShardState EXCEPT ![tnInfo, r] = "fowardCommitted"]
       /\ tnState' = [tnState EXCEPT ![tnInfo, r] = "fowardCommitted"]
  
  
  
  
  
  
  LeaderFowardSingleShardAbort(tnInfo, r, dependencyInfo, tnOperations, shardsInfo, shardInfo) ==
  LET 
       primaryLeader == CHOOSE n \in NODES : rmState[tnInfo, n, -1] = "primaryLeader"
   IN
       /\ SendShardMsg([type |-> "abortedResponse", 
                            tn |-> tnInfo, 
                            dependency |-> dependencyInfo,
                            src |-> r,
                            dst |-> primaryLeader,
                            operations |-> tnOperations,
                            shards |-> shardsInfo,
                            shard |-> shardInfo])
       /\ tnShardState' = [tnShardState EXCEPT ![tnInfo, r] = "fowardAborted"]
  
                            


  LeaderHandleCommit(tnInfo, r, msg) ==
  (*******************************************************************************************************************************)
  (*Leader r received preparedResponsePhase1 from other nodes,                                                                   *)
  (*if majority have votes preparedResponsePhase1. then votes commit                                                             *)
  (*******************************************************************************************************************************)
    /\ rmState[tnInfo, r, msg.shard] = "leader"             
    /\ \E MS \in Quorum(msg.shard):    
        LET 
            
            mset == {m \in ValidMessage(msgs) : /\ m.type = "preparedResponsePhase1"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                                  /\ m.shard = msg.shard
                                  /\ m.shards = msg.shards
                                  /\ m.src  \in MS}
            
            
        IN  /\ \A ac \in MS : \E m \in mset : m.src = ac
\*            /\ LeaderSendCommit(tnInfo, r, msg.dependency, msg.operations)
            /\ LeaderFowardSingleShardCommit(msg.tn, r, msg.dependency, msg.operations, msg.shards, msg.shard)
     /\ test' = test + 1
     /\ UNCHANGED <<transactionNumbers, msgs, rmState, clientRequests, localTransactionHistory, localNodesGraph, 
                        rejectedTransactions, pendingTransactions, acceptedTransactions, clientRequests, localNodesGraph, localTransactionHistory, pendingTransactions, rejectedTransactions, rmState>>
 
            
            
            
            
            
  LeaderHandleAbort(tnInfo, r, msg) ==
  (*********************************************************************************)
  (*Leader r received abortedResponsePhase1 from other nodes,                      *)
  (*if majority have votes abortedResponsePhase1. then votes abort                 *)
  (*********************************************************************************)
    /\ rmState[tnInfo, r, msg.shard] = "leader"             
    /\ \E MS \in Quorum(msg.shard):   
        LET 
            
            mset == {m \in ValidMessage(msgs) : /\ m.type = "abortedResponsePhase1"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                                  /\ m.shard = msg.shard
                                  /\ m.shards = msg.shards
                                  /\ m.src  \in MS}
            
            
        IN  /\ \A ac \in MS : \E m \in mset : m.src = ac
\*            /\ LeaderSendAbort(tnInfo, r, msg.dependency, msg.operations)
            /\ LeaderFowardSingleShardAbort(tnInfo, r, msg.dependency, msg.operations, msg.shards, msg.shard)
     /\ test' = test + 1
     /\ UNCHANGED <<transactionNumbers, rmState, clientRequests, localTransactionHistory, localNodesGraph, 
                        rejectedTransactions, pendingTransactions, acceptedTransactions, clientRequests, localNodesGraph, localTransactionHistory, pendingTransactions, rejectedTransactions, msgs, tnState>>           
            
       
            
            
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
            
  
   PrimaryLeaderHandleCommit(tnInfo, r, msg) ==
   LET 
            
      mset == {m \in ValidMessage(msgsShards) : /\ m.type = "preparedResponse"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                    }
      commitMsg == [ m \in { 
                          [type |-> "committed", 
                            tn |-> tnInfo, 
                            dependency |-> msg.dependency, 
                            src |-> s, 
                            dst |-> -1, 
                            operations |-> msg.operations,
                            shards |-> msg.shards,
                            shard |-> s
                          ]
                          : s \in msg.shards
                            } 
                   |-> 1 ]
   IN
       /\ Cardinality(mset) = Cardinality(msg.shards)
       /\ msgsShards' = msgsShards @@ commitMsg
       /\ tnShardState' = [tnShardState EXCEPT ![tnInfo, r] = "primarySendCommitted"]
   
   
   
   
   
   PimaryLeaderHandleAbort(tnInfo, r, msg) ==
   LET 
            
      mset == {m \in ValidMessage(msgsShards) : /\ m.type = "abortedResponse"
                                  /\ m.dst = r
                                  /\ m.tn  = tnInfo
                    }
      commitMsg == [ m \in { 
                          [type |-> "aborted", 
                            tn |-> tnInfo, 
                            dependency |-> msg.dependency, 
                            src |-> s, 
                            dst |-> -1, 
                            operations |-> msg.operations,
                            shards |-> msg.shards,
                            shard |-> s
                          ]
                          : s \in msg.shards
                            } 
                   |-> 1 ]
   IN
       /\ Cardinality(mset) > 0
       /\ msgsShards' = msgsShards @@ commitMsg
       /\ tnShardState' = [tnShardState EXCEPT ![tnInfo, r] = "primarySendAborted"]
   
   
   PrimaryLeaderSendPrepares(tnInfo, s, tnOperations, shardsInfo) ==
   LET 
   prepareMsg == [ m \in { 
                          [type |-> "prepared", 
                            tn |-> tnInfo, 
                            dependency |-> localTransactionHistory[s]["recentCommitted"],
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
      /\ msgsShards' = msgsShards @@ prepareMsg
      /\ tnShardState' = [tnShardState EXCEPT! [tnInfo, s] = "primarySendPrepared"]
      
      
      
      
   LeaderRecvPrepareMsgFromPrimaryLeader(r, msg) ==
   LET 
       NoLeaderExist == \A x \in ShardNodeMapping[msg.shard], s \in {msg.shard} \union {-1} : rmState[msg.tn, x, s] = "follower" 
   IN 
      /\ r \in ShardNodeMapping[msg.shard]
      /\ 
        \/ 
           /\ NoLeaderExist
           /\ tnShardState[msg.tn, r] = "unknown"
            
        \/ 
           /\ rmState[msg.tn, r, -1] = "primaryLeader"
           /\ rmState[msg.tn, r, msg.shard] = "follower"
           /\ tnShardState[msg.tn, r] = "primarySendPrepared"
      
      /\ rmState' = [rmState EXCEPT! [msg.tn, r, msg.shard] = "leader"]
      /\ LeaderSendPrepares(msg.tn, r, msg.operations, msg.shards, msg.shard)
      /\ tnShardState' = [tnShardState EXCEPT![msg.tn, r] = "leaderRcvPrepare"]
      /\ test' = test + 1
      /\ UNCHANGED <<acceptedTransactions, clientRequests, localNodesGraph, localTransactionHistory, msgsShards, pendingTransactions, rejectedTransactions>>
      
      
      
      
   LeaderRecvCommitMsgFromPrimaryLeader(r, msg) ==
   /\ msg.type = "committed"
   /\ rmState[msg.tn, r, msg.shard] = "leader"
   /\ 
        \/ tnShardState[msg.tn, r] = "fowardCommitted"
        \/ tnShardState[msg.tn, r] = "primarySendCommitted"  \*  primary leader should be aboe to recv the commit msg even itself sent out committed
   /\ LeaderSendCommit(msg.tn, r, msg.dependency, msg.operations, msg.shards, msg.shard)
   /\ tnShardState' = [tnShardState EXCEPT! [msg.tn, r] = "recvCommitFromPrimary"]
   /\ test' = test + 1
   /\ UNCHANGED <<acceptedTransactions, clientRequests, localNodesGraph, localTransactionHistory, msgsShards, pendingTransactions, rejectedTransactions, rmState>>
   
   
   LeaderRecvAbortMsgFromPrimaryLeader(r, msg) ==
   /\ msg.type = "aborted"
   /\ rmState[msg.tn, r, msg.shard] = "leader"
   /\
        \/ tnShardState[msg.tn, r] = "fowardCommitted"
        \/ tnShardState[msg.tn, r] = "fowardAborted"
        \/ tnShardState[msg.tn, r] = "primarySendAborted" \*  primary leader should be aboe to recv the commit msg even itself sent out aborted
   /\ LeaderSendAbort(msg.tn, r, msg.dependency, msg.operations, msg.shards, msg.shard)
   /\ tnShardState' = [tnShardState EXCEPT! [msg.tn, r] = "recvAbortFromPrimary"]
   /\ test' = test + 1
   /\ UNCHANGED <<acceptedTransactions, clientRequests, localNodesGraph, localTransactionHistory, msgsShards, pendingTransactions, rejectedTransactions, rmState>>
   
   
   
   PimaryLeaderRecvLeaderCommitResponse(msg) ==
   /\ msg.type = "preparedResponse"
   /\ rmState[msg.tn, msg.dst, -1] = "primaryLeader"
   /\ 
        \/tnShardState[msg.tn, msg.dst] = "primarySendPrepared"
        \/tnShardState[msg.tn, msg.dst] = "fowardCommitted" \*  primary leader should be aboe to recv the commit msg even itself sent out fowardCommitted
   /\ PrimaryLeaderHandleCommit(msg.tn, msg.dst, msg)
   /\ test' = test + 1
   /\ UNCHANGED << acceptedTransactions, clientRequests, localNodesGraph, localTransactionHistory, msgs, pendingTransactions, rejectedTransactions, rmState, tnState>>
   
   
   
   PrimaryLeaderRecvLeaderAbortResponse(msg) ==
   /\ msg.type = "abortedResponse"
   /\ rmState[msg.tn, msg.dst, -1] = "primaryLeader"
   /\ 
        \/tnShardState[msg.tn, msg.dst] = "primarySendPrepared"
        \/tnShardState[msg.tn, msg.dst] = "fowardAborted"
   /\ PimaryLeaderHandleAbort(msg.tn, msg.dst, msg) 
   /\ test' = test + 1
   /\ UNCHANGED <<acceptedTransactions, clientRequests, localNodesGraph, localTransactionHistory, msgs, pendingTransactions, rejectedTransactions, rmState, tnState>> 
      
       
   
\*   ReceiveClient(i) ==
\*    LET 
\*        clientRequest == Head(clientRequests[i])
\*    IN
\*        /\ Len(clientRequests[i]) > 0
\*        /\ LeaderSendPrepares(clientRequest, i, transactions[clientRequest])
\*        /\ clientRequests' = [clientRequests EXCEPT ![i] = Tail(clientRequests[i])]
\*        
\*       /\ UNCHANGED <<transactionNumbers, localTransactionHistory, 
\*        localNodesGraph, acceptedTransactions, rejectedTransactions, pendingTransactions, rmState, test>>    
       


  RecvPrepared(r, msg) ==
   /\ msg.type = "prepared" 
   /\ r \in ShardNodeMapping[msg.shard]
   /\  
       \/tnState[msg.tn, r] = "unknown"   \*   other ndoes didn't know the new transaction 
       \/tnState[msg.tn, r] = "sendPrepared"   \*   the node sent out send prepared should still able to recv its own prepare message 
    \*      (tnInfo, r, s, depdencyInfo, tnOperations)
   /\ RecvPhase1(msg.tn, r, msg.src, msg.dependency, msg.operations, msg.shards, msg.shard)
 
            
            
  RecvPreparedResponsePhase1(msg) ==
   /\ msg.type = "preparedResponsePhase1" 
   /\ msg.dst \in ShardNodeMapping[msg.shard]
   /\             
       \/tnState[msg.tn, msg.dst] = "sendPrepared"
       \/tnState[msg.tn, msg.dst] = "sendPreparedResponsePhase1" \*   leader should be aboe to recv reponse from other nodes even itself sent out prepare
       \/tnState[msg.tn, msg.dst] = "sendAbortedResponsePhase1" \*   leader should be aboe to recv reponse from other nodes even itself sent out abort
   /\ LeaderHandleCommit(msg.tn, msg.dst, msg)
   
  
  RecvAbortedResponsePhase1(msg) ==
   /\ msg.type = "abortedResponsePhase1"
   /\ msg.dst \in ShardNodeMapping[msg.shard]
   /\             
       \/tnState[msg.tn, msg.dst] = "sendPrepared"
       \/tnState[msg.tn, msg.dst] = "sendPreparedResponsePhase1"
       \/tnState[msg.tn, msg.dst] = "sendAbortedResponsePhase1"
   /\ LeaderHandleAbort(msg.tn, msg.dst, msg)
  
    
    
    
   RecvCommit(r, msg) ==
   /\ msg.type = "committed"
   /\ r \in ShardNodeMapping[msg.shard]
   /\ 
        \/ tnState[msg.tn, r] = "sendPreparedResponsePhase1"
        \/ tnState[msg.tn, r] = "sendCommit"
   /\ RcvCommitMsg(r, msg.src, msg.tn, msg.dependency,  msg.operations, msg.shard)
   
   
  RecvAbort(r,msg) ==
  /\ msg.type = "aborted"
  /\ r \in ShardNodeMapping[msg.shard]
  /\ 
      \/ tnState[msg.tn, r] = "sendPreparedResponsePhase1" 
      \/ tnState[msg.tn, r] = "sendAbortedResponsePhase1"
      \/ tnState[msg.tn, r] = "sendAbort"
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
        localNodesGraph, acceptedTransactions, rejectedTransactions, tnState, msgsShards, tnShardState, test>>
   
   
   
   
   
  ReceiveClient(i) ==
    LET 
        clientRequest == Head(clientRequests[i])
    IN
        /\ Len(clientRequests[i]) > 0
        /\ PrimaryLeaderSendPrepares(clientRequest, i, transactions[clientRequest], transactionShards[clientRequest])
        /\ clientRequests' = [clientRequests EXCEPT ![i] = Tail(clientRequests[i])]
        
       /\ UNCHANGED <<transactionNumbers, localTransactionHistory, 
        localNodesGraph, acceptedTransactions, rejectedTransactions, pendingTransactions, rmState, msgs, tnState, test>>
           
        
        
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
            i \in {"committed","recentCommitted","prepared" } |-> {}
        ]
    ]
  /\ acceptedTransactions = [tn \in tSet |-> {}]
  /\ rejectedTransactions = [tn \in tSet |-> {}]
  /\ tnState = [r \in tSet, t \in NODES |-> "unknown"]
  /\ tnShardState = [r \in tSet, t \in NODES |-> "unknown"]
  /\ test = 0
  
  
  Next ==
\*      \/ \E i,j \in NODES : Receive(i, j)


      \/ \E i \in NODES, m \in ValidMessage(msgs) :  RecvPrepared(i,m)
      \/ \E i \in NODES, m \in ValidMessage(msgs) : RecvCommit(i,m)
      \/ \E m \in ValidMessage(msgs) : RecvPreparedResponsePhase1(m)
      \/ \E m \in ValidMessage(msgs) : RecvAbortedResponsePhase1(m)
      \/ \E i \in NODES, m \in ValidMessage(msgs) : RecvAbort(i,m)
      \/ \E i \in NODES : ClientRequest(i)
      \/ \E i \in NODES : ReceiveClient(i)
      \/ \E i \in NODES, m \in ValidMessage(msgsShards) : LeaderRecvPrepareMsgFromPrimaryLeader(i, m)
      \/ \E i \in NODES, m \in ValidMessage(msgsShards) : LeaderRecvCommitMsgFromPrimaryLeader(i, m)
      \/ \E i \in NODES, m \in ValidMessage(msgsShards) : LeaderRecvAbortMsgFromPrimaryLeader(i, m) 
      \/ \E m \in ValidMessage(msgsShards) : PimaryLeaderRecvLeaderCommitResponse(m)
      \/ \E m \in ValidMessage(msgsShards) : PrimaryLeaderRecvLeaderAbortResponse(m)
   
      
      
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
    test < 20 /\ Cardinality(DOMAIN(msgs)) < 15 /\ Cardinality(DOMAIN(msgsShards)) < 15
    
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
\* Last modified Mon May 05 20:41:45 CST 2025 by junhaohu
\* Created Sun Feb 16 22:23:24 CST 2025 by junhaohu