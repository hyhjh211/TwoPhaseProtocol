---- MODULE MC ----
EXTENDS twoPhaseSingleShard, TLC

\* CONSTANT definitions @modelParameterConstants:0transactionNumbers
const_17545917354052000 == 
<<1,2,3>>
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_17545917354053000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 5, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2NumLostMsg
const_17545917354054000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3transactionShards
const_17545917354055000 == 
<<{1}, {1}, {1}>>
----

\* CONSTANT definitions @modelParameterConstants:4Shard
const_17545917354056000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5NumFailedNodes
const_17545917354057000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6ShardNodeMapping
const_17545917354058000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:7NODES
const_17545917354059000 == 
{1,2,3}
----

=============================================================================
\* Modification History
\* Created Fri Aug 08 02:35:35 CST 2025 by junhaohu
