---- MODULE MC ----
EXTENDS twoPhaseSingleShard, TLC

\* CONSTANT definitions @modelParameterConstants:0transactionNumbers
const_1753203624667592000 == 
<<1,2>>
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1753203624667593000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 1, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2NumLostMsg
const_1753203624667594000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3transactionShards
const_1753203624667595000 == 
<<{1}, {1}, {1}>>
----

\* CONSTANT definitions @modelParameterConstants:4Shard
const_1753203624667596000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5NumFailedNodes
const_1753203624667597000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6ShardNodeMapping
const_1753203624667598000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:7NODES
const_1753203624667599000 == 
{1,2,3}
----

=============================================================================
\* Modification History
\* Created Wed Jul 23 01:00:24 CST 2025 by junhaohu
