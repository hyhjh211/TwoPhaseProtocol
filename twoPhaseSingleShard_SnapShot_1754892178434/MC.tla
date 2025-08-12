---- MODULE MC ----
EXTENDS twoPhaseSingleShard, TLC

\* CONSTANT definitions @modelParameterConstants:0transactionNumbers
const_1754892174623102000 == 
<<1,2,3>>
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1754892174624103000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 5, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2NumLostMsg
const_1754892174624104000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3transactionShards
const_1754892174624105000 == 
<<{1}, {1}, {1}>>
----

\* CONSTANT definitions @modelParameterConstants:4Shard
const_1754892174624106000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5NumFailedNodes
const_1754892174624107000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6ShardNodeMapping
const_1754892174624108000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:7NODES
const_1754892174624109000 == 
{1,2,3}
----

=============================================================================
\* Modification History
\* Created Mon Aug 11 14:02:54 CST 2025 by junhaohu
