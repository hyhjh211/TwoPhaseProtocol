---- MODULE MC ----
EXTENDS twoPhaseSingleShard, TLC

\* CONSTANT definitions @modelParameterConstants:0transactionNumbers
const_1753116103586290000 == 
<<1,2>>
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1753116103586291000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 1, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2NumLostMsg
const_1753116103586292000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3transactionShards
const_1753116103586293000 == 
<<{1}, {1}>>
----

\* CONSTANT definitions @modelParameterConstants:4Shard
const_1753116103586294000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5NumFailedNodes
const_1753116103586295000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6ShardNodeMapping
const_1753116103586296000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:7NODES
const_1753116103586297000 == 
{1,2,3}
----

=============================================================================
\* Modification History
\* Created Tue Jul 22 00:41:43 CST 2025 by junhaohu
