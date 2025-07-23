---- MODULE MC ----
EXTENDS twoPhaseSingleShard, TLC

\* CONSTANT definitions @modelParameterConstants:0transactionNumbers
const_1753116026593276000 == 
<<1,2>>
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1753116026593277000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 1, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2NumLostMsg
const_1753116026593278000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3transactionShards
const_1753116026593279000 == 
<<{1}, {1}>>
----

\* CONSTANT definitions @modelParameterConstants:4Shard
const_1753116026593280000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5NumFailedNodes
const_1753116026593281000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6ShardNodeMapping
const_1753116026593282000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:7NODES
const_1753116026593283000 == 
{1,2,3}
----

=============================================================================
\* Modification History
\* Created Tue Jul 22 00:40:26 CST 2025 by junhaohu
