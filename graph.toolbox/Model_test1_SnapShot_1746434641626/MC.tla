---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1746434633512280000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1746434633512281000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1746434633512282000 == 
<<1,2>>
----

\* CONSTANT definitions @modelParameterConstants:3Shard
const_1746434633533283000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:4ShardNodeMapping
const_1746434633533284000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:5transactionShards
const_1746434633533285000 == 
<<{1}, {1}>>
----

=============================================================================
\* Modification History
\* Created Mon May 05 16:43:53 CST 2025 by junhaohu
