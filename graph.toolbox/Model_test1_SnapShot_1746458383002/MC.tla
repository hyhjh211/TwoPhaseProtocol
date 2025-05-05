---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1746458375950513000 == 
{1,2,3,4,5,6}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1746458375950514000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 2], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1746458375950515000 == 
<<1>>
----

\* CONSTANT definitions @modelParameterConstants:3Shard
const_1746458375950516000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:4ShardNodeMapping
const_1746458375950517000 == 
[i \in {1, 2} |-> IF i = 1 THEN {1,2, 3} ELSE {4,5,6}]
----

\* CONSTANT definitions @modelParameterConstants:5transactionShards
const_1746458375950518000 == 
<<{1,2}>>
----

=============================================================================
\* Modification History
\* Created Mon May 05 23:19:35 CST 2025 by junhaohu
