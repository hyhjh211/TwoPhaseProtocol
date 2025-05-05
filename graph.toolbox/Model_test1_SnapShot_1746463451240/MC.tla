---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1746462547689548000 == 
{1,2,3,4,5,6}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1746462547690549000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 2], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1746462547690550000 == 
<<1,2>>
----

\* CONSTANT definitions @modelParameterConstants:3Shard
const_1746462547690551000 == 
{1,2}
----

\* CONSTANT definitions @modelParameterConstants:4ShardNodeMapping
const_1746462547690552000 == 
[i \in {1, 2} |-> IF i = 1 THEN {1,2, 3} ELSE {4,5,6}]
----

\* CONSTANT definitions @modelParameterConstants:5transactionShards
const_1746462547690553000 == 
<<{1,2}, {1}>>
----

=============================================================================
\* Modification History
\* Created Tue May 06 00:29:07 CST 2025 by junhaohu
