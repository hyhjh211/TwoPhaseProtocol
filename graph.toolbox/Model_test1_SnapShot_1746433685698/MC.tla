---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1746433681580256000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1746433681580257000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1746433681580258000 == 
<<1,2>>
----

\* CONSTANT definitions @modelParameterConstants:3Shard
const_1746433681580259000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:4ShardNodeMapping
const_1746433681580260000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:5transactionShards
const_1746433681580261000 == 
<<{1}, {1}>>
----

=============================================================================
\* Modification History
\* Created Mon May 05 16:28:01 CST 2025 by junhaohu
