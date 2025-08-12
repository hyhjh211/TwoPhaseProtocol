---- MODULE MC ----
EXTENDS twoPhaseSingleShard, TLC

\* CONSTANT definitions @modelParameterConstants:0transactionNumbers
const_175483991747982000 == 
<<1,2,3>>
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_175483991747983000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 5, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2NumLostMsg
const_175483991747984000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3transactionShards
const_175483991747985000 == 
<<{1}, {1}, {1}>>
----

\* CONSTANT definitions @modelParameterConstants:4Shard
const_175483991747986000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5NumFailedNodes
const_175483991747987000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6ShardNodeMapping
const_175483991747988000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:7NODES
const_175483991747989000 == 
{1,2,3}
----

=============================================================================
\* Modification History
\* Created Sun Aug 10 23:31:57 CST 2025 by junhaohu
