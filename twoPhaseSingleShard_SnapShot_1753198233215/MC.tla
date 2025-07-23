---- MODULE MC ----
EXTENDS twoPhaseSingleShard, TLC

\* CONSTANT definitions @modelParameterConstants:0transactionNumbers
const_1753198220535346000 == 
<<1,2,3>>
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1753198220535347000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 1, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2NumLostMsg
const_1753198220535348000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3transactionShards
const_1753198220535349000 == 
<<{1}, {1}, {1}>>
----

\* CONSTANT definitions @modelParameterConstants:4Shard
const_1753198220535350000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5NumFailedNodes
const_1753198220535351000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6ShardNodeMapping
const_1753198220535352000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:7NODES
const_1753198220535353000 == 
{1,2,3}
----

=============================================================================
\* Modification History
\* Created Tue Jul 22 23:30:20 CST 2025 by junhaohu
