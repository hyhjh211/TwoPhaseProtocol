---- MODULE MC ----
EXTENDS twoPhaseSingleShard, TLC

\* CONSTANT definitions @modelParameterConstants:0transactionNumbers
const_1753201678535418000 == 
<<1,2>>
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1753201678535419000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0, shard |-> 1], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1, shard |-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0, shard |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 1, shard |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2NumLostMsg
const_1753201678535420000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:3transactionShards
const_1753201678535421000 == 
<<{1}, {1}, {1}>>
----

\* CONSTANT definitions @modelParameterConstants:4Shard
const_1753201678535422000 == 
{1}
----

\* CONSTANT definitions @modelParameterConstants:5NumFailedNodes
const_1753201678535423000 == 
1
----

\* CONSTANT definitions @modelParameterConstants:6ShardNodeMapping
const_1753201678535424000 == 
[i \in {1} |-> {1,2,3}]
----

\* CONSTANT definitions @modelParameterConstants:7NODES
const_1753201678535425000 == 
{1,2,3}
----

=============================================================================
\* Modification History
\* Created Wed Jul 23 00:27:58 CST 2025 by junhaohu
