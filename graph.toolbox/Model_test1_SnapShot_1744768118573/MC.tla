---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1744767029529152000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1744767029530153000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 5]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1744767029530154000 == 
<<1,2,3>>
----

=============================================================================
\* Modification History
\* Created Wed Apr 16 09:30:29 CST 2025 by junhaohu
