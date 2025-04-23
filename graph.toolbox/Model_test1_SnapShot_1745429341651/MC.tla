---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_17454293302432000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_17454293302433000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_17454293302434000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Thu Apr 24 01:28:50 CST 2025 by junhaohu
