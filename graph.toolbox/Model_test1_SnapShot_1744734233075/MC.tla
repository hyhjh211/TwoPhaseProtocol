---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1744734223969122000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1744734223969123000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1744734223969124000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Wed Apr 16 00:23:43 CST 2025 by junhaohu
