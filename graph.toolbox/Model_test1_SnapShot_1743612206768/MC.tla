---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1743612203690212000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1743612203690213000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1743612203690214000 == 
<<1>>
----

=============================================================================
\* Modification History
\* Created Thu Apr 03 00:43:23 CST 2025 by junhaohu
