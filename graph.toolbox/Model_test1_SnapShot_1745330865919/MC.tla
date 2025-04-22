---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1745330852787106000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1745330852787107000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1745330852787108000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Tue Apr 22 22:07:32 CST 2025 by junhaohu
