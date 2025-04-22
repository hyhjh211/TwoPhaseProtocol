---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_174532636434674000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_174532636434675000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 5]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_174532636434676000 == 
<<1>>
----

=============================================================================
\* Modification History
\* Created Tue Apr 22 20:52:44 CST 2025 by junhaohu
