---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_174583462069911000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_174583462069912000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_174583462069913000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Mon Apr 28 18:03:40 CST 2025 by junhaohu
