---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_174470660093065000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_174470660093066000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 2]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_174470660093067000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Tue Apr 15 16:43:20 CST 2025 by junhaohu
