---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1744779278358164000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1744779278358165000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 2]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1744779278358166000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Wed Apr 16 12:54:38 CST 2025 by junhaohu
