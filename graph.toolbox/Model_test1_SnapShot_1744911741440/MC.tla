---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1744911737374179000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1744911737374180000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 2]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1744911737374181000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Fri Apr 18 01:42:17 CST 2025 by junhaohu
