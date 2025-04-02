---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1743606197848116000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1743606197848117000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1743606197848118000 == 
<<1>>
----

=============================================================================
\* Modification History
\* Created Wed Apr 02 23:03:17 CST 2025 by junhaohu
