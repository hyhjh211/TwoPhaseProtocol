---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1743605997802101000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1743605997802102000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1743605997802103000 == 
<<1>>
----

=============================================================================
\* Modification History
\* Created Wed Apr 02 22:59:57 CST 2025 by junhaohu
