---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_174360593671698000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_174360593671699000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1743605936716100000 == 
<<1>>
----

=============================================================================
\* Modification History
\* Created Wed Apr 02 22:58:56 CST 2025 by junhaohu
