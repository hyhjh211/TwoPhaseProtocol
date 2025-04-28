---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_17458345810805000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_17458345810806000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_17458345810807000 == 
<<1>>
----

=============================================================================
\* Modification History
\* Created Mon Apr 28 18:03:01 CST 2025 by junhaohu
