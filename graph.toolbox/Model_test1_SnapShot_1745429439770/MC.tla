---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_174542943668310000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_174542943668311000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_174542943668312000 == 
<<1>>
----

=============================================================================
\* Modification History
\* Created Thu Apr 24 01:30:36 CST 2025 by junhaohu
