---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1745740732191417000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1745740732192418000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1745740732192419000 == 
<<1>>
----

=============================================================================
\* Modification History
\* Created Sun Apr 27 15:58:52 CST 2025 by junhaohu
