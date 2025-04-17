---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1744911662479175000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1744911662480176000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 2]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1744911662480177000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Fri Apr 18 01:41:02 CST 2025 by junhaohu
