---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_174472584329898000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_174472584329899000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1744725843298100000 == 
<<1>>
----

=============================================================================
\* Modification History
\* Created Tue Apr 15 22:04:03 CST 2025 by junhaohu
