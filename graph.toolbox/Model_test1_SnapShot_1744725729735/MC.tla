---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_174472572665185000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_174472572665186000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "remove", sourceVertex |-> 0]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_174472572665187000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Tue Apr 15 22:02:06 CST 2025 by junhaohu
