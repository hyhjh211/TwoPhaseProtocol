---- MODULE MC ----
EXTENDS graph, TLC

\* CONSTANT definitions @modelParameterConstants:0NODES
const_1744779314282171000 == 
{1,2,3}
----

\* CONSTANT definitions @modelParameterConstants:1transactions
const_1744779314282172000 == 
<<<<[type |-> "nodes" , Operation |-> "add", sourceVertex|-> 0], [type |-> "nodes" , Operation |-> "add", sourceVertex|-> 1], [type |-> "edges", Operation  |-> "add", sourceVertex |-> 0, desVertex |-> 1]>>, <<[type |-> "nodes", Operation |-> "add", sourceVertex |-> 2]>>>>
----

\* CONSTANT definitions @modelParameterConstants:2transactionNumbers
const_1744779314282173000 == 
<<1,2>>
----

=============================================================================
\* Modification History
\* Created Wed Apr 16 12:55:14 CST 2025 by junhaohu
