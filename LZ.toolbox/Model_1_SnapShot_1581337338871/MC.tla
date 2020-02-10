---- MODULE MC ----
EXTENDS LZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Processes
const_1581337311783191000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581337311783192000 == 
Permutations(const_1581337311783191000)
----

\* CONSTANT definitions @modelParameterConstants:1Signals
const_1581337311783193000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581337311783194000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 15:21:51 MSK 2020 by zakharov
