---- MODULE MC ----
EXTENDS ELZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Signals
const_1581336682729142000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581336682729143000 == 
Permutations(const_1581336682729142000)
----

\* CONSTANT definitions @modelParameterConstants:1Processes
const_1581336682729144000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581336682729145000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 15:11:22 MSK 2020 by zakharov
