---- MODULE MC ----
EXTENDS ELZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Signals
const_1581336623574126000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581336623574127000 == 
Permutations(const_1581336623574126000)
----

\* CONSTANT definitions @modelParameterConstants:1Processes
const_1581336623574128000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581336623574129000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 15:10:23 MSK 2020 by zakharov
