---- MODULE MC ----
EXTENDS LZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Processes
const_1581343696359251000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581343696359252000 == 
Permutations(const_1581343696359251000)
----

\* CONSTANT definitions @modelParameterConstants:1Signals
const_1581343696359253000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581343696359254000 == 
1..3
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1581343696359255000 ==
EXT!TypeOK
----
=============================================================================
\* Modification History
\* Created Mon Feb 10 17:08:16 MSK 2020 by zakharov
