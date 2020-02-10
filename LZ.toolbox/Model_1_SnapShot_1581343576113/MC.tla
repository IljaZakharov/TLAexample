---- MODULE MC ----
EXTENDS LZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Processes
const_1581343573087241000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581343573087242000 == 
Permutations(const_1581343573087241000)
----

\* CONSTANT definitions @modelParameterConstants:1Signals
const_1581343573087243000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581343573087244000 == 
1..3
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1581343573087245000 ==
EXT!TypeOK
----
=============================================================================
\* Modification History
\* Created Mon Feb 10 17:06:13 MSK 2020 by zakharov
