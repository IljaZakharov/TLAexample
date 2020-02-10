---- MODULE MC ----
EXTENDS LZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Processes
const_1581343751038256000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581343751038257000 == 
Permutations(const_1581343751038256000)
----

\* CONSTANT definitions @modelParameterConstants:1Signals
const_1581343751038258000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581343751038259000 == 
1..3
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1581343751039260000 ==
EXT!TypeOK
----
=============================================================================
\* Modification History
\* Created Mon Feb 10 17:09:11 MSK 2020 by zakharov
