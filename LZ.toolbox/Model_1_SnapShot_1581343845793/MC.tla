---- MODULE MC ----
EXTENDS LZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Processes
const_1581343828770276000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581343828770277000 == 
Permutations(const_1581343828770276000)
----

\* CONSTANT definitions @modelParameterConstants:1Signals
const_1581343828770278000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581343828770279000 == 
1..3
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1581343828770280000 ==
EXT!Spec
----
=============================================================================
\* Modification History
\* Created Mon Feb 10 17:10:28 MSK 2020 by zakharov
