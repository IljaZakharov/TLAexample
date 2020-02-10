---- MODULE MC ----
EXTENDS LZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Processes
const_1581344571519281000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581344571519282000 == 
Permutations(const_1581344571519281000)
----

\* CONSTANT definitions @modelParameterConstants:1Signals
const_1581344571519283000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581344571519284000 == 
1..3
----

\* PROPERTY definition @modelCorrectnessProperties:0
prop_1581344571519285000 ==
EXT!Spec
----
=============================================================================
\* Modification History
\* Created Mon Feb 10 17:22:51 MSK 2020 by zakharov
