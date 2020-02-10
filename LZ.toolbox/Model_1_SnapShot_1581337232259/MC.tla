---- MODULE MC ----
EXTENDS LZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Processes
const_1581337206183176000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581337206183177000 == 
Permutations(const_1581337206183176000)
----

\* CONSTANT definitions @modelParameterConstants:1Signals
const_1581337206183178000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581337206183179000 == 
1..3
----

\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1581337206183180000 ==
EXT!TypeOK
----
=============================================================================
\* Modification History
\* Created Mon Feb 10 15:20:06 MSK 2020 by zakharov
