---- MODULE MC ----
EXTENDS LZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Processes
const_1581343788833266000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581343788833267000 == 
Permutations(const_1581343788833266000)
----

\* CONSTANT definitions @modelParameterConstants:1Signals
const_1581343788833268000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581343788833269000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 17:09:48 MSK 2020 by zakharov
