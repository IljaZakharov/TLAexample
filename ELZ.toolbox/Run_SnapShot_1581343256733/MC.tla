---- MODULE MC ----
EXTENDS ELZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Signals
const_1581343251714231000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581343251714232000 == 
Permutations(const_1581343251714231000)
----

\* CONSTANT definitions @modelParameterConstants:1Processes
const_1581343251714233000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581343251714234000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 17:00:51 MSK 2020 by zakharov
