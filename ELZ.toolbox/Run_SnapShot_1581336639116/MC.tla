---- MODULE MC ----
EXTENDS ELZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Signals
const_1581336633080137000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581336633080138000 == 
Permutations(const_1581336633080137000)
----

\* CONSTANT definitions @modelParameterConstants:1Processes
const_1581336633080139000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581336633080140000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 15:10:33 MSK 2020 by zakharov
