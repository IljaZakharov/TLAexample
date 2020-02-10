---- MODULE MC ----
EXTENDS ELZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Signals
const_1581342692581201000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581342692581202000 == 
Permutations(const_1581342692581201000)
----

\* CONSTANT definitions @modelParameterConstants:1Processes
const_1581342692581203000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581342692581204000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 16:51:32 MSK 2020 by zakharov
