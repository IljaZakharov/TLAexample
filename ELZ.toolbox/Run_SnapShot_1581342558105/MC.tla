---- MODULE MC ----
EXTENDS ELZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Signals
const_1581342554082196000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581342554082197000 == 
Permutations(const_1581342554082196000)
----

\* CONSTANT definitions @modelParameterConstants:1Processes
const_1581342554082198000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581342554082199000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 16:49:14 MSK 2020 by zakharov
