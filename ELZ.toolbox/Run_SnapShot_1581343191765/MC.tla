---- MODULE MC ----
EXTENDS ELZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Signals
const_1581343186724216000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581343186724217000 == 
Permutations(const_1581343186724216000)
----

\* CONSTANT definitions @modelParameterConstants:1Processes
const_1581343186724218000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581343186724219000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 16:59:46 MSK 2020 by zakharov
