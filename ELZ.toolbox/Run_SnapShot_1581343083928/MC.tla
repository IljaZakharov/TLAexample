---- MODULE MC ----
EXTENDS ELZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Signals
const_1581343079905206000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581343079905207000 == 
Permutations(const_1581343079905206000)
----

\* CONSTANT definitions @modelParameterConstants:1Processes
const_1581343079905208000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581343079905209000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 16:57:59 MSK 2020 by zakharov
