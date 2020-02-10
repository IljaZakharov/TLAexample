---- MODULE MC ----
EXTENDS LZ, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
x1, x2
----

\* MV CONSTANT definitions Processes
const_1581337246115186000 == 
{x1, x2}
----

\* SYMMETRY definition
symm_1581337246115187000 == 
Permutations(const_1581337246115186000)
----

\* CONSTANT definitions @modelParameterConstants:1Signals
const_1581337246115188000 == 
1..2
----

\* CONSTANT definitions @modelParameterConstants:2WorkingSet
const_1581337246115189000 == 
1..3
----

=============================================================================
\* Modification History
\* Created Mon Feb 10 15:20:46 MSK 2020 by zakharov
