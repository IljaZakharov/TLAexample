-------------------------------- MODULE ELZ --------------------------------
EXTENDS Integers, TLC


(***************************************************************************)
(* This model describes the semantics of rendezvous signal exchange        *)
(* intended for C programs verification tools. These operations should not *)
(* be considered as regular operators for execution.                       *)
(***************************************************************************)

CONSTANTS Processes, \* The numbver of processes (threads actually) that can communicate. *\ 
          Signals,    \* The set of names of signal that can be sent by any thread. *\
          WorkingSet \* Values that can be assigned at any working step *\
                      
VARIABLES SigStates,     \* Describes the state of each signal transition. *\
          ProcStates,
          ProcValues,
          SigStorage    \* Describes the state of each process. *\
          
vars == <<SigStates, ProcStates, ProcValues, SigStorage>>


Flag(p,s) == /\ ProcStates[p] = "working"
             /\ ProcStates' = [ProcStates EXCEPT![p] = "ready"]
             /\ SigStates[s] = "idle"
             /\ SigStates' = [SigStates EXCEPT![s] = "waiting"]
             /\ UNCHANGED <<ProcValues, SigStorage>>

Send(p,s) == /\ ProcStates[p] = "working"   
             /\ SigStates[s] = "waiting"
             /\ SigStates' = [SigStates EXCEPT![s] = "set"]
             /\ SigStorage' = [SigStorage EXCEPT![s] = ProcValues[p]]
             /\ UNCHANGED <<ProcStates, ProcValues>>
                
Receive(p,s) == /\ ProcStates[p] = "ready"
                /\ SigStates[s] = "set"
                /\ ProcStates' = [ProcStates EXCEPT![p] = "working"]
                /\ ProcValues' = [ProcValues EXCEPT![p] = SigStorage[s]]
                /\ SigStates' = [SigStates EXCEPT![s] = "idle"]
                /\ UNCHANGED <<SigStorage>>
                  
Working(p) == /\ ProcStates[p] = "working"
              /\ \E i \in WorkingSet:  ProcValues' = [ProcValues EXCEPT![p] = i]
              /\ UNCHANGED <<ProcStates, SigStates, SigStorage>>

Init == /\ SigStates = [s \in Signals |-> "idle"]
        /\ SigStorage = [s \in Signals |-> 0]
        /\ ProcStates = [p \in Processes |-> "working"]
        /\ ProcValues = [p \in Processes |-> 0]        

Next == \E p \in Processes: \/ Working(p)
                            \/ \E s \in Signals: \/ Flag(p, s)
                                                 \/ Send(p, s)
                                                 \/ Receive(p, s)     

Spec == Init /\ [][Next]_vars

TypeOK == /\ SigStates \in [Signals -> {"idle", "waiting", "set"}]
          /\ SigStorage \in [Signals -> WorkingSet]
          /\ ProcStates \in [Processes -> {"working", "ready"}]
          /\ ProcValues \in [Processes -> WorkingSet]
          
PropPending ==  \E x \in Processes: ProcStates[x] = "ready" <=> \E s \in Signals: SigStates[s] # "idle"  

=============================================================================
\* Modification History
\* Last modified Mon Feb 10 15:09:42 MSK 2020 by zakharov
\* Created Fri Feb 07 12:23:21 MSK 2020 by zakharov
