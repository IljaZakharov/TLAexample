-------------------------------- MODULE ELZ --------------------------------
EXTENDS Integers, TLC


(***************************************************************************)
(* This model describes the semantics of rendezvous signal exchange        *)
(* intended for C programs verification tools. These operations should not *)
(* be considered as regular operators for execution.                       *)
(***************************************************************************)

CONSTANTS Processes,  \* The numbver of processes (threads actually) that can communicate. *\ 
          Signals,    \* The set of names of signal that can be sent by any thread. *\
          WorkingSet  \* Values that can be assigned at any working step *\
          
                      
VARIABLES SigStates,    \* Describes the state of each signal transition. *\
          ProcStates,   \* Process states: working or ready. *\
          ProcValues,   \* Current values stored per process *\
          SigStorage,   \* Describes the state of each process. *\
          ProcSignals  \* Specifies the signal that expected to be received *\
          
vars == <<SigStates, ProcStates, ProcValues, SigStorage, ProcSignals>>

(***************************************************************************)
(* At the very beginning, each process has a 0 value, and all processes    *)
(* have the same signal as a chosen one.                                   *)
(***************************************************************************)
Init == /\ SigStates = [s \in Signals |-> "idle"]
        /\ SigStorage = [s \in Signals |-> 0]
        /\ ProcStates = [p \in Processes |-> "working"]
        /\ ProcValues = [p \in Processes |-> 0]
        /\ ProcSignals = [p \in Processes |-> 0]        

(***************************************************************************)
(* At the very beginning, each process has a 0 value, and all processes    *)
(* have the same signal as a chosen one.                                   *)
(***************************************************************************)

(***************************************************************************)
(* At the working step, a process may change its values                    *)
(*  nondeterministically.                                                  *)
(***************************************************************************)
Working(p) == /\ ProcStates[p] = "working"
              /\ \E i \in WorkingSet:  ProcValues' = [ProcValues EXCEPT![p] = i]
              /\ UNCHANGED <<ProcStates, SigStates, SigStorage>>

(***************************************************************************)
(* Flag action shows other processes that this process wants to receive a  *) 
(* message.                                                                *)
(***************************************************************************)
Flag(p,s) == /\ ProcStates[p] = "working"
             /\ ProcStates' = [ProcStates EXCEPT![p] = "ready"]
             /\ SigStates[s] = "idle"
             /\ SigStates' = [SigStates EXCEPT![s] = "waiting"]
             /\ UNCHANGED <<ProcValues, SigStorage>>

(***************************************************************************)
(* Send value to any process that waits signal "s".                        *)
(***************************************************************************)
Send(p,s) == /\ ProcStates[p] = "working"   
             /\ SigStates[s] = "waiting"
             /\ SigStates' = [SigStates EXCEPT![s] = "set"]
             /\ SigStorage' = [SigStorage EXCEPT![s] = ProcValues[p]]
             /\ UNCHANGED <<ProcStates, ProcValues>>
                
(***************************************************************************)
(* A process can receive the value that was sent by another process.       *)
(***************************************************************************)
Receive(p,s) == /\ ProcStates[p] = "ready"
                /\ SigStates[s] = "set"
                /\ ProcSignals[p] = s
                /\ ProcStates' = [ProcStates EXCEPT![p] = "working"]
                /\ ProcValues' = [ProcValues EXCEPT![p] = SigStorage[s]]
                /\ SigStates' = [SigStates EXCEPT![s] = "idle"]
                /\ UNCHANGED <<SigStorage>>

(***************************************************************************)
(* This action is an artificial one and intended for choosing another      *)
(* signal by a process. It is crucial preventing the change of a           *) 
(* process'es signal when it is in the "ready" state.                      *)
(***************************************************************************)
ChangeSignal(p) == /\ ProcStates[p] = "working"
                   /\ \E s \in Signals: ProcSignals' = [ProcSignals EXCEPT![p] = s]
                   /\ UNCHANGED <<SigStates, ProcStates, ProcValues, SigStorage>> 

(***************************************************************************)
(* This action is an artificial one and intended for choosing another      *)
(* signal by a process. It is crucial preventing the change of a           *) 
(* process'es signal when it is in the "ready" state.                      *)
(***************************************************************************)

(***************************************************************************)
(* Each step a process may either work, change its signal, flag and then   *)
(* receive a signal or send any signal.                                    *)
(***************************************************************************)
Next == \E p \in Processes: \/ Working(p)
                            \/ ChangeSignal(p)
                            \/ \E s \in Signals: \/ Flag(p, s)
                                                 \/ Send(p, s)
                                                 \/ Receive(p, s)     

(***************************************************************************)
(* The formula describes the behaviour of the model.                       *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The formula below is a type invariant.                                  *)
(***************************************************************************)
TypeOK == /\ SigStates \in [Signals -> {"idle", "waiting", "set"}]
          /\ SigStorage \in [Signals -> WorkingSet \cup {0}]
          /\ ProcStates \in [Processes -> {"working", "ready"}]
          /\ ProcValues \in [Processes -> WorkingSet \cup {0}]
          /\ ProcSignals \in [Processes -> Signals \cup {0}]
          
(***************************************************************************)
(* The formula below shows the correspondence between signals and          *)
(* processes.                                                              *)
(***************************************************************************)
PropPending ==  \E x \in Processes: ProcStates[x] = "ready" <=> \E s \in Signals: SigStates[s] # "idle"

=============================================================================
\* Modification History
\* Last modified Mon Feb 10 16:57:49 MSK 2020 by zakharov
\* Created Fri Feb 07 12:23:21 MSK 2020 by zakharov
