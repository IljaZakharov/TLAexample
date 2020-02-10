--------------------------------- MODULE LZ ---------------------------------
EXTENDS Integers, TLC

CONSTANTS Processes, \* The numbver of processes (threads actually) that can communicate. *\ 
          Signals,    \* The set of names of signal that can be sent by any thread. *\
          WorkingSet \* Values that can be assigned at any working step *\


(***       this is a comment containing the PlusCal code ***

--algorithm LZ {

variables Locks = [p \in Signals |-> 0], 
          ProcValues = [p \in Processes |-> 0],
          ProcStates = [p \in Processes |-> "working"],
          SigStates = [s \in Signals |-> "idle"],
          SigStorage = [s \in Signals |-> 0];


process(p \in Processes) 
    variables sig \in Signals;
{

    \* Choose working step, flag then receive or send.
    i1: either 
           goto w1;
        or
           goto c1;
        
    \* Do some work
    w1: with (i \in WorkingSet) { 
            ProcValues[self] := i;
        };
        goto i1;
    
    \* Choose a signal before doing anything. 
    c1: sig := RandomElement(Signals);
        goto c2;
    
    \* We can either receive or send a signal.
    c2: either 
            goto f1;
        or 
            goto s1;
        
    \* Lock
    f1: await Locks[sig] = 0;
        Locks[sig] := 1;            
        goto f2;
    
    \* Change state from "idle" to "waiting" or abort.
    f2: if (SigStates[sig] = "idle") {
            SigStates[sig] := "waiting";
            ProcStates[self] := "ready";
            goto f3;
        }
        else {
            \* Here we stop because the algorithm is intended for a model checker and
            \* not for a normal execution. This is the semantics of the "assume" statement.
            await FALSE;
        };
    
    \* Change the process state.   
    f3: goto f4;     
    
    \* Release the lock and then go to receiving.
    f4: Locks[sig] := 0;
        goto r1;
     
    \* Wait until the lock is released.
    r1: await Locks[sig] = 0;
        Locks[sig] := 1;            
        goto r2;
    
    \* Change the signal state or hang forever (the assume statement).
    r2: if (SigStates[sig] = "set") {
            ProcValues[self] := SigStorage[sig];
            SigStates[sig] := "idle";
            ProcStates[self] := "working";
            goto r3;
        }
        else {
            \* Here we stop because the algorithm is intended for a model checker and
            \* not for a normal execution. This is the semantics of the "assume" statement.
            await FALSE;
        };
    
    \* Change back the signal state.    
    r3: goto r4;
    
    \* Change back the process state.
    r4: goto r5;
    
    \* Release the signal lock and return to the initial state.
    r5: Locks[sig] := 0;
        goto i1;
    
    \* Wait until the lock is released.
    s1: await Locks[sig] = 0;
        Locks[sig] := 1;            
        goto s2;
        
    \* Change the signal state or hang forever (the assume statement).
    s2: if (SigStates[sig] = "waiting") {
            SigStorage[sig] := ProcValues[self];
            SigStates[sig] := "set";
            ProcStates[self] := "working";
            goto s3;
        }
        else {
            \* Here we stop because the algorithm is intended for a model checker and
            \* not for a normal execution. This is the semantics of the "assume" statement.
            await FALSE;
        }; 
    
    \* Change the signal state
    s3: goto s4;
    
    \* Change the process state.
    s4: goto s5;
        
    \* Release the signal lock and return to the initial state.
    s5: Locks[sig] := 0;
        goto i1;  
}        
               
    
}
****     this ends the comment containg the pluscal code      **********)
\* BEGIN TRANSLATION
VARIABLES Locks, ProcValues, ProcStates, SigStates, SigStorage, pc, sig

vars == << Locks, ProcValues, ProcStates, SigStates, SigStorage, pc, sig >>

ProcSet == (Processes)

Init == (* Global variables *)
        /\ Locks = [p \in Signals |-> 0]
        /\ ProcValues = [p \in Processes |-> 0]
        /\ ProcStates = [p \in Processes |-> "working"]
        /\ SigStates = [s \in Signals |-> "idle"]
        /\ SigStorage = [s \in Signals |-> 0]
        (* Process p *)
        /\ sig \in [Processes -> Signals]
        /\ pc = [self \in ProcSet |-> "i1"]

i1(self) == /\ pc[self] = "i1"
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "w1"]
               \/ /\ pc' = [pc EXCEPT ![self] = "c1"]
            /\ UNCHANGED << Locks, ProcValues, ProcStates, SigStates, 
                            SigStorage, sig >>

w1(self) == /\ pc[self] = "w1"
            /\ \E i \in WorkingSet:
                 ProcValues' = [ProcValues EXCEPT ![self] = i]
            /\ pc' = [pc EXCEPT ![self] = "i1"]
            /\ UNCHANGED << Locks, ProcStates, SigStates, SigStorage, sig >>

c1(self) == /\ pc[self] = "c1"
            /\ sig' = [sig EXCEPT ![self] = RandomElement(Signals)]
            /\ pc' = [pc EXCEPT ![self] = "c2"]
            /\ UNCHANGED << Locks, ProcValues, ProcStates, SigStates, 
                            SigStorage >>

c2(self) == /\ pc[self] = "c2"
            /\ \/ /\ pc' = [pc EXCEPT ![self] = "f1"]
               \/ /\ pc' = [pc EXCEPT ![self] = "s1"]
            /\ UNCHANGED << Locks, ProcValues, ProcStates, SigStates, 
                            SigStorage, sig >>

f1(self) == /\ pc[self] = "f1"
            /\ Locks[sig[self]] = 0
            /\ Locks' = [Locks EXCEPT ![sig[self]] = 1]
            /\ pc' = [pc EXCEPT ![self] = "f2"]
            /\ UNCHANGED << ProcValues, ProcStates, SigStates, SigStorage, sig >>

f2(self) == /\ pc[self] = "f2"
            /\ IF SigStates[sig[self]] = "idle"
                  THEN /\ SigStates' = [SigStates EXCEPT ![sig[self]] = "waiting"]
                       /\ ProcStates' = [ProcStates EXCEPT ![self] = "ready"]
                       /\ pc' = [pc EXCEPT ![self] = "f3"]
                  ELSE /\ FALSE
                       /\ pc' = [pc EXCEPT ![self] = "f3"]
                       /\ UNCHANGED << ProcStates, SigStates >>
            /\ UNCHANGED << Locks, ProcValues, SigStorage, sig >>

f3(self) == /\ pc[self] = "f3"
            /\ pc' = [pc EXCEPT ![self] = "f4"]
            /\ UNCHANGED << Locks, ProcValues, ProcStates, SigStates, 
                            SigStorage, sig >>

f4(self) == /\ pc[self] = "f4"
            /\ Locks' = [Locks EXCEPT ![sig[self]] = 0]
            /\ pc' = [pc EXCEPT ![self] = "r1"]
            /\ UNCHANGED << ProcValues, ProcStates, SigStates, SigStorage, sig >>

r1(self) == /\ pc[self] = "r1"
            /\ Locks[sig[self]] = 0
            /\ Locks' = [Locks EXCEPT ![sig[self]] = 1]
            /\ pc' = [pc EXCEPT ![self] = "r2"]
            /\ UNCHANGED << ProcValues, ProcStates, SigStates, SigStorage, sig >>

r2(self) == /\ pc[self] = "r2"
            /\ IF SigStates[sig[self]] = "set"
                  THEN /\ ProcValues' = [ProcValues EXCEPT ![self] = SigStorage[sig[self]]]
                       /\ SigStates' = [SigStates EXCEPT ![sig[self]] = "idle"]
                       /\ ProcStates' = [ProcStates EXCEPT ![self] = "working"]
                       /\ pc' = [pc EXCEPT ![self] = "r3"]
                  ELSE /\ FALSE
                       /\ pc' = [pc EXCEPT ![self] = "r3"]
                       /\ UNCHANGED << ProcValues, ProcStates, SigStates >>
            /\ UNCHANGED << Locks, SigStorage, sig >>

r3(self) == /\ pc[self] = "r3"
            /\ pc' = [pc EXCEPT ![self] = "r4"]
            /\ UNCHANGED << Locks, ProcValues, ProcStates, SigStates, 
                            SigStorage, sig >>

r4(self) == /\ pc[self] = "r4"
            /\ pc' = [pc EXCEPT ![self] = "r5"]
            /\ UNCHANGED << Locks, ProcValues, ProcStates, SigStates, 
                            SigStorage, sig >>

r5(self) == /\ pc[self] = "r5"
            /\ Locks' = [Locks EXCEPT ![sig[self]] = 0]
            /\ pc' = [pc EXCEPT ![self] = "i1"]
            /\ UNCHANGED << ProcValues, ProcStates, SigStates, SigStorage, sig >>

s1(self) == /\ pc[self] = "s1"
            /\ Locks[sig[self]] = 0
            /\ Locks' = [Locks EXCEPT ![sig[self]] = 1]
            /\ pc' = [pc EXCEPT ![self] = "s2"]
            /\ UNCHANGED << ProcValues, ProcStates, SigStates, SigStorage, sig >>

s2(self) == /\ pc[self] = "s2"
            /\ IF SigStates[sig[self]] = "waiting"
                  THEN /\ SigStorage' = [SigStorage EXCEPT ![sig[self]] = ProcValues[self]]
                       /\ SigStates' = [SigStates EXCEPT ![sig[self]] = "set"]
                       /\ ProcStates' = [ProcStates EXCEPT ![self] = "working"]
                       /\ pc' = [pc EXCEPT ![self] = "s3"]
                  ELSE /\ FALSE
                       /\ pc' = [pc EXCEPT ![self] = "s3"]
                       /\ UNCHANGED << ProcStates, SigStates, SigStorage >>
            /\ UNCHANGED << Locks, ProcValues, sig >>

s3(self) == /\ pc[self] = "s3"
            /\ pc' = [pc EXCEPT ![self] = "s4"]
            /\ UNCHANGED << Locks, ProcValues, ProcStates, SigStates, 
                            SigStorage, sig >>

s4(self) == /\ pc[self] = "s4"
            /\ pc' = [pc EXCEPT ![self] = "s5"]
            /\ UNCHANGED << Locks, ProcValues, ProcStates, SigStates, 
                            SigStorage, sig >>

s5(self) == /\ pc[self] = "s5"
            /\ Locks' = [Locks EXCEPT ![sig[self]] = 0]
            /\ pc' = [pc EXCEPT ![self] = "i1"]
            /\ UNCHANGED << ProcValues, ProcStates, SigStates, SigStorage, sig >>

p(self) == i1(self) \/ w1(self) \/ c1(self) \/ c2(self) \/ f1(self)
              \/ f2(self) \/ f3(self) \/ f4(self) \/ r1(self) \/ r2(self)
              \/ r3(self) \/ r4(self) \/ r5(self) \/ s1(self) \/ s2(self)
              \/ s3(self) \/ s4(self) \/ s5(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Processes: p(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

EXT == INSTANCE ELZ

(* This is main result *)
THEOREM Spec => EXT!Spec

(* Additional checks of correctness *)

(* Two or more processes cannot be in a signal critical section at once *)
LockSafe == [] ~ \E p1 \in ProcSet, p2 \in ProcSet: /\ p1 # p2
                                                    /\ sig[p1] = sig[p2]      
                                                    /\ pc[p1] = pc[p2]
                                                    /\ pc[p1] \in {"f2" , "r2", "s2"} 
(* TODO: random value *)

=============================================================================
\* Modification History
\* Last modified Mon Feb 10 15:21:37 MSK 2020 by zakharov
\* Created Fri Feb 07 18:50:53 MSK 2020 by zakharov
