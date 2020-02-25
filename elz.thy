(*  Title:      elz.thy
    Author:     Ilja Zakharov, ISPRAS
*)

theory elz
  imports "HOL-TLA.TLA"
begin

section \<open>Common preliminaries.\<close>

declare [[show_types]]
declare [[show_consts]]

(* Process status type *)
datatype ProcState = WORKING | READY

(* Signal status type *)
datatype SigState = IDLE | WAITING | SET

(* This is very helpful function to work with functions implementing dictionaries/maps *)
definition Updated :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> 'b trfun \<Rightarrow> action" where
  "Updated f x v \<equiv> ACT (\<forall>n. id<f$,#n> = (if #n = #x then v else id<$f,#n>))"

(* This function just choses an element from the given set *)
definition Random :: "'b set \<Rightarrow> 'b" where
"Random xs \<equiv> (SOME x. x \<in> xs)"

axiomatization 
  (* The number of processes and signals in the model *)
  ProcCount :: nat and 
  SigCount :: nat and

  (* Untyped sets of processes and signals *)
  Processes :: "'a set" and
  Signals :: "'b set" and
  (* Set of values that can be passed between processes *)
  WorkingSet :: "int set"
where
  (* There are at least one process *)
  NodeCount_positive: "ProcCount > 0" and
  (* Size of processes and signals sets are restricted by given constants *)
  ProcessesCount: "card Processes = ProcCount" and
  SignalsCount: "card Signals = ProcCount"

section \<open>Abstract Model - ELZ\<close>

subsection \<open>Definition of ELZ\<close>

txt \<open>Now we can describe the abstract model. We do that as a separate locale for the further
     refinement step. There are five base variables in the model as in corresponding TLA
     specification. Note, that the model can step into a deadlock situation. \<close>

locale ELZ =
  (* Maps that describe statuses and values that correspond to processes and signals *)
  fixes ProcStates :: "('a \<Rightarrow> ProcState) stfun"
  fixes SigStates :: "('a \<Rightarrow> SigState) stfun"
  fixes ProcValues :: "('a \<Rightarrow> int) stfun"
  fixes SigStorage :: "('a \<Rightarrow> int) stfun"
  
  (* The map describe which signal is under the processing by each process*)
  fixes ProcSignals :: "('a \<Rightarrow> 'a) stfun"
  
    (* Variables of the abstract model *)
  assumes bv: "basevars (ProcStates, SigStates, ProcValues, SigStorage, ProcSignals)"
  
  (* Initial state of the model *)
  fixes ELZInit ELZProcInit ELZSigInit
    (* Note that here we cannot change type, so conditions are different *)
    defines "ELZProcInit \<equiv> PRED \<forall> x. (id<ProcStates, #x> = #WORKING) 
                                   \<and> (id<ProcValues, #x> = #0)
                                   \<and> (id<ProcSignals, #x> \<notin> #Signals)"
    defines "ELZSigInit \<equiv> PRED \<forall> x. (id<SigStates, #x> = #IDLE) 
                                  \<and> (id<SigStorage, #x> = #0)"
    (* Finally this is the initial state *)
    defines "ELZInit \<equiv> PRED (ELZProcInit \<and> ELZSigInit)"
  
  fixes Working :: "'a \<Rightarrow> action"  
    (* This is action that \E i \in WorkingSet:  ProcValues' = [ProcValues EXCEPT![p] = i] *)
    defines "Working p \<equiv> ACT (id<$ProcStates, #p> = #WORKING)
                           \<and> (Updated ProcValues p (const (Random WorkingSet)))
                           \<and> unchanged (ProcStates, SigStates, SigStorage, ProcSignals)"

  fixes Flag :: "'a \<Rightarrow> 'a \<Rightarrow> action"
    (* Function that set a new state after Flag action performed by p process for s signal *)
    defines "Flag p s \<equiv> ACT (id<$ProcStates, #p> = #WORKING)
                          \<and> (id<$SigStates, #s> = #IDLE)
                          \<and> (Updated ProcStates p (const READY))
                          \<and> (Updated SigStates s (const WAITING))
                          \<and> unchanged (ProcValues, SigStorage, ProcSignals)"
  
  fixes Receive :: "'a \<Rightarrow> 'a \<Rightarrow> action"
    (* Describes the final step: receiving values *)
    defines "Receive p s \<equiv> ACT (id<$ProcStates, #p> = #READY)
                             \<and> (id<$SigStates, #s> = #SET)
                             \<and> (id<$ProcSignals, #p> = #s)
                             \<and> (Updated ProcStates p (const WORKING))
                             \<and> (Updated ProcValues p (ACT id<$SigStorage, #s>))
                             \<and> (Updated SigStates s (const IDLE))
                             \<and> unchanged (SigStorage, ProcSignals)"

  fixes Send :: "'a \<Rightarrow> 'a \<Rightarrow> action"
    (* Describes function Send that saves values to the signal storage *)
    defines "Send p s \<equiv> ACT (id<$ProcStates, #p> = #WORKING)
                          \<and> (id<$SigStates, #s> = #WAITING)
                          \<and> (Updated SigStates s (const SET))
                          \<and> (Updated SigStorage s (ACT id<$ProcValues, #p>))
                          \<and> unchanged (ProcStates, ProcValues, ProcSignals)"

  fixes ChangeSignal :: "'a \<Rightarrow> action"
    (* Describes non-deterministic signal switch*)
    defines "ChangeSignal p \<equiv> ACT (id<$ProcStates, #p> = #WORKING) 
                                \<and> (Updated ProcSignals p (const (Random Signals)))
                                \<and> unchanged (SigStates, ProcStates, ProcValues, SigStorage)"

  fixes SignalAction :: "'a \<Rightarrow> 'a \<Rightarrow> action"
    (* Group signal-related actions *)
    defines "SignalAction p s \<equiv> ACT ((Flag p s) \<or> (Send p s) \<or> (Receive p s))"

  fixes BasicAction :: "'a \<Rightarrow> action"
    (* Group process-related actions *)  
    defines "BasicAction p \<equiv> ACT ((Working p) 
                                   \<or> (ChangeSignal p)
                                   \<or> (SignalAction p (Random Signals)))"
  fixes Next :: "action"
    (* This formula describes step transition *)
    defines "Next \<equiv> BasicAction (Random Processes)"

  fixes Spec :: "temporal"
    (* Describes behavior of the model *)
    defines "Spec \<equiv> TEMP Init ELZInit \<and> \<box>[Next]_(ProcStates, SigStates, ProcValues, SigStorage, ProcSignals)"

subsection \<open>Properties of ELZ\<close>

txt \<open>Before we proceed to the refinement lets check PropPending formula from the TLA specification.\<close>

context ELZ
begin

theorem PropPending1: 
  "\<turnstile> (Spec \<longrightarrow> \<box>((\<exists> p. id<ProcStates, #p> = #READY) \<longrightarrow> (\<exists> s. id<SigStates, #s> = #IDLE)))"
  oops

theorem PropPending2: 
  "\<turnstile> (Spec \<longrightarrow> \<box>((\<exists> s. id<SigStates, #s> = #IDLE) \<longrightarrow> (\<exists> p. id<ProcStates, #p> = #READY)))"
  oops
end

end                                                                                   