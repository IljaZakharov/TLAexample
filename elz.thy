(*  Title:      elz.thy
    Author:     Ilja Zakharov, ISPRAS
*)

section \<open>ELZ description in Isabelle/TLA.\<close>

theory elz
  imports "HOL-TLA.TLA"
begin

declare [[show_types]]
declare [[show_consts]]

(* Process status type *)
datatype ProcState = WORKING | READY

(* Signal status type *)
datatype SigState = IDLE | WAITING | SET

(* This is very helpful function to work with functions implementing dictionaries/maps *)
definition Updated :: "('a \<Rightarrow> 'b) stfun \<Rightarrow> 'a \<Rightarrow> 'b trfun \<Rightarrow> action" where
  "Updated f x v \<equiv> ACT (\<forall>n. id<f$,#n> = (if #n = #x then v else id<$f,#n>))"

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

locale ELZ =
  (* Maps that describe statuses and values that correspond to processes and signals *)
  fixes ProcStates :: "('a \<Rightarrow> ProcState) stfun"
  fixes SigStates :: "('a \<Rightarrow> SigState) stfun"
  fixes ProcValues :: "('a \<Rightarrow> int) stfun"
  fixes SigStorage :: "('a \<Rightarrow> int) stfun"

  (* The map describe which signal is under the processing by each process*)
  fixes ProcSignals :: "('a \<Rightarrow> 'b) stfun"

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

  fixes NextWorking
  defines "NextWorking \<equiv> ACT (\<exists> x. Updated ProcValues x 1::int)"
  
value "y = (SOME x. x \<in> {1::nat, 2 ,3})"

(* Now describe the abstract model *)
(* locale ELZ =
  fi
*)
end                                                                                   