Set Implicit Arguments.
From Lang Require Import Util RuleGraphs.

Module PSProperties(PS : ProofSystem).
Include PS.
Module Import RG := RuleGraph(PS). 

Definition derivable s :=
  exists rg, derives rg s.

Definition acyc_derivable s :=
  exists rg, ~ cyclic rg /\ derives rg s.

(* A statement is valid if 
   a graph exists where 
   1. all lifted statements in the graph are valid
   2. all rules used in the graph are locally sound
   3. the statement exists somewhere in the graph
*)
Theorem sound_from_acyclic_graph :
  forall (s:stmt),
  (exists rg, 
    derives rg s /\ 
    ~ cyclic rg /\
    rules_in_graph_sound rg
  ) ->
  valid_stmt s.
Proof.
  intros. exists* H.
  destruct H. destruct H2.
  rewrite <- H2.
  apply~ acyclic_soundness.
Qed.

Definition relatively_complete :=
  forall (s : stmt),
  valid_stmt s ->
  exists rg,
  derives rg s /\ rules_in_graph_sound rg.


Definition relatively_complete_acyclic :=
  forall (s : stmt),
  valid_stmt s ->
  exists rg,
  derives rg s /\ rules_in_graph_sound rg /\ 
  ~ cyclic rg.

Definition theorem := derivable.
Definition acyc_theorem := acyc_derivable.

Lemma acyc_thm_is_theorem :
  acyc_theorem ⊆ theorem.
Proof.
  introv [rg [_ H1]]. exists~ rg.
Qed.

Module PSExtend <: ProofSystem.
  Parameter r : Type.
  Parameter valid_r : list stmt -> stmt -> Prop.

  Definition stmt := PS.stmt.
  Definition liftable := PS.liftable.
  Definition valid_stmt := PS.valid_stmt.

  Open Scope type_scope.
  Definition rule := PS.rule + r.

  Definition valid_rule (rl : rule) (pre : list stmt) (c : stmt) : Prop :=
    match rl with 
    | inl rl => PS.valid_rule rl pre c 
    | inr rl => valid_r pre c
    end.
  
End PSExtend.

End PSProperties.

Module MorePSProperties(PS : ProofSystem).
Include PS.
Module Import RG := RuleGraph(PS). 
Module Import PSP := PSProperties(PS).
(* Parameter  *)


(* Lemma thm_extend_mono (PS : ProofSystem) (r : Type) (valid_r : list PS.stmt -> PS.stmt -> Prop) 
  : True.
   *)
