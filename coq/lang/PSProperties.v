Set Implicit Arguments.
From Lang Require Import Util RuleGraphs.

Section PSProperties.
Variable univ : universe.
Variable ps : proof_system univ.

Notation stmt := univ.(stmt).
Notation valid_stmt := univ.(valid_stmt).

Implicit Type s : stmt.
Implicit Type rg : rule_graph ps.

Definition derivable s :=
  exists (rg : rule_graph ps), derives rg s.

Definition acyc_derivable s :=
  exists (rg : rule_graph ps), ~ cyclic rg /\ derives rg s.

(* A statement is valid if 
   a graph exists where 
   1. all lifted statements in the graph are valid
   2. all rules used in the graph are locally sound
   3. the statement exists somewhere in the graph
*)
Theorem sound_from_acyclic_graph :
  forall (s:stmt),
  (exists (rg : rule_graph ps),
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


Definition theorem := derivable.
Definition acyc_theorem := acyc_derivable.

Lemma acyc_thm_is_theorem :
  acyc_theorem ⊆ theorem.
Proof.
  introv [rg [_ H1]]. exists~ rg.
Qed.

Definition relatively_complete :=
  valid_stmt ⊆ theorem.

Definition acyc_relatively_complete :=
  valid_stmt ⊆ acyc_theorem.

Lemma rel_comp_weak :
  acyc_relatively_complete -> relatively_complete.
Proof.
  introv ??. specializes H H0.
  apply~ acyc_thm_is_theorem.
Qed.

Section ExtendPSProperties.
Variable r : Type.
Variable r_inhab : Inhab r.
Variable valid_r : list stmt -> stmt -> Prop.

Definition extend_ps : proof_system univ :=
  let liftable := ps.(liftable) in
  let rule := (ps.(rule) + r)%type in
  let valid_rule (rl : rule) (pre : list stmt) (c : stmt) := match rl with 
    | inl rl => ps.(valid_rule) rl pre c 
    | inr rl => valid_r pre c
    end
  in
  @mk_ps univ liftable rule valid_rule.

Definition extend_rg (rg : rule_graph ps) : rule_graph extend_ps.
Proof.
  pose (erg_rule := fun nd => match rg.(rg_rule) nd with
    | Lift _ => Lift extend_ps
    | Rule _ r => Rule extend_ps (inl r)
  end).
  assert (forall nd : rg.(rg_node), 
    match erg_rule nd with
    | Rule _ r => extend_ps.(valid_rule) r (List.map rg.(rg_conc) (rg.(rg_prems) nd)) (rg.(rg_conc) nd)
    | Lift _ => extend_ps.(liftable) (rg.(rg_conc) nd) /\ (rg.(rg_prems) nd) = nil
    end).
  2 : refine (@mk_rg univ extend_ps rg.(rg_nodes) rg.(rg_conc) erg_rule rg.(rg_prems) H).
  subst erg_rule. simpls. intros.
  pose proof (H2 := rg_wf nd).
  destruct (rg_rule nd) eqn:H; auto.
Defined.

Lemma extend_lift_validity (rg : rule_graph ps) :
  graph_lift_valid rg ->
  graph_lift_valid (extend_rg rg).
Proof.
  introv H1. 
  intro.
  specializes H1 nd.
  destruct (rg_rule nd) eqn:H2; auto.
  destruct (@rg_rule univ ps rg nd) eqn:H3; auto.
  unfolds extend_ps. simpls.
  rewrite H3 in H2. discriminate.
Qed.

Lemma extend_derives (rg : rule_graph ps) (s : stmt) :
  derives rg s ->
  derives (extend_rg rg) s.
Proof.
  introv [H1 H2].
  split~. now apply extend_lift_validity.
Qed.

End ExtendPSProperties.

End PSProperties.

Section MorePSProperties.
Variable univ : universe.
Variable ps : proof_system univ.

Notation stmt := univ.(stmt).
Notation valid_stmt := univ.(valid_stmt).

Implicit Type s : stmt.
Implicit Type rg : rule_graph ps.

Variable r : Type.
Variable r_inhab : Inhab r.
Variable valid_r : list stmt -> stmt -> Prop.

Notation extend_ps := (extend_ps ps r valid_r).

Lemma thm_extend_mono :
  theorem ps ⊆ theorem extend_ps.
Proof.
  introv [rg H1].
  unfold theorem.
  unfold derivable.
  exists (extend_rg r valid_r rg).
  now apply extend_derives.
Qed.

Lemma acyc_thm_extend_mono :
  acyc_theorem ps ⊆ acyc_theorem extend_ps.
Proof.
  introv [rg [H1 H2]].
  exists (extend_rg r valid_r rg).
  split~; now apply extend_derives.
Qed.

Definition admits := 
  theorem extend_ps ⊆ theorem ps.

Definition acyc_admits := 
  acyc_theorem extend_ps ⊆ acyc_theorem ps.


Lemma admits_derives s :
  derivable extend_ps s ->
  admits ->
  derivable ps s.
Proof.
  intros. apply H0, H.
Qed.

Lemma acyc_admits_admits :
  acyc_admits -> admits.
Proof.
  intro. unfolds acyc_admits, admits, acyc_theorem, theorem, acyc_derivable, derivable.
  introv (?&?).
Abort.

Lemma admits_rel_comp :
  relatively_complete extend_ps -> 
  admits ->
  relatively_complete ps.
Proof.
  introv ???. specializes H H1.
  specializes H0 x. auto.
Qed.