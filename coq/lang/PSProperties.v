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

Definition relatively_complete :=
  forall (s : stmt),
  valid_stmt s ->
  exists (rg : rule_graph ps),
  derives rg s /\ rules_in_graph_sound rg.


Definition relatively_complete_acyclic :=
  forall (s : stmt),
  valid_stmt s ->
  exists (rg : rule_graph ps),
  derives rg s /\ rules_in_graph_sound rg /\ 
  ~ cyclic rg.

Definition theorem := derivable.
Definition acyc_theorem := acyc_derivable.

Lemma acyc_thm_is_theorem :
  acyc_theorem ⊆ theorem.
Proof.
  introv [rg [_ H1]]. exists~ rg.
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

Lemma thm_extend_mono :
  theorem ps ⊆ theorem (extend_ps ps r valid_r).
Proof.
  introv [rg H1].
  unfold theorem.
  unfold derivable.
  exists (extend_rg r valid_r rg).
  now apply extend_derives.
Qed.

Lemma acyc_thm_extend_mono :
  acyc_theorem ps ⊆ acyc_theorem (extend_ps ps r valid_r).
Proof.
  introv [rg [H1 H2]].
  exists (extend_rg r valid_r rg).
  split~; now apply extend_derives.
Qed.

Definition admits := 
  theorem (extend_ps ps r valid_r) ⊆ theorem ps.

Definition acyc_admits := 
  acyc_theorem (extend_ps ps r valid_r) ⊆ acyc_theorem ps.

Lemma admits_characteristic :
  (forall (prems : list stmt) (conc : stmt),
    valid_rule (extend_ps ps r valid_r) (inr (arbitrary r_inhab)) prems conc ->
      List.Forall (derivable ps) prems ->
      (derivable ps) conc)
  <-> admits.
Proof.
  split. {
    intros.
    unfold admits.
    introv [rg [H1 H2]].
    unfold theorem.
    (* Print extend_ps. *)
    exists* H2.
    specializes H (List.map rg.(rg_conc) (rg.(rg_prems) nd)) x.
    apply H.
    + simpls.
      remember (extend_ps ps r valid_r) as ext.
      pose (ext.(valid_rule)).
      subst.
      unfolds extend_ps. simpls.
      specializes P (inr (arbitrary r_inhab)).
      unfolds 
    unfolds extend_ps. simpls.
    specializes H (List.map rg.(rg_conc) (rg.(rg_prems) nd)) x.
    apply H.
    + pose proof (H3 : ps.(valid_rule)). destruct rg. simpls.
    
    
     destruct arbitrary. unfold r_inhab.
    unfold derivable.
    unfold derives.
    destruct rg. simpls.
    auto.
  }
Qed.


(* Lemma admits_characteristic : locally_sound (derivable ps) ->  *)