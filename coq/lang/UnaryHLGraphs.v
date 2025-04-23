Set Implicit Arguments. 
From Lang Require Export Assertions.
From Lang Require Import RuleGraphs PSProperties Nodes.

(*Implicit Type m : mem.
Implicit Type n : int.
Implicit Type I : binding.
Implicit Type c : cmd.*)

Section PS.

  Variant _stmt := 
    | StmtTriple (c:cmd) (P Q : assrt)
    | StmtAssrt (P:assrt).
  
  Definition liftable (s : _stmt) : Prop :=
    match s with 
    | StmtAssrt _ => True
    | _ => False
    end.

  Definition valid_stmt (s : _stmt) : Prop :=
    match s with 
    | StmtAssrt P => valid_assrt P
    | StmtTriple c P Q => valid_triple c P Q
    end.

  Definition univ := @mk_univ _stmt valid_stmt.

  Notation "'|-' c ':' P '=>' Q" := 
    (StmtTriple c P%A Q%A)
    (at level 50, c at next level, no associativity).

  Notation "'|-' P" :=
    (StmtAssrt P%A)
    (at level 50, no associativity).

  Variant rule :=
    | HL_CSQ
    | HL_Skip
    | HL_Assn
    | HL_Seq
    | HL_If
    | HL_WhileTrue
    | HL_WhileFalse.

  Variant valid_rule : rule -> list _stmt -> _stmt -> Prop :=
    | Valid_HL_CSQ c P P' Q Q' : 
      valid_rule HL_CSQ [(|- (P->P')); (|- c : P' => Q'); (|- (Q'->Q))] (|- c : P => Q)
    | Valid_HL_Skip P : 
      valid_rule HL_Skip [] (|- CSkip : P => P)
    | Valid_HL_Assn x a P : 
      valid_rule HL_Assn [] (|- CAssn x a : P[a/x] => P)
    | Valid_HL_Seq c1 c2 P Q R : 
      valid_rule HL_Seq [(|- c1 : P => Q); (|- c2 : Q => R)] (|- CSeq c1 c2 : P => R)
    | Valid_HL_If c P Q (b:bexp) c' : 
      valid_rule HL_If [(|- c : P /\ b => Q); (|- c' : P /\ ~b => Q)] (|- CIf b c c' : P => Q)
    | Valid_HL_WhileTrue c P Q (b:bexp) : 
      valid_rule HL_WhileTrue [(|- CSeq c (CWhile b c) : P /\ b => Q)] (|- CWhile b c : P /\ b => (Q /\ ~b))
    | Valid_HL_WhileFalse P b c : 
      valid_rule HL_WhileFalse [] (|- CWhile b c : P /\ ~b => (P /\ ~b)).

  Definition uhl := @mk_ps univ liftable rule valid_rule.

End PS.

Notation "'|-' c ':' P '=>' Q" := 
  (StmtTriple c P%A Q%A)
  (at level 50, c at next level, no associativity).

Notation "'|-' P" :=
  (StmtAssrt P%A)
  (at level 50, no associativity).

Section Soundness.

Open Scope valid_scope.

Lemma csq_sound c P Q P' Q' 
  (H1 : |= (P -> P'))
  (H2 : |= c : P' => Q') 
  (H3 : |= (Q' -> Q)) 
  : |= c : P => Q.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros.
  specializes H1 m I.
  simpls.
  specializes H1 H.
  specializes H2 H1.
  specializes H2 H0.
  apply H3.
  trivial.
Qed.

Lemma skip_sound P : |= CSkip : P => P.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros. unfolds yields.
  destruct H0.
  inverts~ H0.
  cstep_skip.
Qed.

Lemma assn_sound x a P : 
  |= CAssn x a : P[a/x] => P.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros. unfolds in H0.
  exists* H0. sort.
  inverts H0. inverts H1.
  inverts H'. 2: cstep_skip.
  assert (~ has_ivars (aeval m a)) as IV; auto.
  apply assrt_subst_equiv.
  simpls. now apply subst_val.
Qed.

Lemma seq_sound c c' P Q R :
  |= c : P => Q ->
  |= c' : Q => R ->
  |= CSeq c c' : P => R.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros.
  apply seq_intermediate_yields in H2.
  destruct H2 as (m'' & H2 & H3).
  specializes H m I.
Qed.

Lemma if_sound (b:bexp) c c' P Q :
  |= c : P /\ b => Q ->
  |= c' : P /\ ~b => Q ->
  |= CIf b c c' : P => Q.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros. simpls.
  unfolds in H2.
  exists* H2. sort.
  destruct (beval m b) eqn:E.
  - inverts H2. inverts H3. 2 : contradiction.
    applys H m'0. splits~. now rewrite bexp_assrt_equiv.
    exists~ n0.
  - inverts H2. inverts H3. now rewrite E in Hg.
    applys H0 m'0. splits~. now rewrite bexp_assrt_equiv.
    exists~ n0.
Qed.

Lemma yields_while_unroll b c m m' :
  yields (CWhile b c) m m' ->
  beval m b ->
  yields (CSeq c (CWhile b c)) m m'.
Proof.
  intros. destruct H. inverts H.
  inverts H1; [|contradiction].
  exists~ n.
Qed.

Lemma while_true_sound (b:bexp) c P Q :
  |= CSeq c (CWhile b c) : P /\ b => Q ->
  |= CWhile b c : P /\ b => (Q /\ ~ b).
Proof.
  introv H1 H2 H3. simpls.
  split.
  - apply yields_while_unroll in H3.
    applys H1 H2 H3. 
    rewrite <- bexp_assrt_equiv. apply H2.
  - rewrite bexp_assrt_equiv.
    inverts H3.
    now apply while_multistep_termination in H.
Qed.

Lemma while_false_sound (b:bexp) c P :
  |= CWhile b c : P /\ ~ b => (P /\ ~ b).
Proof.
  introv H1 H2.
  inverts H2.
  inverts H.
  inverts H0.
  2 : { inverts~ H'. cstep_skip. }
  apply sat_and in H1.
  destruct H1.
  simpls.
  contradict H0.
  apply bexp_assrt_equiv.
  trivial.
Qed.

Theorem uhl_sound :
  forall (rg : rule_graph uhl), rules_in_graph_sound rg.
Proof.
  intro.
  unfold rules_in_graph_sound.
  intros.
  destruct H.
  unfold ps_sound_rule, sound_rule.
  intros.
  destruct conc. 2 : inverts H0.
  unfold valid_stmt.
  Ltac prem_open :=
    repeat match goal with 
    | [ H:(List.Forall _ _) |- _ ] => inverts H
    end. 
  inverts H0; prem_open; unfolds valid_stmt.
  + applys csq_sound H3 H2 H4.
  + applys skip_sound.
  + applys assn_sound.
  + applys seq_sound H3 H2.
  + applys if_sound H3 H2.
  + applys while_true_sound H3.
  + applys while_false_sound.
Qed. 

End Soundness.


Section AcyclicIncompleteness.

Local Lemma infinite_loop_aux :
  forall n m c m',
  multistep (CWhile true CSkip) m c m' n ->
  c <> CSkip.
Proof.
  induction n using (well_founded_induction lt_wf).
  intros. destruct n.
  { inverts H0. discriminate. }
  inverts H0. inverts H6.
  2: { contradict Hg. auto. }
  inverts H'. discriminate.
  inverts H0. { inverts H6. }
  applys H H'0. math.
Qed.

Local Lemma infinite_loop_valid P Q :
  (|= (CWhile true CSkip) : P => Q)%V.
Proof.
  unfold valid_triple, triple, yields.
  intros. exists* H0. now apply infinite_loop_aux in H0.
Qed.


Section GraphFacts.

Variable rg : rule_graph uhl.
Variable lift_valid : graph_lift_valid rg.
Variable acyclic : ~ cyclic rg.

Definition form_1 P Q :=
  |- (CWhile true CSkip) : P => Q.

Definition form_2 P Q :=
  |- (CSeq CSkip (CWhile true CSkip)) : P => Q.

Implicit Type nd : rg_node rg.

Lemma form_1_rules nd P Q :
  rg_conc nd = form_1 P Q ->
  (|= P)%V ->
  rg_rule nd = Rule uhl HL_CSQ \/ 
  rg_rule nd = Rule uhl HL_WhileTrue.
Proof.
  intros Conc TautP.
  pose proof rg_wf nd.
  destruct (rg_rule nd) eqn:R.
  2: { 
    destruct H. unfolds in H. rewrite Conc in H.
    now unfolds form_1.
  }
  rewrite Conc in H. unfolds form_1.
  destruct~ r; inverts H.
  (* Show that HL_False cannot be applied *)
  apply valid_and in TautP as (?&?).
  unfolds in H1.
  specialize H1 with (fun _ => 0) (fun _ => 0).
  simpls. now contradict H1.
Qed.

Lemma form_2_rules nd P Q :
  rg_conc nd = form_2 P Q ->
  rg_rule nd = Rule uhl HL_CSQ \/ 
  rg_rule nd = Rule uhl HL_Seq.
Proof.
  intros Conc.
  pose proof rg_wf nd.
  destruct (rg_rule nd) eqn:R.
  2: { 
    destruct H. unfolds in H. now rewrite Conc in H.
  }
  rewrite Conc in H. unfolds form_2.
  destruct~ r; inverts H.
Qed.

Lemma strong_csq nd P Q c :
  rg_conc nd = |- c : P => Q ->
  rg_rule nd = Rule uhl HL_CSQ ->
  (|= P)%V ->
  exists nd' P' Q',
  (|= P')%V /\
  rg_conc nd' = (StmtTriple c P' Q' : univ.(stmt)) /\
  List.In nd' (rg_prems nd).
Proof.
  intros Conc Rule TautP.
  pose proof rg_wf nd. rewrite Rule in H.
  inverts H. rewrite Conc in H1.
  inverts H1. sort.
  (* Break down prems list into 3 items *)
  destruct (rg_prems nd). discriminate.
  simpls. destruct l. discriminate. simpls.
  destruct l. discriminate.
  simpls. destruct l. 2: discriminate.
  simpls. inverts H0.
  exists r0 P' Q'. splits~.
  specializes lift_valid r.
  rewrite <- H1 in lift_valid.
  destruct (rg_rule r) eqn:E.
  pose proof rg_wf r. rewrite E in H.
  rewrite <- H1 in H. inverts H.
  unfolds in lift_valid.
  introv. specializes TautP m I.
  specializes lift_valid m I.
Qed.

Lemma form_1_while nd P Q :
  rg_conc nd = form_1 P Q ->
  rg_rule nd = Rule uhl HL_WhileTrue ->
  (|= P)%V ->
  exists nd' P' Q',
  (|= P')%V /\
  rg_conc nd' = (form_2 P' Q' : univ.(stmt)) /\
  List.In nd' (rg_prems nd).
Proof.
  intros F Rule HP.
  pose proof rg_wf nd. rewrite Rule in H.
  inverts H. sort.
  destruct (rg_prems nd). discriminate.
  simpls. inverts H0.
  exists r (P0/\b)%A Q0.
  rewrite F in H1. inverts~ H1.
Qed.

Lemma form_2_seq nd P Q :
  rg_conc nd = form_2 P Q ->
  rg_rule nd = Rule uhl HL_Seq ->
  (|= P)%V ->
  exists nd' P' Q',
  (|= P')%V /\
  rg_conc nd' = (form_1 P' Q' : univ.(stmt)) /\
  List.In nd' (rg_prems nd).
Proof.
  intros F Rule HP.
  pose proof rg_wf nd. rewrite Rule in H.
  inverts H. sort.
  destruct (rg_prems nd). discriminate.
  simpls. inverts H0.
  destruct l; inverts H3. clear H4. sort.
  rewrite F in H1. inverts H1.
  rename Q0 into R.
  exists r0 R Q. splits~.
  2: { right. constructor~. }

  pose proof rg_wf r. rewrite <- H2 in H.
  pose proof acyclic_soundness acyclic lift_valid (@uhl_sound rg) r.
  rewrite <- H2 in H1. unfolds in H1.
  simpls. introv.
  specializes HP m I. specializes H1 HP m.
  apply H1. unfolds. exists O.
  constructor.
Qed.

Definition has_form nd P Q :=
  let conc := rg_conc nd in
  conc = form_1 P Q \/ 
  conc = form_2 P Q.

Lemma form_step nd P Q :
  has_form nd P Q ->
  (|= P)%V ->
  exists nd' P' Q',
  (|= P')%V /\
  has_form nd' P' Q' /\
  List.In nd' (rg_prems nd).
Proof.
  intros F HP. destruct F as [F|F].
  - pose proof form_1_rules _ F HP.
    destruct H.
    + pose proof strong_csq nd F H HP. exists* H0.
      exists nd' P' Q'. splits~. unfolds. left~.
    + pose proof form_1_while nd F H HP. exists* H0.
      exists nd' P' Q'. splits~. right~.
  - pose proof form_2_rules _ F.
    destruct H.
    + pose proof strong_csq nd F H HP. exists* H0.
      exists nd' P' Q'. splits~. unfolds. right~.
    + pose proof form_2_seq nd F H HP. exists* H0.
      exists nd' P' Q'. splits~. left~.
Qed.
  

Lemma path_grow nd P Q :
  has_form nd P Q ->
  (|= P)%V ->
  forall n,
  exists nd' P' Q', exists (p:path rg),
  has_form nd' P' Q' /\
  (|= P')%V /\
  first (proj1_sig p) = Some nd /\
  last (proj1_sig p) = Some nd' /\
  length (proj1_sig p) = S n.
Proof.
  intros F HP.
  induction n.
  { intros. now exists nd P Q (single_path nd). }
  destruct IHn as (nd'&P'&Q'&p&F'&HP'&Fst&Lst&L). sort.
  pose proof form_step F' HP' as (nd''&P''&Q''&HP''&F''&In).
  sort.
  exists nd'' P'' Q''.
  assert (Path : is_path (nd'::nd''::[])) by easy.
  pose proof path_appending p (exist _ _ Path) Lst as Path'.
  simpls. exists (exist _ _ Path').
  simpls. splits~.
  - rewrite~ first_append. intro. rewrite H in *. discriminate.
  - rewrite~ last_append. easy.
  - rewrite length_app. rewrite length_cons, length_nil, L. math.
Qed.

End GraphFacts.

Theorem unary_HL_acyclic_incomplete :
  ~ acyc_relatively_complete uhl.
Proof.
  unfolds acyc_relatively_complete.
  intro. specializes H (|- (CWhile true CSkip) : true => false).
  specializes H infinite_loop_valid.
  destruct H as (rg&Acyc&(Lft&nd&Conc)).
  pose proof @path_grow _ Lft Acyc nd true false.
  contradict Acyc. apply cyclic_cardinal.
  specializes H (NodeSet.cardinal (rg_nodes rg)); try easy.
  { unfolds. left. now rewrite Conc. }
  destruct H as (_&_&_&p&_&_&_&_&L).
  exists p. math.
Qed.

End AcyclicIncompleteness.

Section CyclicTraceRules.

Open Scope valid_scope.

Definition invalid_triple c P Q n :=
  exists m I, 
    (m+I |= P)%V /\ 
    exists m' n',
      multistep c m CSkip m' n' /\ 
      ~ (m'+I |= Q)%V /\
      n' < n.

Lemma while_true_trace_rule b c P Q n :
  invalid_triple (CWhile b c) (P /\ b)%A (Q /\ ~b)%A (S n) ->
  invalid_triple (CSeq c (CWhile b c)) (P /\ b)%A (Q)%A n.
Proof.
  intro.
  unfold invalid_triple in *.
  exists* H.
  apply while_multistep_termination in H0 as H4.
  inverts H0.
  sort.
  inverts H3.
  2 : {
    simpls.
    contradict Hg.
    destruct H.
    applys bexp_assrt_equiv.
    applys H0.
  }
  exists m'0 I.
  splits~.
  exists m' n0.
  splits~.
  2 : math.
  contra H1.
  simpls.
  splits~.
  contra H4.
  now apply bexp_assrt_equiv in H4.
Qed.

Lemma if_trace_rule b c c' P Q n :
  invalid_triple (CIf b c c') P Q (S n) ->
  invalid_triple c (P /\ b)%A Q n \/ invalid_triple c' (P /\ ~b)%A Q n.
Proof.
  intro.
  unfold invalid_triple in H.
  exists* H.
  inverts H0.
  inverts H3.
  - left.
    unfold invalid_triple.
    exists m'0 I.
    split.
    simpls.
    splits~.
    now rewrite bexp_assrt_equiv.
    exists m' n0.
    splits~. 
    math. 
  - right.
    unfold invalid_triple.
    exists m'0 I.
    split.
    simpls.
    splits~.
    now rewrite bexp_assrt_equiv.
    exists m' n0.
    splits~. 
    math.
Qed.

Lemma seq_trace_rule c c' P Q R n :
  invalid_triple (CSeq c c') P R (S n) ->
    invalid_triple c P Q n \/ invalid_triple c' Q R n.
Proof.
  intro.
  unfold invalid_triple in H.
  exists* H.
  apply seq_intermediate_multistep in H0.
  exists* H0.
  either (m'0 + I |= Q)%V.
  - right.
    unfold invalid_triple.
    exists m'0 I.
    splits~.
    exists m' n2.
    splits~.
    math.
  - left.
    unfold invalid_triple.
    exists m I.
    splits~.
    exists m'0 n1.
    splits~.
    math.
Qed.

Lemma csq_trace_rule c P Q P' Q' 
  (H1 : |= (P -> P')) (H3 : |= (Q' -> Q)) n :
  invalid_triple c P Q n ->
  invalid_triple c P' Q' n.
Proof.
  intro.
  unfold invalid_triple in *.
  exists* H.
  exists m I.
  split.
  apply H1, H.
  exists m' n'.
  splits~.
  contra H2.
  now apply H3.
Qed.

Lemma case_trace_rule c b P Q n :
  invalid_triple c P Q n ->
    invalid_triple c (P /\ b)%A Q n \/ invalid_triple c (P /\ ~b)%A Q n.
Proof.
  intro.
  unfold invalid_triple in H.
  exists* H.
  either (m + I |= b)%V.
  - left.
    unfold invalid_triple.
    exists m I.
    splits~.
    simpls~.
    exists m' n'.
    splits~.
  - right.
    unfold invalid_triple.
    exists m I.
    splits~.
    simpls~.
    exists m' n'.
    splits~.
Qed.

End CyclicTraceRules.

Section InfiniteInvalid.

Variable rg : rule_graph uhl.
Variable lift_valid : graph_lift_valid rg.

Definition invalid_stmt s n : Prop :=
  match s with 
  | StmtAssrt P => ~ (valid_assrt P)
  | StmtTriple c P Q => invalid_triple c P Q n
  end.

(* Locate is_prem.

Lemma invalid_stmt_has_invalid_prem :
  forall nd n,
    invalid_stmt (rg.(rg_conc) nd) n ->
    exists prem,
      is_prem prem nd /\ invalid_stmt (rg.(rg_conc) prem) n.





Locate derives.  *)

End InfiniteInvalid.
