Set Implicit Arguments.
From Lang Require Export Assertions.
From Lang Require Import RuleGraphs.

Implicit Type m : mem.
Implicit Type n : int.
Implicit Type I : binding.
Implicit Type c : cmd.

Module RGP <: RuleGraphParams.
  
  Variant stmt_aux := 
    | StmtTriple (c:cmd) (P Q : assrt)
    | StmtAssrt (P:assrt).
  Definition stmt := stmt_aux.
  
  Definition liftable (s : stmt) : Prop :=
    match s with 
    | StmtAssrt _ => True
    | _ => False
    end.

  Definition valid_stmt (s : stmt) : Prop :=
    match s with 
    | StmtAssrt P => valid_assrt P
    | StmtTriple c P Q => valid_triple c P Q
    end.

  Notation "'|-' c ':' P '=>' Q" := 
    (StmtTriple c P%A Q%A)
    (at level 50, c at next level, no associativity).

  Notation "'|-' P" :=
    (StmtAssrt P%A)
    (at level 50, no associativity).

  Variant rule_aux :=
    | HL_CSQ
    | HL_Skip
    | HL_Assn
    | HL_Seq
    | HL_If
    | HL_WhileTrue
    | HL_WhileFalse.
  Definition rule := rule_aux.

  Variant valid_rule_aux : rule -> list stmt -> stmt -> Prop :=
    | Valid_HL_CSQ c P P' Q Q' : 
        valid_rule_aux HL_CSQ [(|- (P->P')); (|- c : P' => Q'); (|- (Q'->Q))] (|- c : P => Q)
    | Valid_HL_Skip P : 
        valid_rule_aux HL_Skip [] (|- CSkip : P => P)
    | Valid_HL_Assn x a P : 
        valid_rule_aux HL_Assn [] (|- CAssn x a : P[a/x] => P)
    | Valid_HL_Seq c1 c2 P Q R : 
        valid_rule_aux HL_Seq [(|- c1 : P => Q); (|- c2 : Q => R)] (|- CSeq c1 c2 : P => R)
    | Valid_HL_If c P Q (b:bexp) c' : 
        valid_rule_aux HL_If [(|- c : P /\ b => Q); (|- c' : P /\ ~b => Q)] (|- CIf b c c' : P => Q)
    | Valid_HL_WhileTrue c P Q (b:bexp) : 
        valid_rule_aux HL_WhileTrue [(|- CSeq c (CWhile b c) : P /\ b => Q)] (|- CWhile b c : P /\ b => (Q /\ ~b))
    | Valid_HL_WhileFalse P b c : 
        valid_rule_aux HL_WhileFalse [] (|- CWhile b c : P /\ ~b => (P /\ ~b)).
  Definition valid_rule := valid_rule_aux.

End RGP.

Module Import TripleGraph := RuleGraph(RGP).

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

Theorem hl_sound :
  forall (rg : rule_graph), rules_in_graph_sound rg.
Proof.
  intro.
  unfold rules_in_graph_sound.
  intros.
  destruct H.
  unfold sound_rule.
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

Section Example.

Definition nodes : NodeSet.t :=
  NodeSetProperties.of_list ([0;1;2;3;4;5;6;7]%nat)%list.

Definition node := {nd | NodeSet.In nd nodes}.

End Example.
