Set Implicit Arguments.
From Lang Require Export Assertions.

Implicit Type m : mem.
Implicit Type n : int.
Implicit Type I : binding.
Implicit Type c : cmd.

Reserved Notation "'|-' c ':' P '=>' Q" 
  (at level 50, c at next level, no associativity).

Inductive derivable_triple : cmd -> assrt -> assrt -> Prop :=
  (* Structural rules *)
  | HL_CSQ c P Q P' Q'
    (H1 : |= (P->P')) (H2 : |- c : P' => Q') (H3 : |= (Q'->Q)) :
    |- c : P => Q
  | HL_Case c P Q P'
    (H1 : |- c : P /\ P' => Q) 
    (H2 : |- c : P /\ ~ P' => Q) :
    |- c : P => Q
  (* Symbolic execution rules *)
  | HL_Skip P : 
    |- CSkip : P => P
  | HL_Assn x (a : aexp) P :
    |- CAssn x a : P[a/x] => P
  | HL_Seq c c' P Q R
    (H1 : |- c : P => Q) (H2 : |- c' : Q => R) :
    |- CSeq c c' : P => R
  | HL_IfTrue (b:bexp) c c' P Q
    (H : |- c : P /\ b => Q) :
    |- CIf b c c' : P /\ b => Q
  | HL_IfFalse (b:bexp) c c' P Q
    (H : |- c' : P /\ ~ b => Q) :
    |- CIf b c c' : P /\ ~ b => Q
  | HL_WhileTrue (b:bexp) c P Q
    (H : |- CSeq c (CWhile b c) : P /\ b => Q) :
    |- CWhile b c : P /\ b => (Q /\ ~ b)
  | HL_WhileFalse (b:bexp) c P :
    |- CWhile b c : P /\ ~ b => (P /\ ~ b)
where "'|-' c ':' P '=>' Q" := 
  (derivable_triple c P%A Q%A).


Section Soundness.

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

Lemma case_sound c P Q P' 
  (H1 : |= c : P /\ P' => Q) 
  (H2 : |= c : P /\ ~ P' => Q) 
  : |= c : P => Q.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros.
  simpls.
  specializes H1 m I.
  specializes H2 m I.
  destruct (classic (m, I |= P')).
  + specializes H1 (conj H H3). 
    specializes~ H1 H0.
  + specializes H2 (conj H H3). 
    specializes~ H2 H0.
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

Lemma if_true_sound (b:bexp) c c' P Q :
  |= c : P /\ b => Q ->
  |= CIf b c c' : P /\ b => Q.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros.
  simpls.
  unfolds in H1.
  exists* H1. sort.
  assert (H2 : beval m b) by (destruct H0; now rewrite bexp_assrt_equiv in H2).
  inverts H1. inverts H3. 2 : contradiction.
  specializes H H0. 
  assert (H3 : yields c'0 m'0 m') by (unfolds; exists~ n0).
  specializes~ H H3.
Qed.

Lemma if_false_sound (b:bexp) c c' P Q :
  |= c' : P /\ ~ b => Q ->
  |= CIf b c c' : P /\ ~ b => Q.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros.
  simpls.
  unfolds in H1.
  exists* H1. sort.
  assert (H2 : ~ beval m b) by (destruct H0; now rewrite bexp_assrt_equiv in H2).
  inverts H1. inverts H3. contradiction.
  specializes H H0.
  assert (H3 : yields c'0 m'0 m') by (unfolds; exists~ n0).
  specializes~ H H3.
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

Theorem soundness c P Q :
  |- c : P => Q -> |= c : P => Q.
Proof.
  introv H. induction H; simpls.
  - eapply csq_sound; eauto.
  - applys case_sound IHderivable_triple1 IHderivable_triple2.
  - apply skip_sound. 
  - apply assn_sound.
  - eapply seq_sound; eauto.
  - eapply if_true_sound; eauto.
  - eapply if_false_sound; eauto.
  - eapply while_true_sound; eauto.
  - eapply while_false_sound; eauto.
Qed.

End Soundness.



Section DerivedRules.

Lemma false_rule_derivable c Q :
  |- c : false => Q.
Proof.
  generalize dependent Q; induction c; intros.
  - apply HL_CSQ with (P':=false) (Q':=false).
    + apply valid_ex_falso.
    + apply HL_Skip.
    + apply valid_ex_falso.
  - apply HL_Seq with (Q:=false). apply IHc1. apply IHc2.
  - apply HL_Case with (P':=e).
    + apply HL_IfTrue. 
      apply HL_CSQ with (P':=false) (Q':=Q).
      * apply valid_imp_and_l, valid_ex_falso.
      * apply IHc1.
      * apply valid_imp_refl.
    + apply HL_IfFalse.
      apply HL_CSQ with (P':=false) (Q':=Q).
      * apply valid_imp_and_l, valid_ex_falso.
      * apply IHc2.
      * apply valid_imp_refl.
  - pose proof (aexp_no_ivars e).
    apply HL_CSQ with (P':=false) (Q':=false).
    * apply valid_ex_falso.
    * apply HL_Assn with (a:=e) (x:=x) (P:=false).
    * apply valid_ex_falso.
  - apply HL_CSQ with 
      (P':=(false /\ ~ e)%A)
      (Q':=(false /\ ~ e)%A).
    * apply valid_ex_falso.
    * apply HL_WhileFalse.
    * apply valid_imp_and_l, valid_ex_falso.
Qed.

Lemma HL_CSQ_L c P Q P' :
  |= (P->P') ->
  |- c : P' => Q ->
  |- c : P => Q.
Proof.
  intros.
  now apply HL_CSQ with (P':=P') (Q':=Q).
Qed.

Lemma HL_CSQ_R c P Q Q' :
  |- c : P => Q' ->
  |= (Q'->Q) ->
  |- c : P => Q.
Proof.
  intros.
  now apply HL_CSQ with (P':=P) (Q':=Q').
Qed.

Lemma HL_Skip' P Q :
  |= (P -> Q) ->
  |- CSkip : P => Q.
Proof.
  intros. applys HL_CSQ_L H.
  apply HL_Skip.
Qed.

Lemma HL_Assn' x a P Q :
  |= (P -> Q[a/x]) ->
  |- CAssn x a : P => Q.
Proof.
  intros. applys HL_CSQ_L H.
  apply HL_Assn.
Qed.

Lemma HL_IfTrue' (b:bexp) c c' P Q :
  |= (P -> b) ->
  |- c : P /\ b => Q ->
  |- CIf b c c' : P => Q.
Proof.
  intros. assert (|= (P -> P /\ b)).
  { unfolds. intros. simpls.
    intros. splits~.
    apply~ H. }
  applys HL_CSQ_L H1.
  apply~ HL_IfTrue.
Qed.

Lemma HL_IfFalse' (b:bexp) c c' P Q :
  |= (P -> ~ b) ->
  |- c' : P /\ ~ b => Q ->
  |- CIf b c c' : P => Q.
Proof.
  intros. assert (|= (P -> P /\ ~b)).
  { unfolds. intros. simpls.
    intros. splits~.
    apply~ H. }
  applys HL_CSQ_L H1.
  apply~ HL_IfFalse.
Qed.

Lemma HL_If (b:bexp) c c' P Q :
  |- c : P /\ b => Q ->
  |- c' : P /\ ~ b => Q ->
  |- CIf b c c' : P => Q.
Proof.
  intros.
  apply HL_Case with (P':=b).
  apply~ HL_IfTrue.
  apply~ HL_IfFalse.
Qed.

Lemma HL_WhileTrue' (b:bexp) c P Q :
  |= (P -> b) ->
  |- CSeq c (CWhile b c) : P /\ b => Q ->
  |- CWhile b c : P => Q.
Proof.
  intros. assert (|= (P -> P /\ b)).
  { unfolds. intros. simpls.
    intros. splits~.
    apply~ H. }
  assert (|= (Q /\ ~b -> Q)).
  { apply~ valid_imp_and_l. }
  applys HL_CSQ H1 H2.
  apply~ HL_WhileTrue.
Qed.

Lemma HL_WhileFalse' (b:bexp) c P Q :
  |= (P -> ~b) ->
  |= (P -> Q) ->
  |- CWhile b c : P => Q.
Proof.
  intros. assert (|= (P -> P /\ ~b)).
  { unfolds. intros. simpls.
    intros. splits~.
    apply~ H. }
  assert (|= (P /\ ~b -> Q)).
  { apply~ valid_imp_and_l. }
  applys HL_CSQ H1 H2.
  apply~ HL_WhileFalse.
Qed.

End DerivedRules.
