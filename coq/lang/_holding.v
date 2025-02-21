Section Interp.

Definition interp (P : bexp) : [mem] :=
  fun m => beval m P.

Notation "'[[' P ']]'" := (interp P).

Lemma interp_and (P Q : bexp) :
  [[BAnd P Q]] = [[P]] ∩ [[Q]].
Proof.
  unfolds. extensionality m.
  simpls. unfolds subset_and.
  apply istrue_and_eq.
Qed.

Lemma interp_or (P Q : bexp) :
  [[BOr P Q]] = [[P]] ∪ [[Q]].
Proof.
  extensionality m.
  unfolds. simpls.
  unfolds subset_or.
  apply istrue_or_eq.
Qed.

Lemma interp_true :
  [[BVal true]] = ⬤.
Proof.
  unfolds. extensionality m.
  simpls. rewrite istrue_true_eq.
  symmetry. apply univ_set_true.
Qed.

Lemma interp_false :
  [[BVal false]] = ∅.
Proof.
  unfolds. extensionality m.
  simpls. rewrite istrue_false_eq.
  symmetry. apply emptyset_false.
Qed.

Lemma interp_not P :
  [[BNot P]] = not ∘ [[P]].
Proof.
  unfolds. extensionality m.
  simpls. now rewrite istrue_neg_eq.
Qed.

Lemma interp_imp (P Q : bexp) :
  [[BImp P Q]] = not ∘ [[P]] ∪ [[Q]].
Proof.
  unfolds. extensionality m.
  simpls. rewrite Bool.implb_orb.
  unfolds subset_or.
  destruct (beval m P), (beval m Q); simpls.
  all: try rewrite istrue_true_eq; try rewrite istrue_false_eq.
  - symmetry. rewrite prop_eq_True_eq. right~.
  - symmetry. apply prop_eq_False. intro.
    destruct~ H.
  - symmetry. rewrite prop_eq_True_eq. right~.
  - symmetry. rewrite prop_eq_True_eq. left~.
Qed.

End Interp.

Notation "'[[' P ']]'" := (interp P).

Section Valid.

Definition valid (b : bexp) :=
  forall m, beval m b.

Lemma valid_interp b :
  valid b <-> [[b]] = ⬤.
Proof.
  splits; intros.
  unfolds interp, valid.
  extensionality m. specializes H m.
  auto.
  intro. apply equal_f with m in H.
  unfolds in H.
  rewrite H. now rewrite univ_set_true.
Qed.

Notation "'⊨' P" := (valid P) (at level 50).

Lemma true_eq H :
  True = H <-> H.
Proof.
  splits; intros; subst~.
  symmetry. rewrite~ prop_eq_True_eq.
Qed.

Lemma valid_and (P Q : bexp) :
  ⊨ BAnd P Q <-> (⊨ P /\ ⊨ Q).
Proof.
  unfolds valid. splits; intros.
  - apply forall_conj_inv_1. intros.
    specializes H x1. simpls.
    now rewrite <- istrue_and_eq.
  - destruct H. specializes H m. specializes H0 m.
    simpls. rewrite istrue_and_eq. splits~.  
Qed.

Lemma valid_or (P Q : bexp) :
  (⊨ P \/ ⊨ Q) -> ⊨ BOr P Q.
Proof.
  unfolds valid. intros. simpls.
  rewrite istrue_or_eq.
  destruct H; specializes H m.
  auto. auto.
Qed.

Lemma valid_imp (P Q : bexp) :
  [[P]] ⊆ [[Q]] <->
  ⊨ BImp P Q.
Proof.
  splits; intros.
  - intro m. simpls. specializes H m.
    unfolds interp.
    destruct (beval m P).
    2: { now rewrite Bool.implb_false_l. }
    destruct~ H. now rewrite Bool.implb_same.
  - intros m HP. unfolds valid, interp.
    simpls. specializes H m.
    destruct (beval m P).
    2: { easy. }
    now destruct (beval m Q).
Qed.

End Valid.




Section Example.


Local Lemma ex1_proof :
  |- c1 : true => AssrtEqA (AVar "x") (AVal 50).
Proof.
  unfold c1.
  apply HL_Assn'.
  simpls. unfolds.
  intros. simpls. intros.
  case_if~.
Qed.


Local Definition c2 : cmd :=
  (*CAssn "x" #n ;;*)
  CAssn "i" #3 ;;
  CWhile (BLt #0 (AVar "i"))
  (CAssn "x" (AMul (AVar "x") #2);;
   CAssn "i" (ASub (AVar "i") #1)).

Local Lemma ex2_eval m :
  yields c2 m (m["x"=8*m "x"]["i"=0]).
Proof.
  econstructor.
  econstructor. econstructor. econstructor.
  simpls. econstructor.
  apply StepSeqSkip. econstructor.
  econstructor.
  simpls. now rewrite upd_read1.
  econstructor. repeat econstructor.
  simpls. rewrite upd_read1_diff; [|discriminate].
  remember (m "x") as x0.
  econstructor. econstructor.
  apply StepSeqSkip.
  econstructor. econstructor.
  econstructor. econstructor.
  apply StepSeqSkip.
  simpls. rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. econstructor.
  simpls. now rewrite upd_read1.
  econstructor. econstructor.
  econstructor. econstructor.
  simpls. rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. econstructor.
  apply StepSeqSkip.
  econstructor. econstructor.
  econstructor. simpls.
  rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. apply StepSeqSkip.
  econstructor. econstructor.
  simpls. now rewrite upd_read1.
  econstructor. econstructor.
  econstructor. econstructor.
  simpls. rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. econstructor.
  apply StepSeqSkip.
  econstructor. econstructor.
  econstructor. simpls.
  rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. apply StepSeqSkip.
  econstructor. apply StepWhileFalse.
  simpls. now rewrite upd_read1.
  replace (x0*2*2*2) with (8*x0). 2: math.
  replace (3-1-1-1) with 0. 2: math.
  constructor.
Qed.

Notation EQ x n := (AssrtEqA (AVar x) #n).

Lemma ex2_proof n :
  |- c2 : 
    EQ "x" n =>
    (EQ "x" (8*n) /\ EQ "i" 0).
Proof.
  unfold c2.
  apply HL_Seq with (Q:=(EQ "x" n /\ EQ "i" 3)%A).
  { simpls. apply HL_Assn'.
    introv ?. simpls.
    case_if~. simpls. splits~.
    case_if~. }
  apply HL_WhileTrue'.
  { simpls. introv (?&?).
    simpls. math. }
  apply HL_Seq with (Q:=(EQ "x" (n*2) /\ EQ "i" 2)%A).
  { apply HL_Seq with (Q:=(EQ "x" (n*2) /\ EQ "i" 3)%A).
    { apply HL_Assn'. simpls.
      introv (?&?&?). simpls.
      case_if~. simpls. splits~. math.
      case_if~. simpls. math. }
    apply HL_Assn'.
    introv ?. simpls.
    case_if~. simpls. splits~. math.
    case_if~. simpls. math. }
  
  apply HL_WhileTrue'.
  { simpls. introv (?&?).
    simpls. math. }
  apply HL_Seq with (Q:=(EQ "x" (n*4) /\ EQ "i" 1)%A).
  { apply HL_Seq with (Q:=(EQ "x" (n*4) /\ EQ "i" 2)%A).
    { apply HL_Assn'. simpls.
      introv (?&?&?). simpls.
      case_if~. simpls. splits~. math.
      case_if~. simpls. math. }
    apply HL_Assn'.
    introv ?. simpls.
    case_if~. simpls. splits~. math.
    case_if~. simpls. math. }

  apply HL_WhileTrue'.
  { simpls. introv (?&?).
    simpls. math. }
  apply HL_Seq with (Q:=(EQ "x" (n*8) /\ EQ "i" 0)%A).
  { apply HL_Seq with (Q:=(EQ "x" (n*8) /\ EQ "i" 1)%A).
    { apply HL_Assn'. simpls.
      introv (?&?&?). simpls.
      case_if~. simpls. splits~. math.
      case_if~. simpls. math. }
    apply HL_Assn'.
    introv ?. simpls.
    case_if~. simpls. splits~. math.
    case_if~. simpls. math. }

  apply HL_WhileFalse'.
  { introv (?&?). simpls. math. }
  introv (?&?). simpls. math.
Qed.


    
End Example.

