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
