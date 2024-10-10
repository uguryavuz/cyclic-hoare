Set Implicit Arguments.

Import SigTNotations.

From Lang Require Import Util.

Open Scope fmap_scope.



Section Memory.

Notation varid := string.

Definition mem := varid -> int.
Implicit Type m : mem.


Definition upd m x n : mem :=
  fun x' => If x = x' then n else m x'.


Lemma upd_shadow1 m x n n' :
  upd (upd m x n) x n' = upd m x n'.
Proof using.
  unfolds upd. extensionality x'.
  case_if~.
Qed.

Lemma upd_shadow2 m x y k n n' :
  upd (upd (upd m x n) y k) x n' = upd (upd m y k) x n'.
Proof using.
  unfold upd. extensionality x'.
  case_if~.
Qed.

Lemma upd_swap_diff m x x' n n' :
  x <> x' ->
  upd (upd m x n) x' n' = upd (upd m x' n') x n.
Proof using.
  intros.
  extensionality x''.
  unfolds. case_if~.
  case_if~.
Qed.

Lemma upd_read1 m x n :
  (upd m x n) x = n.
Proof using.
  unfolds. case_if~.
Qed.

Lemma upd_read2 m x x' n n' :
  x <> x' ->
  upd (upd m x n) x' n' x = n.
Proof using.
  intros.
  unfolds. case_if~. case_if~.
Qed.




End Memory.
Notation varid := string.
Implicit Type m : mem.


Section Language.

Inductive aexp :=
| AVal (n:int)
| AVar (x:varid)
| ANeg (a:aexp)
| AAdd (a1 a2:aexp)
| ASub (a1 a2:aexp)
| AMul (a1 a2:aexp)
.

Inductive bexp :=
| BVal (b:bool)
| BNot (b:bexp)
| BAnd (b1 b2:bexp)
| BOr  (b1 b2:bexp)
| BImp (b1 b2:bexp)
| BEqB (b1 b2:bexp)
| BEqA (a1 a2:aexp)
| BLt  (a1 a2:aexp)
| BLeq (a1 a2:aexp)
.


Inductive cmd :=
| CSkip
| CSeq (c : cmd) (c : cmd)
| CIf (e : bexp) (c1 c2 : cmd)
| CAssn (x : varid) (e : aexp)
| CWhile (e : bexp) (c : cmd)
.



Fixpoint aeval m a : int :=
match a with
| AVal n => n
| AVar x => m x
| ANeg a => -(aeval m a)
| AAdd a1 a2 => (aeval m a1) + (aeval m a2)
| ASub a1 a2 => (aeval m a1) - (aeval m a2)
| AMul a1 a2 => (aeval m a1) * (aeval m a2)
end.

Fixpoint beval m b : bool :=
match b with
| BVal b => b
| BNot b => ! (beval m b)
| BAnd b1 b2 => (beval m b1) && (beval m b2)
| BOr  b1 b2 => (beval m b1) || (beval m b2)
| BImp b1 b2 => implb (beval m b1) (beval m b2)
| BEqB b1 b2 => Bool.eqb (beval m b1) (beval m b2)
| BEqA a1 a2 => Z.eqb (aeval m a1) (aeval m a2)
| BLt  a1 a2 => Z.ltb (aeval m a1) (aeval m a2)
| BLeq a1 a2 => Z.leb (aeval m a1) (aeval m a2)
end.


Inductive cstep : cmd -> mem -> cmd -> mem -> Prop :=
| StepSeq m m' c1 c1' c2
  (H1 : cstep c1 m c1' m')
  : cstep (CSeq c1 c2) m (CSeq c1' c2) m'
| StepSeqSkip m c
  : cstep (CSeq CSkip c) m c m
| StepIfTrue m b c1 c2
  (Hg : beval m b)
  : cstep (CIf b c1 c2) m c1 m
| StepIfFalse m b c1 c2
  (Hg : ~ beval m b)
  : cstep (CIf b c1 c2) m c2 m
| StepWhileTrue m b c
  (Hg : beval m b)
  : cstep (CWhile b c) m (CSeq c (CWhile b c)) m
| StepWhileFalse m b c
  (Hg : ~ beval m b)
  : cstep (CWhile b c) m CSkip m
| StepAssn m x a
  : cstep (CAssn x a) m CSkip (upd m x (aeval m a))
.


Inductive multistep : cmd -> mem -> cmd -> mem -> nat -> Prop :=
| Multi0 c m : multistep c m c m O
| MultiI c c' c'' m m' m'' n
  (H : cstep c m c' m') 
  (H' : multistep c' m' c'' m'' n)
  : multistep c m c'' m'' (S n)
.

Definition yields c m m' :=
  exists n, multistep c m CSkip m' n.

Definition terminates c m := 
  exists m', yields c m m'.

Definition diverges c m :=
  ~ terminates c m.


Lemma seq_intermediate c1 c2 m m'' :
  yields (CSeq c1 c2) m m'' ->
  exists m',
  yields c1 m m' /\
  yields c2 m' m''.
Proof using.
  intros (n&H).
  generalize dependent H.
  generalize dependent c1.
  generalize dependent c2.
  generalize dependent m.
  generalize dependent m''.
  
  induction n.
  { intros. inverts H. }
  intros. sort.
  inverts H. sort.
  inverts H5.
  2: { 
    exists m'. splits~.
    unfolds. exists. constructor.
    unfolds. exists. apply H'.
  }
  specializes IHn H'. exists* IHn.
  exists m'0. splits~.
  unfold yields in IHn. exists* IHn.
  sort. unfolds. exists (S n0).
  econstructor. apply H6. auto.
Qed.

End Language.



Lemma eq_emptyset {T} (X : [T]) :
  X = ∅ <-> ~ exists x, X x.
Proof using.
  splits; intros.
  subst. intro. now exists* H.
  contra H. now apply not_emptyset in H.
Qed.

Ltac empty_inhab_false :=
  match goal with
  | [ H : ∅ _ |- _ ] => 
    rewrite emptyset_false in H; contradiction
  end.



Section Binding.

Notation ivarid := string.
Inductive ivar : Type :=
| IVar (i : ivarid)
.

Definition binding := ivar -> int.
Implicit Type I : binding.


Definition iupd I i n : binding :=
  fun i' => If i = i' then n else I i'.


Lemma iupd_shadow1 I i n n' :
  iupd (iupd I i n) i n' = iupd I i n'.
Proof using.
  unfolds iupd. extensionality x'.
  case_if~.
Qed.

Lemma iupd_shadow2 I i j k n n' :
  iupd (iupd (iupd I i n) j k) i n' = iupd (iupd I j k) i n'.
Proof using.
  unfold iupd. extensionality x'.
  case_if~.
Qed.

Lemma iupd_swap_diff I i i' n n' :
  i <> i' ->
  iupd (iupd I i n) i' n' = iupd (iupd I i' n') i n.
Proof using.
  intros.
  extensionality i''.
  unfolds. case_if~.
  case_if~.
Qed.

Lemma iupd_read1 I i n :
  (iupd I i n) i = n.
Proof using.
  unfolds. case_if~.
Qed.

Lemma iupd_read2 I i i' n n' :
  i <> i' ->
  iupd (iupd I i n) i' n' i = n.
Proof using.
  intros.
  unfolds. case_if~. case_if~.
Qed.

End Binding.
Notation ivarid := string.
Implicit Type I : binding.

Section Assertions.

Inductive aexpv :=
| AvVal (n:int)
| AvVar (x:varid)
| AvNeg (a:aexpv)
| AvAdd (a1 a2:aexpv)
| AvSub (a1 a2:aexpv)
| AvMul (a1 a2:aexpv)
| AvIVar (i:ivar)
.

Inductive assrt :=
| AssrtVal (b:bool)
| AssrtNot (b:assrt)
| AssrtAnd (b1 b2:assrt)
| AssrtOr  (b1 b2:assrt)
| AssrtImp (b1 b2:assrt)
| AssrtEqB (b1 b2:assrt)
| AssrtEqA (a1 a2:aexpv)
| AssrtLt  (a1 a2:aexpv)
| AssrtLeq (a1 a2:aexpv)
| AssrtForall (i:ivar) (b:assrt)
| AssrtExists (i:ivar) (b:assrt)
.

Fixpoint aveval m I a : int :=
match a with
| AvVal n => n
| AvVar x => m x
| AvIVar i => I i
| AvNeg a => -(aveval m I a)
| AvAdd a1 a2 => (aveval m I a1) + (aveval m I a2)
| AvSub a1 a2 => (aveval m I a1) - (aveval m I a2)
| AvMul a1 a2 => (aveval m I a1) * (aveval m I a2)
end.

Implicit Type P Q : assrt.

Fixpoint sat m I P : Prop :=
  match P with
  | AssrtVal b => b
  | AssrtNot P => ~ sat m I P
  | AssrtAnd P Q => sat m I P /\ sat m I Q
  | AssrtOr P Q => sat m I P \/ sat m I Q
  | AssrtImp P Q => sat m I P -> sat m I Q
  | AssrtEqB P Q => sat m I P = sat m I Q
  | AssrtEqA a1 a2 => aveval m I a1 = aveval m I a2
  | AssrtLt a1 a2 => aveval m I a1 < aveval m I a2
  | AssrtLeq a1 a2 => aveval m I a1 <= aveval m I a2
  | AssrtForall i P => forall n, sat m (iupd I i n) P
  | AssrtExists i P => exists n, sat m (iupd I i n) P
  end.

Notation "m ',' I '|=' P" := (sat m I P) (at level 50).

Fixpoint aexp_to_aexpv a : aexpv :=
  match a with
  | AVal n => AvVal n
  | AVar x => AvVar x
  | ANeg a => AvNeg (aexp_to_aexpv a)
  | AAdd a1 a2 => AvAdd (aexp_to_aexpv a1) (aexp_to_aexpv a2)
  | ASub a1 a2 => AvSub (aexp_to_aexpv a1) (aexp_to_aexpv a2)
  | AMul a1 a2 => AvMul (aexp_to_aexpv a1) (aexp_to_aexpv a2)
  end.

Lemma aexp_aexpv_equiv m I a :
  aveval m I (aexp_to_aexpv a) = aeval m a.
Proof using.
  induction a; simpls; f_equal~.
Qed.

Fixpoint bexp_to_assrt b : assrt :=
  match b with
  | BVal b => AssrtVal b
  | BNot b => AssrtNot (bexp_to_assrt b)
  | BAnd b1 b2 => AssrtAnd (bexp_to_assrt b1) (bexp_to_assrt b2)
  | BOr  b1 b2 => AssrtOr (bexp_to_assrt b1) (bexp_to_assrt b2)
  | BImp b1 b2 => AssrtImp (bexp_to_assrt b1) (bexp_to_assrt b2)
  | BEqB b1 b2 => AssrtEqB (bexp_to_assrt b1) (bexp_to_assrt b2)
  | BEqA a1 a2 => AssrtEqA (aexp_to_aexpv a1) (aexp_to_aexpv a2)
  | BLt  a1 a2 => AssrtLt (aexp_to_aexpv a1) (aexp_to_aexpv a2)
  | BLeq a1 a2 => AssrtLeq (aexp_to_aexpv a1) (aexp_to_aexpv a2)
  end.

Lemma bexp_assrt_equiv m I b :
  sat m I (bexp_to_assrt b) <-> beval m b.
Proof using.
  induction b; simpls.
  - reflexivity.
  - split; intros. contra H. apply IHb. 
    destruct (beval m b); simpls; auto.
    intro. apply IHb in H0. rewrite H0 in H. auto.
  - rewrite IHb1, IHb2.
    rewrite istrue_and_eq.
    easy.
  - rewrite IHb1, IHb2.
    rewrite istrue_or_eq.
    easy.
  - rewrite IHb1, IHb2.
    destruct (beval m b1), (beval m b2); simpls.
    + easy.
    + split. intro. auto. auto.
    + split. intro. auto. auto.
    + split. intro. auto. auto.
  - split.
    + intro. destruct (beval m b1), (beval m b2); simpls; auto;
      rewrite H in IHb1; rewrite IHb1 in IHb2; apply IHb2; auto.
    + intro. 
      destruct (beval m b1), (beval m b2); simpls; try easy.
      * rewrite <- IHb1 in IHb2. apply prop_ext. easy.
      * rewrite <- IHb1 in IHb2. apply prop_ext. easy.
  - do 2 rewrite aexp_aexpv_equiv.
    rewrite <- Z.eqb_eq. easy.
  - do 2 rewrite aexp_aexpv_equiv.
    rewrite <- bool_eq_true_eq.
    split; intros.
    * apply Z.ltb_lt.
      math.
    * apply Z.ltb_lt in H.
      math.
  - do 2 rewrite aexp_aexpv_equiv.
    rewrite <- bool_eq_true_eq.
    split; intros.
    * apply Z.leb_le.
      math.
    * apply Z.leb_le in H.
      math.
Qed.

Fixpoint has_ivars (a : aexpv) : Prop :=
  match a with
  | AvVal _ => False
  | AvVar _ => False
  | AvNeg a => has_ivars a
  | AvAdd a1 a2 => has_ivars a1 \/ has_ivars a2
  | AvSub a1 a2 => has_ivars a1 \/ has_ivars a2
  | AvMul a1 a2 => has_ivars a1 \/ has_ivars a2
  | AvIVar _ => True
  end.

Lemma aexp_no_ivars (a : aexp) :
  ~ has_ivars (aexp_to_aexpv a).
Proof.
  induction a; simpls; intro; auto; destruct~ H.
Qed.

Definition aexpv_subst (x : varid) (a' : aexpv) : aexpv -> aexpv :=
  fix rec (a : aexpv) :=
    match a with
    | AvVal n => AvVal n
    | AvVar x' => If x = x' then a' else AvVar x'
    | AvNeg a => AvNeg (rec a)
    | AvAdd a1 a2 => AvAdd (rec a1) (rec a2)
    | AvSub a1 a2 => AvSub (rec a1) (rec a2)
    | AvMul a1 a2 => AvMul (rec a1) (rec a2)
    | AvIVar i => AvIVar i
    end.

Definition aexpv_isubst (i : ivar) (a' : aexpv) : aexpv -> aexpv :=
  fix rec (a : aexpv) :=
    match a with
    | AvVal n => AvVal n
    | AvVar x => AvVar x
    | AvNeg a => AvNeg (rec a)
    | AvAdd a1 a2 => AvAdd (rec a1) (rec a2)
    | AvSub a1 a2 => AvSub (rec a1) (rec a2)
    | AvMul a1 a2 => AvMul (rec a1) (rec a2)
    | AvIVar i' => If i = i' then a' else AvIVar i'
    end. 

Definition assrt_subst (x : varid) (a : aexpv) (H : ~ has_ivars a) : assrt -> assrt :=
  fix rec (P : assrt) :=
    match P with
    | AssrtVal b => AssrtVal b
    | AssrtNot P => AssrtNot (rec P)
    | AssrtAnd P Q => AssrtAnd (rec P) (rec Q)
    | AssrtOr P Q => AssrtOr (rec P) (rec Q)
    | AssrtImp P Q => AssrtImp (rec P) (rec Q)
    | AssrtEqB P Q => AssrtEqB (rec P) (rec Q)
    | AssrtEqA a1 a2 => AssrtEqA (aexpv_subst x a a1) (aexpv_subst x a a2)
    | AssrtLt a1 a2 => AssrtLt (aexpv_subst x a a1) (aexpv_subst x a a2)
    | AssrtLeq a1 a2 => AssrtLeq (aexpv_subst x a a1) (aexpv_subst x a a2)
    | AssrtForall i P => AssrtForall i (rec P)
    | AssrtExists i P => AssrtExists i (rec P)
    end.

Definition assrt_isubst (i : ivar) (a : aexpv) (H : ~ has_ivars a) : assrt -> assrt :=
  fix rec (P : assrt) :=
    match P with
    | AssrtVal b => AssrtVal b
    | AssrtNot P => AssrtNot (rec P)
    | AssrtAnd P Q => AssrtAnd (rec P) (rec Q)
    | AssrtOr P Q => AssrtOr (rec P) (rec Q)
    | AssrtImp P Q => AssrtImp (rec P) (rec Q)
    | AssrtEqB P Q => AssrtEqB (rec P) (rec Q)
    | AssrtEqA a1 a2 => AssrtEqA (aexpv_isubst i a a1) (aexpv_isubst i a a2)
    | AssrtLt a1 a2 => AssrtLt (aexpv_isubst i a a1) (aexpv_isubst i a a2)
    | AssrtLeq a1 a2 => AssrtLeq (aexpv_isubst i a a1) (aexpv_isubst i a a2)
    | AssrtForall i' P => AssrtForall i' (If i = i' then P else rec P)
    | AssrtExists i' P => AssrtExists i' (If i = i' then P else rec P)
    end.

Lemma aexpv_subst_equiv m I x a n : 
  aveval m I (aexpv_subst x (AvVal n) a) = aveval (upd m x n) I a.
Proof using.
  induction a; simpls; auto; try math.
  + case_if; simpls.
    * subst. rewrite upd_read1. trivial.
    * unfold upd. case_if. trivial.
Qed.

Lemma aexpv_isubst_equiv m I i a n : 
  aveval m I (aexpv_isubst i (AvVal n) a) = aveval m (iupd I i n) a.
Proof using.
  induction a; simpls; auto; try math.
  + case_if; simpls.
    * subst. rewrite iupd_read1. trivial.
    * unfold iupd. case_if. trivial.
Qed.

Lemma assrt_subst_equiv m I x n P H :
  sat m I (assrt_subst x (AvVal n) H P) <-> sat (upd m x n) I P.
Proof using.
  generalize dependent n. 
  generalize dependent I. 
  induction P; simpls; auto; try easy.
  - intros. rewrite IHP. easy.
  - intros. rewrite IHP1, IHP2. easy.
  - intros. rewrite IHP1, IHP2. easy.
  - intros. rewrite IHP1, IHP2. easy.
  - intros. split. 
    + intros. 
      specializes IHP1 n. 
      specialize IHP1 with H. 
      rewrite H0 in IHP1. 
      specializes IHP2 n.
      specialize IHP2 with H.
      rewrite IHP1 in IHP2. apply prop_ext. auto.
    + intros. 
      specializes IHP1 n. 
      specialize IHP1 with H. 
      rewrite H0 in IHP1. 
      specializes IHP2 n.
      specialize IHP2 with H.
      rewrite <- IHP1 in IHP2. apply prop_ext. symmetry. auto.
  - intros. do 2 rewrite aexpv_subst_equiv. easy.
  - intros. do 2 rewrite aexpv_subst_equiv. easy.
  - intros. do 2 rewrite aexpv_subst_equiv. easy.
  - split. 
    + intros. 
      eapply IHP.
      apply H0. 
    + intros.
      eapply IHP.
      apply H0.
  - intros. split.
    + intros (?&?).
      exists x0.
      eapply IHP.
      apply H0.
    + intros (?&?).
      exists x0.
      eapply IHP.
      apply H0. 
Qed.

Lemma assrt_isubst_equiv m I i n P H :
  sat m I (assrt_isubst i (AvVal n) H P) <-> sat m (iupd I i n) P.
Proof using.
  generalize dependent n. 
  generalize dependent I. 
  induction P; simpls; auto; try easy.
  - intros. rewrite IHP. easy.
  - intros. rewrite IHP1, IHP2. easy.
  - intros. rewrite IHP1, IHP2. easy.
  - intros. rewrite IHP1, IHP2. easy.
  - intros. split. 
    + intros. 
      specializes IHP1 n. 
      specialize IHP1 with H. 
      rewrite H0 in IHP1. 
      specializes IHP2 n.
      specialize IHP2 with H.
      rewrite IHP1 in IHP2. apply prop_ext. auto.
    + intros. 
      specializes IHP1 n. 
      specialize IHP1 with H. 
      rewrite H0 in IHP1. 
      specializes IHP2 n.
      specialize IHP2 with H.
      rewrite <- IHP1 in IHP2. apply prop_ext. symmetry. auto.
  - intros. do 2 rewrite aexpv_isubst_equiv. easy.
  - intros. do 2 rewrite aexpv_isubst_equiv. easy.
  - intros. do 2 rewrite aexpv_isubst_equiv. easy.
  - intros. split.
    + intros. case_if.
      * subst.
        rewrite iupd_shadow1.
        apply H0.
      * rewrite iupd_swap_diff; auto.
        eapply IHP.
        apply H0.
    + intros. case_if.
      * subst.
        erewrite <- iupd_shadow1.
        apply H0.
      * eapply IHP.
        rewrite iupd_swap_diff; auto.
  - intros. split.
    + intros (?&?). case_if.
      * subst.
        exists x.
        now rewrite iupd_shadow1.
      * exists x.
        rewrite iupd_swap_diff; auto.
        eapply IHP.
        apply H0.
    + intros (?&?). case_if.
      * subst. 
        exists x. 
        now rewrite iupd_shadow1 in H0.
      * exists x.
        eapply IHP.
        rewrite iupd_swap_diff; auto.
Qed.

End Assertions.

Section Interp.


Definition interp (P : bexp) : [mem] :=
  fun m => beval m P.

Notation "'[[' P ']]'" := (interp P).


Lemma interp_and (P Q : bexp) :
  [[BAnd P Q]] = [[P]] ∩ [[Q]].
Proof using.
  unfolds. extensionality m.
  simpls. unfolds subset_and.
  apply istrue_and_eq.
Qed.

Lemma interp_or (P Q : bexp) :
  [[BOr P Q]] = [[P]] ∪ [[Q]].
Proof using.
  extensionality m.
  unfolds. simpls.
  unfolds subset_or.
  apply istrue_or_eq.
Qed.

Lemma interp_true :
  [[BVal true]] = ⬤.
Proof using.
  unfolds. extensionality m.
  simpls. rewrite istrue_true_eq.
  symmetry. apply univ_set_true.
Qed.

Lemma interp_false :
  [[BVal false]] = ∅.
Proof using.
  unfolds. extensionality m.
  simpls. rewrite istrue_false_eq.
  symmetry. apply emptyset_false.
Qed.

Lemma interp_not P :
  [[BNot P]] = not ∘ [[P]].
Proof using.
  unfolds. extensionality m.
  simpls. now rewrite istrue_neg_eq.
Qed.

Lemma interp_imp (P Q : bexp) :
  [[BImp P Q]] = not ∘ [[P]] ∪ [[Q]].
Proof using.
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
Proof using.
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
Proof using.
  splits; intros; subst~.
  symmetry. rewrite~ prop_eq_True_eq.
Qed.


Lemma valid_and (P Q : bexp) :
  ⊨ BAnd P Q <-> (⊨ P /\ ⊨ Q).
Proof using.
  unfolds valid. splits; intros.
  - apply forall_conj_inv_1. intros.
    specializes H x1. simpls.
    now rewrite <- istrue_and_eq.
  - destruct H. specializes H m. specializes H0 m.
    simpls. rewrite istrue_and_eq. splits~.  
Qed.

Lemma valid_or (P Q : bexp) :
  (⊨ P \/ ⊨ Q) -> ⊨ BOr P Q.
Proof using.
  unfolds valid. intros. simpls.
  rewrite istrue_or_eq.
  destruct H; specializes H m.
  auto. auto.
Qed.

Lemma valid_imp (P Q : bexp) :
  [[P]] ⊆ [[Q]] <->
  ⊨ BImp P Q.
Proof using.
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


Local Definition c1 : cmd :=
  CAssn "x" (AMul (AVal 5) (AVal 10)).

Local Lemma ex1_eval m :
  yields c1 m (upd m "x" 50).
Proof.
  unfolds. exists.
  repeat econstructor.
Qed.

Notation "c1 ;; c2" := (CSeq c1 c2) (at level 39, right associativity).

Notation "x @@ z w" := (x (z w)) (at level 38, right associativity, only parsing).

Notation "# n" := (AVal n) (at level 5).

Local Definition c2 : cmd :=
  CAssn "x" #1 ;;
  CAssn "i" #3 ;;
  CWhile (BLt #0 (AVar "i"))
  (CAssn "x" (AMul (AVar "x") #2);;
   CAssn "i" (ASub (AVar "i") #1)).

Local Lemma ex2_eval m :
  yields c2 m (upd (upd m "x" 8) "i" 0).
Proof.
  econstructor.
  econstructor. econstructor. econstructor.
  simpls. econstructor.
  apply StepSeqSkip. econstructor.
  econstructor. econstructor.
  econstructor. apply StepSeqSkip.
  econstructor. econstructor.
  simpls. unfolds upd. case_if.
  constructor. simpls.
  econstructor. repeat econstructor.
  econstructor. econstructor.
  apply StepSeqSkip. econstructor.
  econstructor. econstructor.
  do 2 rewrite upd_shadow2.
  econstructor. apply StepSeqSkip.
  econstructor. econstructor.
  simpls. unfold upd. repeat case_if.
  constructor. simpls.
  rewrite upd_shadow1.
  do 2 (rewrite upd_read2; [|discriminate]).
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  apply StepSeqSkip. econstructor.
  econstructor. econstructor.
  simpls.
  do 2 (rewrite upd_read2; [|discriminate]).
  rewrite upd_shadow2. rewrite upd_shadow1.
  econstructor. apply StepSeqSkip.
  econstructor. econstructor.
  simpls. rewrite upd_read1. constructor.
  econstructor. econstructor.
  econstructor. econstructor.
  econstructor. econstructor.
  apply StepSeqSkip. econstructor.
  econstructor. econstructor.
  simpls. 
  do 2 (rewrite upd_read2; [|discriminate]).
  rewrite upd_shadow2.
  rewrite upd_shadow1.
  econstructor. apply StepSeqSkip.
  econstructor.
  apply StepWhileFalse.
  intro. inverts H.
  rewrite upd_read1 in H1.
  inverts H1.
  econstructor.
Qed.

End Example.