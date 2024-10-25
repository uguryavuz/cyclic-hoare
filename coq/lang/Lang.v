Set Implicit Arguments.
Import SigTNotations.
Require Import Init.Wf Arith.
From Lang Require Import Util.

Open Scope fmap_scope.

Definition varid := string.
Definition mem := tmap varid int.

Implicit Type m : mem.
Implicit Type n : int.

Section Language.

Inductive aexp :=
  | AVal (n : int)
  | AVar (x : varid)
  | ANeg (a : aexp)
  | AAdd (a1 a2 : aexp)
  | ASub (a1 a2 : aexp)
  | AMul (a1 a2 : aexp).

Inductive bexp :=
  | BVal (b : bool)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
  | BOr  (b1 b2 : bexp)
  | BImp (b1 b2 : bexp)
  | BEqB (b1 b2 : bexp)
  | BEqA (a1 a2 : aexp)
  | BLt  (a1 a2 : aexp)
  | BLeq (a1 a2 : aexp).

Inductive cmd :=
  | CSkip
  | CSeq (c : cmd) (c : cmd)
  | CIf (e : bexp) (c1 c2 : cmd)
  | CAssn (x : varid) (e : aexp)
  | CWhile (e : bexp) (c : cmd).

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
  | StepSeq :
      forall m m' c1 c1' c2 (H1 : cstep c1 m c1' m'),
        cstep (CSeq c1 c2) m (CSeq c1' c2) m'
  | StepSeqSkip : forall m c, cstep (CSeq CSkip c) m c m
  | StepIfTrue : forall m b c1 c2 (Hg : beval m b), cstep (CIf b c1 c2) m c1 m
  | StepIfFalse :
      forall m b c1 c2 (Hg : ~ beval m b), cstep (CIf b c1 c2) m c2 m
  | StepWhileTrue :
      forall m b c (Hg : beval m b),
        cstep (CWhile b c) m (CSeq c (CWhile b c)) m
  | StepWhileFalse :
      forall m b c (Hg : ~ beval m b), cstep (CWhile b c) m CSkip m
  | StepAssn m x a : cstep (CAssn x a) m CSkip (m[x=(aeval m a)]).

Ltac cstep_skip :=
  match goal with
  | [ H : cstep CSkip _ _ _ |- _ ] => inverts H
  end.

Lemma cstep_skip :
  forall m c' m',
    cstep CSkip m c' m' -> False.
Proof.
  introv H.
  cstep_skip.
Qed.

Hint Resolve cstep_skip : core.

Inductive multistep : cmd -> mem -> cmd -> mem -> nat -> Prop :=
  | Multi0 c m : multistep c m c m O
  | MultiI c c' c'' m m' m'' (n:nat) (H : cstep c m c' m') (H' : multistep c' m' c'' m'' n) : 
      multistep c m c'' m'' (S n).

Definition yields c m m' :=
  exists n, multistep c m CSkip m' n.

Definition terminates c m := 
  exists m', yields c m m'.

Definition diverges c m :=
  ~ terminates c m.

Lemma cstep_to_multistep : 
  forall c m c' m',
    cstep c m c' m' <-> multistep c m c' m' 1.
Proof.
  split.
  intro H.
  econstructor.
  apply H.
  constructor.
  intro H.
  inverts H.
  inverts H'.
  easy.
Qed.

Lemma deterministic_cstep :
  forall c c1 c2 m m1 m2,
    cstep c m c1 m1 ->
    cstep c m c2 m2 ->
    c1 = c2 /\ m1 = m2.
Proof.
  induction c.
  + intros. cstep_skip.
  + intros. 
    inverts H.
    inverts H0.
    * specializes IHc1 H6 H7. destruct IHc1. subst. easy.
    * cstep_skip.
    * inverts H0. cstep_skip. easy.
  + intros.
    inverts H; inverts H0; try auto; contradiction.
  + intros.
    inverts H; inverts H0; easy.
  + intros.
    inverts H; inverts H0; try auto; contradiction.
Qed.

Lemma determinism_in_n_multistep : 
  forall (n:nat) c c1 c2 m m1 m2,
    multistep c m c1 m1 n ->
    multistep c m c2 m2 n ->
    c1 = c2 /\ m1 = m2.
Proof.
  induction n.
  - intros. inverts H. inverts H0. easy.
  - intros. inverts H. inverts H0.
    pose proof deterministic_cstep H5 H6.
    destruct H. subst.
    specializes IHn H' H'0.
Qed.

Lemma determinism_in_multistep_termination :
  forall (n1 n2 : nat) c m m1 m2,
    multistep c m CSkip m1 n1 ->
    multistep c m CSkip m2 n2 ->
    m1 = m2 /\ n1 = n2.
Proof.
  induction n1.
  { introv H1 H2. inverts H1. inverts~ H2. cstep_skip. }
  introv H1 H2.
  inverts H1.
  inverts H2.
  cstep_skip.
  pose proof deterministic_cstep H H6.
  destruct H0. subst. clean.
  specializes IHn1 H' H'0.
Qed.

Lemma determinism_in_yielding :
  forall c m m1 m2,
    yields c m m1 ->
    yields c m m2 ->
    m1 = m2.
Proof.
  introv H1 H2.
  destruct H1 as [n1 H1].
  destruct H2 as [n2 H2].
  pose proof determinism_in_multistep_termination H1 H2.
  destruct H. auto.
Qed.

Lemma seq_intermediate_multistep :
  forall (n:nat) c1 c2 m m'',
    multistep (CSeq c1 c2) m CSkip m'' n ->
    exists n1 n2 m',
      multistep c1 m CSkip m' n1 /\ 
      multistep c2 m' CSkip m'' n2 /\ 
      S (n1 + n2) = n.
Proof.
  induction n.
  { introv H. inverts H. }
  introv H.
  inverts H.
  inverts H5; sort.
  + specializes IHn H'. 
    exists* IHn. 
    exists (S n1) n2 m'0.
    splits~.
    econstructor.
    apply H6.
    trivial.
  + exists.
    splits.
    constructor.
    apply H'.
    math.
Qed.

Lemma seq_intermediate_yields c1 c2 m m'' :
  yields (CSeq c1 c2) m m'' ->
  exists m',
  yields c1 m m' /\
  yields c2 m' m''.
Proof.
  intros.
  destruct H as [n H].
  pose proof seq_intermediate_multistep H.
  exists* H0.
  exists m'.
  split. 
  exists~ n1. 
  exists~ n2.
Qed.

Lemma while_multistep_termination :
  forall (n : nat) (b : bexp) c m m',
    multistep (CWhile b c) m CSkip m' n
      -> ~ beval m' b.
Proof.
  induction n using (well_founded_induction lt_wf).
  introv H1.
  inverts H1.
  inverts H0. 2 : {inverts~ H'. cstep_skip. }
  apply seq_intermediate_multistep in H'.
  exists* H'.
  apply H in H'0.
  trivial.
  math.
Qed.

End Language.

Ltac cstep_skip :=
  match goal with
  | [ H : cstep CSkip _ _ _ |- _ ] => inverts H
  end.

Lemma eq_emptyset {T} (X : [T]) :
  X = ∅ <-> ~ exists x, X x.
Proof.
  splits; intros.
  subst. intro. now exists* H.
  contra H. now apply not_emptyset in H.
Admitted.

Ltac empty_inhab_false :=
  match goal with
  | [ H : ∅ _ |- _ ] => 
    rewrite emptyset_false in H; contradiction
  end.

Definition ivarid := string.
Inductive ivar : Type :=
  | IVar (i : ivarid).

Definition binding := tmap ivar int.

Implicit Type I : binding.
Implicit Type c : cmd.

Declare Scope assrt_scope.

Section Assertions.

Inductive aexpv :=
  | AvVal (n : int)
  | AvVar (x : varid)
  | AvNeg (a : aexpv)
  | AvAdd (a1 a2 : aexpv)
  | AvSub (a1 a2 : aexpv)
  | AvMul (a1 a2 : aexpv)
  | AvIVar (i : ivar).

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

Fixpoint aexp_to_aexpv a : aexpv :=
  match a with
  | AVal n => AvVal n
  | AVar x => AvVar x
  | ANeg a => AvNeg (aexp_to_aexpv a)
  | AAdd a1 a2 => AvAdd (aexp_to_aexpv a1) (aexp_to_aexpv a2)
  | ASub a1 a2 => AvSub (aexp_to_aexpv a1) (aexp_to_aexpv a2)
  | AMul a1 a2 => AvMul (aexp_to_aexpv a1) (aexp_to_aexpv a2)
  end.

Coercion aexp_to_aexpv : aexp >-> aexpv.

Lemma aexp_aexpv_equiv m I (a : aexp) :
  aveval m I a = aeval m a.
Proof.
  induction a; simpls; f_equal~.
Qed.

Inductive assrt :=
  | AssrtVal (b : bool)
  | AssrtNot (b : assrt)
  | AssrtAnd (b1 b2 : assrt)
  | AssrtOr  (b1 b2 : assrt)
  | AssrtImp (b1 b2 : assrt)
  | AssrtEqB (b1 b2 : assrt)
  | AssrtEqA (a1 a2 : aexpv)
  | AssrtLt  (a1 a2 : aexpv)
  | AssrtLeq (a1 a2 : aexpv)
  | AssrtForall (i : ivar) (b : assrt)
  | AssrtExists (i : ivar) (b : assrt).

Implicit Type P Q : assrt.

Coercion AssrtVal : bool >-> assrt.

Delimit Scope assrt_scope with A.

Infix "/\" := AssrtAnd : assrt_scope.
Infix "\/" := AssrtOr : assrt_scope.
Infix "->" := AssrtImp : assrt_scope.
Infix "<" := AssrtLt : assrt_scope.
Infix "<=" := AssrtLeq : assrt_scope.
Notation "~" := AssrtNot : assrt_scope.

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
  | AssrtForall i P => forall n, sat m (I[i=n]) P
  | AssrtExists i P => exists n, sat m (I[i=n]) P
  end.

Notation "m ',' I '|=' P" := (sat m I P) (at level 50).

Definition valid_assrt P :=
  forall m I, m, I |= P.

Notation "'|=' P" := (valid_assrt P%A) (at level 50).

Fixpoint bexp_to_assrt b : assrt :=
  match b with
  | BVal b => AssrtVal b
  | BNot b => AssrtNot (bexp_to_assrt b)
  | BAnd b1 b2 => (bexp_to_assrt b1 /\ bexp_to_assrt b2)%A
  | BOr  b1 b2 => (bexp_to_assrt b1 \/ bexp_to_assrt b2)%A
  | BImp b1 b2 => (bexp_to_assrt b1 -> bexp_to_assrt b2)%A
  | BEqB b1 b2 => AssrtEqB (bexp_to_assrt b1) (bexp_to_assrt b2)
  | BEqA a1 a2 => AssrtEqA a1 a2
  | BLt  a1 a2 => (a1 < a2)%A
  | BLeq a1 a2 => (a1 <= a2)%A
  end.

Coercion bexp_to_assrt : bexp >-> assrt.

Lemma bexp_assrt_equiv m I (b : bexp) :
  m,I |= b <-> beval m b.
Proof.
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
  ~ has_ivars a.
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
  fix rec (P : assrt) : assrt :=
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

Coercion AvVal : Z >-> aexpv.

Lemma aexpv_subst_equiv m I x a n : 
  aveval m I (aexpv_subst x n a) = aveval (m[x=n]) I a.
Proof.
  induction a; simpls; auto; try math.
  + case_if; simpls.
    * subst. rewrite upd_read1. trivial.
    * unfold upd. case_if. trivial.
Qed.

Lemma aexpv_isubst_equiv m I i a n : 
  aveval m I (aexpv_isubst i n a) = aveval m (I[i=n]) a.
Proof.
  induction a; simpls; auto; try math.
  + case_if; simpls.
    * subst. rewrite upd_read1. trivial.
    * unfold upd. case_if. trivial.
Qed.

Lemma assrt_subst_equiv m I x n P H :
  m,I |= assrt_subst x n H P <-> m[x=n],I |= P.
Proof.
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
  m,I |= assrt_isubst i n H P <-> m,I[i=n] |= P.
Proof.
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
        rewrite upd_shadow1.
        apply H0.
      * rewrite upd_swap_diff; auto.
        eapply IHP.
        apply H0.
    + intros. case_if.
      * subst.
        erewrite <- upd_shadow1.
        apply H0.
      * eapply IHP.
        rewrite upd_swap_diff; auto.
  - intros. split.
    + intros (?&?). case_if.
      * subst.
        exists x.
        now rewrite upd_shadow1.
      * exists x.
        rewrite upd_swap_diff; auto.
        eapply IHP.
        apply H0.
    + intros (?&?). case_if.
      * subst. 
        exists x. 
        now rewrite upd_shadow1 in H0.
      * exists x.
        eapply IHP.
        rewrite upd_swap_diff; auto.
Qed.

(* Winskel Ex6.6 *)
Corollary assrt_isubst_forall_equiv m I i P :
  m,I |= AssrtForall i P <->
  forall (n:int) H, m,I |= assrt_isubst i n H P.
Proof.
  simpls. split; intros.
  - apply assrt_isubst_equiv. apply H.
  - specializes H n. specializes~ H.
    apply assrt_isubst_equiv in H.
    apply H. Unshelve. auto.
Qed.

(* Winskel Ex6.6 *)
Corollary assrt_isubst_exists_equiv m I i P :
  m,I |= AssrtExists i P <->
  exists (n:int) H, m,I |= assrt_isubst i n H P.
Proof.
  simpls. splits; intros.
  - destruct H. rewrite <- assrt_isubst_equiv in H.
    exists x. exists. apply H.
    Unshelve. auto.
  - exists* H. apply assrt_isubst_equiv in H.
    exists. apply H.
Qed.


Lemma aexpv_subst_compat b :
  forall m I x a a',
  aeval m a = aeval m a' ->
  aveval m I (aexpv_subst x a b) =
  aveval m I (aexpv_subst x a' b).
Proof.
  induction b; simpls; intros; try easy.
  - case_if~. subst.
    do 2 rewrite aexp_aexpv_equiv. auto.
  - f_equal. now apply IHb.
  - rewrite IHb1 with (a':=a').
    rewrite IHb2 with (a':=a'). all: auto.
  - rewrite IHb1 with (a':=a').
    rewrite IHb2 with (a':=a'). all: auto.
  - rewrite IHb1 with (a':=a').
    rewrite IHb2 with (a':=a'). all: auto.
Qed.


Notation "P '[' a '/' x ']'" := 
  (assrt_subst x _ (aexp_no_ivars a) P)
  (at level 10, a at level 5).


Lemma assrt_subst_compat P :
  forall m I x a b,
  aeval m a = aeval m b ->
  (m,I |= P[a/x] <->
  m,I |= P[b/x]).
Proof.
  induction P; simpls; intros.
  - easy.
  - rewrite iff_not_not_eq. apply~ IHP.
  - split; intros (?&?).
    + split. rewrite IHP1.
      apply H0. auto.
      rewrite IHP2.
      apply H1. auto.
    + split. rewrite IHP1.
      apply H0. auto.
      rewrite IHP2. apply H1. auto.
  - split; intros.
    + destruct H0.
      left. rewrite IHP1.
      apply H0. auto.
      right. rewrite IHP2.
      apply H0. auto.
    + destruct H0.
      left. rewrite IHP1.
      apply H0. auto.
      right. rewrite IHP2.
      apply H0. auto.
  - split; intros.
    + rewrite IHP2. apply H0.
      rewrite IHP1. apply H1. auto. auto.
    + rewrite IHP2. apply H0.
      rewrite IHP1. apply H1.
      all: auto.
  - split; intros.
    all: apply prop_ext; split; intros.
    + rewrite IHP2. rewrite <- H0.
      rewrite IHP1. apply H1. auto. auto.
    + rewrite IHP1. rewrite H0.
      rewrite IHP2. apply H1. auto. auto.
    + rewrite IHP2. rewrite <- H0.
      rewrite IHP1. apply H1. auto. auto.
    + rewrite IHP1. rewrite H0.
      rewrite IHP2. apply H1. auto. auto.
  - rewrite (aexpv_subst_compat _ _ _ _ a b).
    rewrite (aexpv_subst_compat _ _ _ _ a b).
    all: easy.
  - rewrite (aexpv_subst_compat _ _ _ _ a b).
    rewrite (aexpv_subst_compat _ _ _ _ a b).
    all: easy.
  - rewrite (aexpv_subst_compat _ _ _ _ a b).
    rewrite (aexpv_subst_compat _ _ _ _ a b).
    all: easy.
  - splits; intros; sort.
    + rewrite IHP. apply H0. auto.
    + rewrite IHP. apply H0. auto.
  - splits; intros; sort.
    + destruct H0. exists x0.
      rewrite IHP. apply H0. auto.
    + destruct H0. exists x0.
      rewrite IHP. apply H0. auto.
Qed.


Lemma val_no_ivars (n:int) :
  ~ has_ivars n.
Proof. auto. Qed.


Corollary subst_val P :
  forall m I x a,
  m,I |= P[a/x] <->
  m,I |= assrt_subst x _ (@val_no_ivars (aeval m a)) P.
Proof.
  intros.
  pose proof assrt_subst_compat P m I x a (AVal (aeval m a)).
  auto.
Qed.


End Assertions.


Notation "P '[' a '/' x ']'" := 
  (assrt_subst x _ (aexp_no_ivars a) P)
  (at level 10, a at level 5).


Delimit Scope assrt_scope with A.

Notation "m ',' I '|=' P" := (sat m I P%A) (at level 50).
Notation "'|=' P" := (valid_assrt P%A) (at level 50).

(*Notation "P /\ Q" := (AssrtAnd P Q) (only parsing) : assrt_scope.*)

Infix "/\" := AssrtAnd : assrt_scope.
Infix "\/" := AssrtOr : assrt_scope.
Infix "->" := AssrtImp : assrt_scope.
Infix "<" := AssrtLt : assrt_scope.
Infix "<=" := AssrtLeq : assrt_scope.
Notation "'~' P" := (AssrtNot P) (at level 75, right associativity) : assrt_scope.

Notation "'For' i '.' P" :=
  (AssrtForall i P)
  (at level 200, right associativity, only parsing) : assrt_scope.

Notation "'Ex' i '.' P" :=
  (AssrtExists i P)
  (at level 200, right associativity, only parsing) : assrt_scope.


Section SatRules.

Lemma sat_true m I :
  m,I |= true.
Proof.
  easy.
Qed.

Lemma sat_neg m I P :
  ~ (m,I |= P) <-> m,I |= ~ P.
Proof.
  now simpls.
Qed.

Lemma sat_and m I P1 P2 :
  (m,I |= P1 /\ m,I |= P2) <-> m,I |= (P1 /\ P2).
Proof.
  simpls. split; auto.
Qed.

Lemma sat_or m I P1 P2 :
  (m,I |= P1 \/ m,I |= P2) <-> m,I |= (P1 \/ P2).
Proof.
  simpls. split; intros; auto.
Qed.

Lemma sat_imp m I P1 P2 :
  (m,I |= P1 -> m,I |= P2) <-> m,I |= (P1 -> P2).
Proof.
  simpls. split; intros; auto.
Qed.

Lemma sat_forall m i I P :
  (forall n, m, I[i=n] |= P) <->
  m,I |= (For i. P).
Proof.
  simpls. split; intros; auto.
Qed.

Lemma sat_exists m i I P :
  (exists n, m, I[i=n] |= P) <-> m,I |= Ex i. P.
Proof.
  simpls. 
  split. trivial. trivial.
Qed.

Lemma sat_eqa m I a1 a2 :
  (aveval m I a1 = aveval m I a2) <-> m,I |= AssrtEqA a1 a2.
Proof.
  simpls. split; auto.
Qed.

Lemma sat_eqb m I P Q :
  (m,I |= P <-> m,I |= Q) <-> m,I |= AssrtEqB P Q.
Proof.
  simpls. split; auto. apply prop_ext. intros. rewrite H. easy.
Qed.

Lemma sat_lt m I (a1 a2 : aexpv) :
  lt (aveval m I a1) (aveval m I a2) <-> m,I |= (a1 < a2).
Proof.
  simpls. split; auto.
Qed.

Lemma sat_leq m I a1 a2 :
  le (aveval m I a1) (aveval m I a2) <-> m,I |= (a1 <= a2).
Proof.
  simpls. split; auto.
Qed.

End SatRules.

Section ValidRules.

Lemma valid_ex_falso Q :
  |= (false -> Q).
Proof.
  introv. now simpls.
Qed.

Lemma valid_imp_refl P :
  |= (P -> P).
Proof.
  introv. easy.
Qed.

Lemma valid_imp_and_l P Q R :
  |= (P -> R) ->
  |= (P /\ Q -> R).
Proof.
  introv ??.
  specializes H m I.
  simpls. now apply H.
Qed.

End ValidRules.


Section Triples.

Definition triple m I c P Q :=
  m,I |= P ->
  forall m', yields c m m' ->
  m',I |= Q.

Definition valid_triple c P Q :=
  forall m I, triple m I c P Q.

Notation "'||=' c ':' P '=>' Q" := (valid_triple c P%A Q%A)
  (at level 50, c at next level, no associativity).

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

End Triples.

Notation "'|-' c ':' P '=>' Q" := (derivable_triple c P%A Q%A)
  (at level 50, c at next level, no associativity).

Notation "'||=' c ':' P '=>' Q" := (valid_triple c P%A Q%A)
  (at level 50, c at next level, no associativity).

Section Soundness.

Lemma csq_sound c P Q P' Q' 
  (H1 : |= (P -> P'))
  (H2 : ||= c : P' => Q') 
  (H3 : |= (Q' -> Q)) 
  : ||= c : P => Q.
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
  (H1 : ||= c : P /\ P' => Q) 
  (H2 : ||= c : P /\ ~ P' => Q) 
  : ||= c : P => Q.
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

Lemma skip_sound P : ||= CSkip : P => P.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros. unfolds yields.
  destruct H0.
  inverts~ H0.
  cstep_skip.
Qed.

Lemma assn_sound x a P : 
  ||= CAssn x a : P[a/x] => P.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros. unfolds in H0.
  exists* H0. sort.
  inverts H0. inverts H1.
  inverts H'. 2: cstep_skip.
  assert (~ has_ivars (aeval m a)) as IV; auto.
  apply assrt_subst_equiv with IV.
  simpls. now apply subst_val.
Qed.

Lemma seq_sound c c' P Q R :
  ||= c : P => Q ->
  ||= c' : Q => R ->
  ||= CSeq c c' : P => R.
Proof.
  unfolds valid_triple, triple, valid_assrt.
  intros.
  apply seq_intermediate_yields in H2.
  destruct H2 as (m'' & H2 & H3).
  specializes H m I.
Qed.

Lemma if_true_sound (b:bexp) c c' P Q :
  ||= c : P /\ b => Q ->
  ||= CIf b c c' : P /\ b => Q.
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
  ||= c' : P /\ ~ b => Q ->
  ||= CIf b c c' : P /\ ~ b => Q.
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
  ||= CSeq c (CWhile b c) : P /\ b => Q ->
  ||= CWhile b c : P /\ b => (Q /\ ~ b).
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
  ||= CWhile b c : P /\ ~ b => (P /\ ~ b).
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

Lemma soundness c P Q :
  |- c : P => Q -> ||= c : P => Q.
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

End DerivedRules.

Section Example.

Local Definition c1 : cmd :=
  CAssn "x" (AMul (AVal 5) (AVal 10)).

Local Lemma ex1_eval m :
  yields c1 m (m["x"=50]).
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
  yields c2 m (m["x"=8]["i"=0]).
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
