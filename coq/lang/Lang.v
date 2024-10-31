Set Implicit Arguments.
Require Import Init.Wf Arith.
From Lang Require Export Util.

Definition varid := string.
Definition mem := tmap varid int.

Implicit Type m : mem.
Implicit Type n : int.

Inductive aexp :=
  | AVal (n : int)
  | AVar (x : varid)
  | ANeg (a : aexp)
  | AAdd (a1 a2 : aexp)
  | ASub (a1 a2 : aexp)
  | AMul (a1 a2 : aexp).

Coercion AVal : Z >-> aexp.

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

Coercion BVal : bool >-> bexp.

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


Section OperationalProperties.

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

End OperationalProperties.