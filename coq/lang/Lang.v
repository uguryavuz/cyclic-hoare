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