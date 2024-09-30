Set Implicit Arguments.

Import SigTNotations.

From Lang Require Import Util.

Open Scope fmap_scope.



Section Language.

Notation varid := string.


Definition mem := varid -> int.
Implicit Type m : mem.

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
  : cstep (CAssn x a) m CSkip (fun x' => If x = x' then aeval m a else m x')
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
  - symmetry. rewrite prop_eq_True_eq.


Lemma interp_impl (P Q : bexp) :
  let ebexp := is_bexp_imp (proj2_sig P) (proj2_sig Q) in
  [[exist _ _ ebexp]] =
  [[exist _ _ (is_bexp_or (is_bexp_neg (proj2_sig P)) (proj2_sig Q))]].
Proof using.
  simpls. destruct P as (P&BP), Q as (Q&BQ).
  simpls. unfold interp, evalbexp. simpls.
  extensionality m. specializes BP m. specializes BQ m.
  destruct evalexp eqn:E in BP; destruct evalexp eqn:F in BQ.
  all: try destruct v; try destruct v0; try easy.
  all: try rewrite E; try rewrite F; try easy.
  destruct b, b0; simpls; try easy.
Qed.


End Interp.


Notation "'[[' P ']]'" := (interp P).


Section Valid.


Definition valid (P : bexp) :=
  forall m,
  match evalbexp m P with
  | None => True
  | Some (VBool true) => True
  | _ => False
  end.

Notation "'⊨' P" := (valid P) (at level 50).


Lemma valid_support P :
  ⊨ P <->
  support (proj1_sig P) = [[P]].
Proof using.
  destruct P as (P&BP). simpls.
  unfolds valid, interp, support, evalbexp. simpls.
  splits; intros H. 
  extensionality m. apply prop_ext; splits; intros H'.
  - specializes H m. destruct~ evalexp. destruct~ v; try easy.
    destruct~ b. easy. easy.
  - specializes H m. now rewrite H' in *.
  - intro. apply equal_f with m in H.
    specializes BP m. destruct~ evalexp.
    destruct~ v. destruct~ b.
    apply eq_sym in H. now rewrite prop_eq_True_eq in H.
Qed.


Lemma true_eq H :
  True = H <-> H.
Proof using.
  splits; intros; subst~.
  symmetry. rewrite~ prop_eq_True_eq.
Qed.


Lemma valid_and (P Q : bexp) :
  ⊨ P /\ ⊨ Q ->
  ⊨ exist _ _ (is_bexp_and (proj2_sig P) (proj2_sig Q)).
Proof using.
  repeat rewrite valid_support.
  simpls. rewrite <- interp_and.
  destruct P as (P&BP), Q as (Q&BQ). simpls.
  intros (?&?).
  extensionality m.
  unfolds support, interp, evalbexp. simpls.
  specializes BP m. specializes BQ m.
  apply equal_f with m in H, H0.
  destruct (evalexp _ P) eqn:E;
  destruct (evalexp _ Q) eqn:F.
  - destruct v, v0; try easy.
    simpls. unfold subset_and.
    rewrite E, F, true_eq in *.
    inverts H. inverts H0. auto.
  - destruct v; try easy.
    unfold subset_and.
    rewrite E, F in *.
    apply prop_ext; splits; intros; try easy.
  - destruct v; try easy.
    unfold subset_and.
    rewrite E, F in *.
    apply prop_ext; splits; intros; try easy.
  - unfold subset_and.
    rewrite E, F in *.
    apply prop_ext; splits; intros; try easy.
Qed.


Lemma valid_imp (P Q : bexp) :
  [[P]] ⊆ [[Q]] ->
  ⊨ exist _ _ (is_bexp_imp (proj2_sig P) (proj2_sig Q)).
Proof using.
  destruct P as (P&BP), Q as (Q&BQ). simpls.
  rewrite valid_support. simpls.
  unfolds support, interp, evalbexp. simpls.
  intros H. extensionality m.
  specializes BP m. specializes BQ m. specializes H m.
  destruct (evalexp m P) eqn:E. destruct v; try easy.
  simpls. destruct (evalexp m Q) eqn:F.
  destruct v; try easy.
  apply true_eq. destruct b; try easy.
  destruct~ H. destruct b; try easy.
  destruct~ H.
Abort.


End Valid.