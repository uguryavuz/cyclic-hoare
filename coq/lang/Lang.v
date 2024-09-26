Set Implicit Arguments.

Import SigTNotations.

From Lang Require Import Util.

Open Scope fmap_scope.


Section Language.

Notation varid := string.

Inductive val :=
| VInt (n:int)
| VBool (b:bool)
.

Inductive vval :=
| VId (x:varid)
| VVal (v:val)
.

Definition mem := fmap varid val.
Implicit Type m : mem.

Global Instance Inhab_mem : Inhab val.
Proof. constructor. exists~ (VInt 0). Qed.


Definition getval m (vv:vval) : val :=
  match vv with
  | VId x => read m x
  | VVal v => v
  end.

Definition inmem (m:mem) (vv:vval) : Prop :=
  match vv with
  | VId x => indom m x
  | VVal _ => True
  end.

(*Inductive instr :=
| EWrite (x : varid) (e : exp)
| EBop (x : varid) (vv1 vv2 : vval) (op : lit -> lit -> lit)
.*)

Inductive uop :=
| UNot | UNeg
.

Inductive bop :=
| BAnd | BOr | BEq | BImp
| BLeq | BLt | BAdd | BSub
.

Inductive exp :=
| EVar (x:varid)
| EVal (v:val)
| EUop (op : uop) (e:exp)
| EBop (op : bop) (e1 e2 : exp)
.

Inductive cmd :=
| CSkip
| CSeq (c : cmd) (c : cmd)
| CIf (e : exp) (c1 c2 : cmd)
| CAssn (x : varid) (e : exp)
| CWhile (e : exp) (c : cmd)
.

Inductive res :=
| Good (m:mem)
| Bot.


Definition evaluop op v : option val :=
match op, v with
| UNot, VInt n => Some (VInt (-n))
| UNeg, VBool b => Some (VBool (negb b))
| _, _ => None
end.


Definition evalbop op v1 v2 : option val :=
match v1, v2 with
| VBool b1, VBool b2 =>
  match op with
  | BAnd => Some (VBool (b1 && b2))
  | BOr => Some (VBool (b1 || b2))
  | BEq => Some (VBool (Bool.eqb b1 b2))
  | BImp => Some (VBool (implb b1 b2))
  | _ => None
  end
| VInt n1, VInt n2 =>
  match op with
  | BEq => Some (VBool (Z.eqb n1 n2))
  | BLeq => Some (VBool (Z.leb n1 n2))
  | BLt => Some (VBool (Z.ltb n1 n2))
  | BAdd => Some (VInt (n1 + n2))
  | BSub => Some (VInt (n1 - n2))
  | _ => None
  end
| _, _ => None
end.


Fixpoint evalexp (m:mem) (e:exp) : option val :=
match e with
| EVar x => If indom m x then Some (read m x) else None
| EVal v => Some v
| EUop op e =>
  match evalexp m e with
  | Some v => evaluop op v
  | None => None
  end
| EBop op e1 e2 =>
  match evalexp m e1, evalexp m e2 with
  | Some v1, Some v2 => evalbop op v1 v2
  | _, _ => None
  end
end.

Inductive evalcmd (m:mem) : cmd -> mem -> Prop :=
| EvalSkip : evalcmd m CSkip m
| EvalSeq m' m'' c1 c2
  (H1 : evalcmd m c1 m')
  (H2 : evalcmd m' c2 m'')
  : evalcmd m (CSeq c1 c2) m''
| EvalIfTrue m' e c1 c2
  (Hg : evalexp m e = Some (VBool true))
  (Hc : evalcmd m c1 m')
  : evalcmd m (CIf e c1 c2) m'
| EvalIfFalse m' e c1 c2
  (Hg : evalexp m e = Some (VBool false))
  (Hc : evalcmd m c2 m')
  : evalcmd m (CIf e c1 c2) m'
| EvalWhileTrue m' e c
  (Hg : evalexp m e = Some (VBool true))
  (Hc : evalcmd m (CSeq c (CWhile e c)) m')
  : evalcmd m (CWhile e c) m'
| EvalWhileFalse e c
  (Hg : evalexp m e = Some (VBool false))
  : evalcmd m (CWhile e c) m
| EvalAssn x e v
  (He : evalexp m e = Some v)
  : evalcmd m (CAssn x e) (update m x v)
.

(*
  Fixpoint seqN (n:nat) c :=
    match n with O => CSkip
    | S n => CSeq c (seqN n c)
    end.

  Lemma while_iter e c :
    forall m m',
    evalcmd m (CWhile e c) m' ->
    exists n,
    evalcmd m (seqN n c) m'.
  Proof using.
  Abort.


  Example ex_loop x m n :
    indom m x ->
    read m x = VInt (Z_of_nat n) ->
    n >= O ->
    evalcmd m
      (CWhile (EBop BLt (EInt 0) (EVar x)) 
              (CAssn x (EBop BSub (EVar x) (EInt 1)))) 
      (update m x (VInt 0)).
  Proof using.
    generalize dependent m.
    intros.
    induction n as [| ? | ?]; [admit|idtac|idtac].

    induction n; intros; sort.
    - replace (update _ _ _) with m.
      applys EvalWhileFalse. admit.
      simpl_fmap. admit.
    - 
  *)


  (*
  Lemma eval_uniq c :
    forall m m1 m2,
    evalcmd m c m1 ->
    evalcmd m c m2 ->
    m1 = m2.
  Proof using.
    destruct c.
    -
    Guarded.
    cofix K.
    intros. cofix c. cofix H H0.
    induction c; introv H1 H2.
    - inverts H1. inverts~ H2.
    - inverts H1. inverts H2.
      specializes IHc1 H4 H5. subst.
      specializes IHc2 H6 H7.
    - inverts H1; inverts H2.
      + specializes IHc1 Hc Hc0.
      + rewrite Hg in Hg0. inverts Hg0.
      + rewrite Hg in Hg0. inverts Hg0.
      + specializes IHc2 Hc Hc0.
    - inverts H1. inverts H2.
      rewrite He in He0. inverts~ He0.
    - inverts H1; inverts~ H2.
      2, 3: now rewrite Hg in Hg0.
    *)



End Language.



Lemma eq_emptyset {T} (X : [T]) :
  X = ∅ <-> ~ exists x, X x.
Proof using.
  splits; intros.
  subst. intro. now exists* H.
  contra H. now apply not_emptyset in H.
Qed.


Notation memp := (empty:mem).



Ltac empty_inhab_false :=
  match goal with
  | [ H : ∅ _ |- _ ] => 
    rewrite emptyset_false in H; contradiction
  end.


Section BoolExp.


Definition support e m :=
  match evalexp m e with
  | Some _ => True
  | _ => False
  end.


Definition is_bexp e :=
  forall m,
  match evalexp m e with
  | None => True
  | Some (VBool _) => True
  | _ => False
  end.

Definition bexp := { e | is_bexp e }.

Definition evalbexp m (P : bexp) :=
  evalexp m (proj1_sig P).


Definition is_bexp_bop op :=
  forall P Q,
  is_bexp P ->
  is_bexp Q ->
  is_bexp (EBop op P Q).

Lemma is_bexp_and :
  is_bexp_bop BAnd.
Proof using.
  intros P Q HP HQ m.
  specializes HP m.
  specializes HQ m. simpls.
  destruct~ (evalexp m P).
  destruct~ (evalexp m Q).
  destruct~ v; now destruct~ v0.
Qed.

Lemma is_bexp_or :
  is_bexp_bop BOr.
Proof using.
  intros P Q HP HQ m.
  specializes HP m.
  specializes HQ m. simpls.
  destruct~ (evalexp m P).
  destruct~ (evalexp m Q).
  destruct~ v; now destruct~ v0.
Qed.

Lemma is_bexp_eq :
  is_bexp_bop BEq.
Proof using.
  intros P Q HP HQ m.
  specializes HP m.
  specializes HQ m. simpls.
  destruct~ (evalexp m P).
  destruct~ (evalexp m Q).
  destruct~ v; now destruct~ v0.
Qed.

Lemma is_bexp_imp :
  is_bexp_bop BImp.
Proof using.
  intros P Q HP HQ m.
  specializes HP m.
  specializes HQ m. simpls.
  destruct~ (evalexp m P).
  destruct~ (evalexp m Q).
  destruct~ v; now destruct~ v0.
Qed.

Lemma is_bexp_val b :
  is_bexp (EVal (VBool b)).
Proof using.
  unfolds. simpls~.
Qed.


Lemma is_bexp_neg :
  forall P,
  is_bexp P ->
  is_bexp (EUop UNeg P).
Proof using.
  intros ? ? ?. specializes H m.
  simpls. destruct~ evalexp.
  destruct~ v.
Qed.

End BoolExp.



Section Interp.


Definition interp (P : bexp) : [mem] :=
  fun m =>
  evalbexp m P = Some (VBool true).


Notation "'[[' P ']]'" := (interp P).


Lemma interp_and (P Q : bexp) :
  let ebexp := is_bexp_and (proj2_sig P) (proj2_sig Q) in
  [[P]] ∩ [[Q]] = [[exist _ _ ebexp]].
Proof using.
  simpls. destruct P as (P&BP), Q as (Q&BQ).
  simpls. extensionality m. apply prop_ext.
  unfolds interp, evalbexp, subset_and.
  simpls.
  specializes BP m. specializes BQ m.
  destruct evalexp. destruct v; try easy.
  all: destruct evalexp. all: try destruct v; try easy.
  destruct b, b0; simpls~; easy.
Qed.


Lemma interp_support P :
  [[P]] ⊆ support (proj1_sig P).
Proof using.
  introv H. inverts H.
  unfolds. destruct P as (P&BP).
  unfolds evalbexp. simpls.
  now rewrite H1.
Qed.


Lemma interp_or (P Q : bexp) :
  let ebexp := is_bexp_or (proj2_sig P) (proj2_sig Q) in
  ([[P]] ∪ [[Q]]) ∩ support (proj1_sig P) ∩ support (proj1_sig Q)
  = [[exist _ _ ebexp]].
Proof using.
  simpls. destruct P as (P&BP), Q as (Q&BQ).
  simpls. extensionality m. apply prop_ext.
  unfolds interp, evalbexp, subset_or, subset_and, support.
  simpls.
  specializes BP m. specializes BQ m.
  destruct evalexp eqn:E in BP; destruct evalexp eqn:F in BQ.
  all: rewrite E, F in *.
  all: try destruct v; try destruct v0; simpls; try easy.
  destruct b, b0; simpls. all: splits~.
  intros. destruct~ H. destruct~ H. destruct~ H.
Qed.


Lemma interp_true :
  let ebexp := is_bexp_val true in
  [[exist _ _ ebexp]] = ⬤.
Proof using.
  simpls. unfold interp, evalbexp, evalexp, univ_set.
  simpls. extensionality m. now apply prop_ext.
Qed.


Lemma interp_false :
  let ebexp := is_bexp_val false in
  [[exist _ _ ebexp]] = ∅.
Proof using.
  simpls. unfold interp, evalbexp, evalexp.
  apply eq_emptyset. intro. simpls. now exists* H.
Qed.


Lemma interp_not (P : bexp) :
  let ebexp := is_bexp_neg (proj2_sig P) in
  [[exist _ _ ebexp]] = 
  fun m => evalexp m (proj1_sig P) = Some (VBool false).
Proof using.
  simpls. unfold interp, evalbexp.
  destruct P as (P&BP). simpls.
  extensionality m. specializes BP m.
  destruct~ evalexp.
  2: { apply prop_ext; splits; intros; discriminate. }
  destruct~ v; try easy.
  destruct~ b; simpls~.
  apply prop_ext; splits; intros; discriminate.
  apply prop_ext; splits; auto.
Qed.


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