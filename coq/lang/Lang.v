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
| EInt (n:int)
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

Fixpoint evalexp (m:mem) (e:exp) : option val. Admitted.

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


Notation eempty := (empty:env).



Ltac empty_inhab_false :=
  match goal with
  | [ H : ∅ _ |- _ ] => 
    rewrite emptyset_false in H; contradiction
  end.
