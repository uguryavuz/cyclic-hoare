Set Implicit Arguments.
From Lang Require Export Lang.

Implicit Type m : mem.
Implicit Type n : int.

Definition ivarid := string.
Inductive ivar : Type :=
  | IVar (i : ivarid).

Definition binding := tmap ivar int.

Implicit Type I : binding.
Implicit Type c : cmd.

Declare Scope assrt_scope.
Delimit Scope assrt_scope with A.

Declare Scope aexpv_scope.
Delimit Scope aexpv_scope with E.

Declare Scope valid_scope.
Delimit Scope valid_scope with V.

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

Arguments aveval _ _ _%aexpv_scope.

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

Infix "/\" := AssrtAnd : assrt_scope.
Infix "\/" := AssrtOr : assrt_scope.
Infix "->" := AssrtImp : assrt_scope.
Infix "<" := AssrtLt : assrt_scope.
Infix "<=" := AssrtLeq : assrt_scope.
Notation "'~' P" := (AssrtNot P) (at level 75, right associativity) : assrt_scope.

Notation "'For' i '.' P" :=
  (AssrtForall i P)
  (at level 200, right associativity) : assrt_scope.

Notation "'Ex' i '.' P" :=
  (AssrtExists i P)
  (at level 200, right associativity, only parsing) : assrt_scope.

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

Notation "m '+' I '|=' P" := (sat m I P%A) (at level 50) : valid_scope.

Definition valid_assrt P :=
  forall m I, (m+I |= P)%V.

Notation "'|=' P" := (valid_assrt P%A) (at level 50) : valid_scope.

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
  (m+I |= b)%V <-> beval m b.
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

Lemma val_no_ivars (n:int) :
  ~ has_ivars n.
Proof. auto. Qed.

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

Definition assrt_subst (x : varid) (a : aexpv) (_ : ~ has_ivars a) : assrt -> assrt :=
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

Notation "P '[' a '/' x ']'" := 
  (assrt_subst x _ (aexp_no_ivars a) P)
  (at level 10, a at level 5) : assrt_scope.

Notation "a '[' b '/' x ']'" := 
  (aexpv_subst x b a)
  (at level 10, b at level 5) : aexpv_scope.


Definition assrt_isubst (i : ivar) (a : aexpv) (_ : ~ has_ivars a) : assrt -> assrt :=
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


(*


(* https://stackoverflow.com/questions/44034734/overloading-notation-for-different-types-in-coq *)
Class Subst (ID S T : Type) := substT : ID -> S -> T -> T.

Notation "P '[' a '/' x ']'" := 
  (substT x a P)
  (at level 10, a at level 5).

Instance SubstAexpInAssrt  : Subst varid aexp assrt := 
  fun x a P => assrt_subst x _ (aexp_no_ivars a) P.
Instance SubstIntInAssrt   : Subst varid int assrt  := 
  fun x n P => assrt_subst x _ (@val_no_ivars n) P.
Instance SubstAexpvInAexpv : Subst varid aexpv aexpv := aexpv_subst.
Instance SubstIntInAexpv   : Subst varid int aexpv   := aexpv_subst.


*)


Section SubstProperties.

Lemma aexpv_subst_equiv m I x a n : 
  aveval m I (a[(AvVal n)/x]) = aveval (m[x=n]) I a.
Proof.
  induction a; simpls; auto; try math.
  case_if; simpls.
  - subst. rewrite upd_read1. trivial.
  - unfold upd. case_if. trivial.
Qed.

Lemma aexpv_isubst_equiv m I i a n : 
  aveval m I (aexpv_isubst i (AvVal n) a) = aveval m (I[i=n]) a.
Proof.
  induction a; simpls; auto; try math.
  + case_if; simpls.
    * subst. rewrite upd_read1. trivial.
    * unfold upd. case_if. trivial.
Qed.

Lemma assrt_subst_equiv m I x n P :
  (m+I |= P[n/x])%V <-> (m[x=n]+I |= P)%V.
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
      rewrite H in IHP1. 
      specializes IHP2 n.
      rewrite IHP1 in IHP2. apply prop_ext. auto.
    + intros. 
      specializes IHP1 n.
      rewrite H in IHP1. 
      specializes IHP2 n.
      rewrite <- IHP1 in IHP2. now apply prop_ext.
  - intros. do 2 rewrite aexpv_subst_equiv. easy.
  - intros. do 2 rewrite aexpv_subst_equiv. easy.
  - intros. do 2 rewrite aexpv_subst_equiv. easy.
  - split. 
    + intros. eapply IHP, H.
    + intros.
      eapply IHP, H.
  - intros. split.
    + intros (?&?).
      exists x0.
      eapply IHP, H.
    + intros (?&?).
      exists x0.
      eapply IHP, H.
Qed.

Lemma assrt_isubst_equiv m I i n P H :
  (m+I |= assrt_isubst i n H P)%V <-> (m+I[i=n] |= P)%V.
Proof.
  Set Printing Coercions.
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
  (m+I |= (For i. P))%V <->
  forall (n:int), (m+I |= assrt_isubst i _ (@val_no_ivars n) P)%V.
Proof.
  simpls. split; intros.
  - apply assrt_isubst_equiv. apply H.
  - specializes H n. specializes~ H.
    apply assrt_isubst_equiv in H.
    apply H.
Qed.

(* Winskel Ex6.6 *)
Corollary assrt_isubst_exists_equiv m I i P :
  (m+I |= (Ex i. P))%V <->
  exists (n:int), (m+I |= assrt_isubst i _ (@val_no_ivars n) P)%V.
Proof.
  simpls. splits; intros.
  - destruct H. rewrite <- assrt_isubst_equiv in H.
    exists x. apply H.
  - exists* H. apply assrt_isubst_equiv in H.
    exists. apply H.
Qed.


Lemma aexpv_subst_compat b :
  forall m I x a a',
  aeval m a = aeval m a' ->
  aveval m I (b[a/x])%E =
  aveval m I (b[a'/x])%E.
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


Lemma assrt_subst_compat P :
  forall m I x a b,
  aeval m a = aeval m b ->
  (m+I |= P[a/x] <->
  m+I |= P[b/x])%V.
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


Corollary subst_val P :
  forall m I x a,
  (m+I |= P[a/x])%V <->
  (m+I |= P[(aeval m a)/x])%V.
Proof.
  intros.
  pose proof assrt_subst_compat P m I x a (AVal (aeval m a)).
  auto.
Qed.

End SubstProperties.



Section SatRules.

Open Scope valid_scope.

Lemma sat_true m I :
  m+I |= true.
Proof.
  easy.
Qed.

Lemma sat_neg m I P :
  ~ (m+I |= P) <-> m+I |= ~P.
Proof.
  now simpls.
Qed.

Lemma sat_and m I P1 P2 :
  (m+I |= P1 /\ m+I |= P2) <-> m+I |= (P1 /\ P2).
Proof.
  simpls. split; auto.
Qed.

Lemma sat_or m I P1 P2 :
  (m+I |= P1 \/ m+I |= P2) <-> m+I |= (P1 \/ P2).
Proof.
  simpls. split; intros; auto.
Qed.

Lemma sat_imp m I P1 P2 :
  (m+I |= P1 -> m+I |= P2) <-> m+I |= (P1 -> P2).
Proof.
  simpls. split; intros; auto.
Qed.

Lemma sat_forall m i I P :
  (forall n, m+I[i=n] |= P) <->
  m+I |= (For i. P).
Proof.
  simpls. split; intros; auto.
Qed.

Lemma sat_exists m i I P :
  (exists n, m+I[i=n] |= P) <-> m+I |= Ex i. P.
Proof.
  simpls. 
  split. trivial. trivial.
Qed.

Lemma sat_eqa m I a1 a2 :
  (aveval m I a1 = aveval m I a2) <-> m+I |= AssrtEqA a1 a2.
Proof.
  simpls. split; auto.
Qed.

Lemma sat_eqb m I P Q :
  (m+I |= P <-> m+I |= Q) <-> m+I |= AssrtEqB P Q.
Proof.
  simpls. split; auto. apply prop_ext. intros. rewrite H. easy.
Qed.

Lemma sat_lt m I (a1 a2 : aexpv) :
  lt (aveval m I a1) (aveval m I a2) <-> m+I |= (a1 < a2).
Proof.
  simpls. split; auto.
Qed.

Lemma sat_leq m I a1 a2 :
  le (aveval m I a1) (aveval m I a2) <-> m+I |= (a1 <= a2).
Proof.
  simpls. split; auto.
Qed.

End SatRules.



Section ValidRules.

Open Scope valid_scope.

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

Lemma valid_imp_taut P Q :
  |= P ->
  |= (Q -> P).
Proof.
  introv ??. easy.
Qed.

Lemma valid_imp_disj_R P Q R :
  |= (P -> Q) ->
  |= (P -> (Q \/ R)).
Proof.
  introv ??.
  simpls; left.
  specializes H m I.
Qed. 

Lemma valid_imp_disj_L P Q R :
  |= (P -> Q) ->
  |= (P -> (R \/ Q)).
Proof.
  introv ??.
  simpls; right.
  specializes H m I.
Qed.

Lemma valid_imp_and_l P Q R :
  |= (P -> R) ->
  |= (P /\ Q -> R).
Proof.
  introv ??.
  specializes H m I.
  simpls. now apply H.
Qed.

Lemma valid_disj_imp P Q R :
  |= (P -> R) ->
  |= (Q -> R) ->
  |= ((P \/ Q) -> R).
Proof.
  introv ??.
  simpls. 
  unfold valid_assrt in *.
  intros.
  specializes H m I.
  specializes H0 m I.
  rewrite <- sat_imp in *.
  intros.
  rewrite <- sat_or in H1.
  destruct H1; auto.
Qed.

End ValidRules.


Hint Resolve valid_imp_refl : core.


Definition triple m I c P Q :=
  (m+I |= P)%V ->
  forall m', yields c m m' ->
  (m'+I |= Q)%V.

Definition valid_triple c P Q :=
  forall m I, triple m I c P Q.

Notation "'|=' c ':' P '=>' Q" := (valid_triple c P%A Q%A)
  (at level 50, c at next level, no associativity) : valid_scope.


Section Soundness.

Open Scope valid_scope.

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
  destruct (classic (m+I |= P')).
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

End Soundness.