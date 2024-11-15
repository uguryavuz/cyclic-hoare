Set Implicit Arguments.

From SLF Require Export LibRelation LibSepReference.
Export ProgramSyntax.
From Coq Require Export 
  Init.Specif 
  Logic.FunctionalExtensionality
  Logic.IndefiniteDescription 
  Logic.Classical_Prop
  Logic.Description.

(* Destruct proposition *)
Ltac either P :=
  let E := fresh "E" in
  pose proof (classic P) as E;
  destruct E.

Lemma conjunction_hypothesis : forall (P Q R : Prop),
  (P /\ Q -> R) <->
  (P -> Q -> R).
Proof using.
  introv. split; intros. auto.
  destruct H0. apply~ H.
Qed.

(* Repeat eexists without unfolding *)
Ltac eexists_rep :=
  repeat match goal with
  | [ |- exists _, _ ] => eexists
  end.
Tactic Notation "eexists*" := eexists_rep.

Ltac exists_rep_H H :=
  match type of H with
  | exists x, _ => 
    let x' := fresh x in
    destruct H as (x'&H);
    exists_rep_H H
  | _ /\ _ =>
    let H' := fresh H in
    destruct H as (H&H');
    exists_rep_H H;
    exists_rep_H H'
  | _ <-> _ =>
    let H' := fresh H in
    destruct H as (H&H');
    exists_rep_H H;
    exists_rep_H H'
  | _ => idtac
  end.

Tactic Notation "exists*" hyp(H) := 
  progress (exists_rep_H H).

Tactic Notation "exists*" hyp(H) "," hyp(H1) := 
  exists* H; exists* H1.

Tactic Notation "exists*" hyp(H) "," hyp(H1) "," hyp(H2) := 
  exists* H; exists* H1; exists* H2.



Theorem not_neq : forall (P Q : Type),
~ (P <> Q) <-> P = Q.
Proof using.
  split; intro.
  - rewrite not_not_eq in H. auto.
  - intro. contradiction.
Qed.

Ltac contra H :=
  apply not_not_inv;
  contradict H;
  repeat (rewrite not_not_eq in *).

Ltac inj H :=
  injection H as H.
  

Lemma none_not_some : forall {T : Type} (i : option T),
  i <> None ->
  exists j, i = Some j.
Proof using.
  intros. destruct i. eexists. auto.
  contradiction.
Qed.


Lemma one_for_other P Q :
  (P /\ (P -> Q)) ->
  P /\ Q.
Proof using.
  intros. exists* H. splits~.
Qed.

Lemma some_neq_none :
  forall T (x : T),
  Some x <> None.
Proof using.
  intros. intro. discriminate.
Qed.
  


Definition eval_u s c s' :=
  eval s c s' val_unit.
   

Ltac split_forall H :=
  try match type of H with
  | forall _, (_ /\ _) =>
    let H' := fresh H in
    apply forall_conj_inv_1 in H as (H&H');
    split_forall H;
    split_forall H'
  end.

Tactic Notation "split_forall" hyp(H) :=
  progress split_forall H.

Tactic Notation "dup_hyp" hyp(H) :=
  let H' := fresh H in
  pose proof H as H'.


Axiom n_pos_inf : nat.
Axiom n_inf_gt : forall n:nat, (n < n_pos_inf).
Axiom n_inf_add : forall n:nat, (n_pos_inf + n = n_pos_inf).

Axiom z_pos_inf : int.
Axiom z_neg_inf : int.

Axiom z_inf_gt : forall z : int, (z < z_pos_inf)%Z.
Axiom z_inf_lt : forall z : int, (z_neg_inf < z)%Z.

Lemma z_inf_comp : (z_neg_inf < z_pos_inf)%Z.
Proof using. apply z_inf_gt. Qed.

Lemma z_inf_ltb : forall z : int, (z_neg_inf <? z)%Z = true.
Proof using. intro. rewrite Z.ltb_lt. apply z_inf_lt. Qed.

Lemma z_inf_gtb : forall z : int, (z <? z_pos_inf)%Z = true.
Proof using. intro. rewrite Z.ltb_lt. apply z_inf_gt. Qed.


Module ListFacts.

  Import LibList.

  Lemma destruct_nonempty_list : forall {T : Type} (l : list T) (n : nat),
    length l = n ->
    n > 0%nat ->
    exists h t,
    l = h::t /\
    length t = pred n.
  Proof using.
    intros. subst. apply length_pos_inv_cons in H0.
    destruct H0 as (?&?&?). subst.
    eexists*. auto.
  Qed.


  Ltac list_from_length H :=
    match type of H with
    | length ?l = 0%nat =>
      apply length_zero_inv in H; subst l
    | length ?l = ?n =>
      apply destruct_nonempty_list in H;
      [| math; fail ];
      destruct H as (?&?&?&H); 
      simpl in H; subst; 
      list_from_length H
    end.

End ListFacts.
Export ListFacts.

(**************************************
 *** MAP THINGS 
 **************************************)

Notation "H1 \++ H2" := (hor H1 H2)
  (at level 100, right associativity) : hprop_scope.

Notation "x \> v" := (Fmap.single x v)
  (at level 36).

Ltac indom_some H :=
  match type of H with
  | indom ?m ?p =>
    unfold indom, map_indom in H;
    apply none_not_some in H;
    destruct H as (?&H)
  end.

Axiom exists_fresh_loc : forall (h : heap),
  exists (p : loc), ~ indom h p.

Parameter make_fresh_loc : heap -> loc.
Parameter indom_fresh_loc : forall h,
  ~ indom h (make_fresh_loc h).
Parameter indom_not_null : forall h,
  (make_fresh_loc h) <> null.


Section FMapFacts.

  Variables A B : Type.
  Local Definition F := fmap A B.

  Variable IB : Inhab B.

  Implicit Type m l r : F.
  Implicit Type p q : A.
  Implicit Type x y : B.

  Lemma update_permute : forall m p q x y,
    p <> q ->
    update (update m p x) q y = update (update m q y) p x.
  Proof using.
    introv H.
    unfold update. rewrite <- union_assoc.
    rewrite (union_comm_of_disjoint (q \> y) (p \> x)).
    apply union_assoc. apply~ disjoint_single_single.
  Qed.

  Lemma indom_single_diff : forall p q x,
    p <> q ->
    ~ indom (p \> x) q.
  Proof using.
    intros. unfold indom, map_indom.
    unfold single. simpl. rewrite~ If_r.
  Qed.

  Lemma indom_union_destruct : forall l r p,
    indom l p \/ indom r p <->
    indom (l \u r) p.
  Proof using.
    introv. split; intro H.
    - destruct H.
      applys indom_union_l H.
      applys indom_union_r H.
    - unfolds indom, map_indom, union, map_union. simpls.
      destruct~ (fmap_data l p).
  Qed.

  Lemma indom_not_union : forall l r p,
    ~ indom l p ->
    ~ indom r p ->
    ~ indom (l \u r) p.
  Proof using.
    introv Hl Hr.
    pose proof (indom_union_destruct l r p).
    rewrite <- iff_not_not_eq in H.
    apply H. rewrite~ not_or_eq.
  Qed.

  Lemma indom_not_union_destruct : forall l r p,
    ~ indom (l \u r) p ->
    ~ indom l p /\ ~ indom r p.
  Proof using.
    introv H.
    pose proof (indom_union_destruct l r p).
    rewrite <- iff_not_not_eq in H0.
    apply H0 in H. auto.
  Qed.

  Lemma indom_not_single : forall p q x,
    ~ indom (p \> x) q ->
    p <> q.
  Proof using.
    introv H. unfolds indom, map_indom, single. simpls.
    contra H. subst. rewrite~ If_l. discriminate.
  Qed.

  Lemma disjoint_single_single_diff : forall p q x y,
    disjoint (p \> x) (q \> y) ->
    p <> q.
  Proof using.
    introv H. contradict H. subst. intro.
    apply disjoint_single_single_same_inv in H.
    auto.
  Qed.

  Lemma indom_excluded_middle : forall m p,
    indom m p \/ ~ indom m p.
  Proof using.
    introv. unfold indom, map_indom.
    destruct (fmap_data m p).
    left. discriminate. auto.
  Qed.

  Lemma indom_exists : forall m p,
    indom m p ->
    exists x, m = p \> x \u m.
  Proof using.
    introv H. apply none_not_some in H.
    destruct H. exists x. apply fmap_extens. intro.
    unfolds union, map_union, single. simpls. case_if~.
    subst~.
  Qed.
    

  Lemma union_shadow_single : forall {A B : Type} (p : A) (x y : B),
    p \> x \u p \> y = p \> x.
  Proof using.
    introv. rewrite <- update_eq_union_single.
    apply update_single.
  Qed.

  Lemma union_shadow_r : forall m p x y,
    p \> x \u (p \> y \u m) = p \> x \u m.
  Proof using.
    introv. rewrite <- union_assoc.
    rewrite union_shadow_single. auto.
  Qed.

  Lemma union_shadow : forall m p x,
    indom m p -> m \u p \> x = m.
  Proof using.
    introv H. apply fmap_extens. intro.
    unfold union, map_union, single. simpls.
    destruct (fmap_data m x0) eqn:E; auto.
    unfolds indom, map_indom.
    apply If_r. intro. subst. contradiction.
  Qed.

  Lemma union_shadow_l : forall m p x y,
    (p \> x \u m) \u p \> y = p \> x \u m.
  Proof using.
    introv. either (indom m p).
    - pose proof (union_shadow y H). rewrite union_assoc.
      rewrite~ H0.
    - rewrite union_assoc. rewrite (@union_comm_of_disjoint _ _ m _).
      apply union_shadow_r. rewrite disjoint_comm.
      apply~ disjoint_single_of_not_indom.
  Qed.

  Lemma union_shadow_middle : forall l r p x y,
    p \> x \u (l \u p \> y \u r) = p \> x \u (l \u r).
  Proof using.
    introv. replace (p \> x \u (l \u p \> y \u r))
      with (((p \> x \u l) \u p \> y) \u r).
    rewrite union_shadow_l. apply union_assoc.
    rewrite union_assoc. apply union_assoc.
  Qed.   


  Lemma single_extensionality : forall p x y,
    p \> x = p \> y ->
    x = y.
  Proof using. 
    introv H. apply eq_inv_fmap_data_eq with (x:=p) in H.
    simpls. rewrite If_l in H. rewrite If_l in H.
    injects H. all: autos.
  Qed.

  Lemma remove_union_id : forall m p x,
    p \> x \u m = p \> x \u remove m p.
  Proof using.
    introv. apply fmap_extens. intro.
    unfold remove, map_remove, map_union, union, single, map_union.
    simpls. case_if. auto.
    rewrite~ If_r.
  Qed.

  Lemma remove_empty : forall p,
    @remove A B empty p = empty.
  Proof using.
    introv. apply fmap_extens. intro.
    unfold remove, map_remove, empty. simpls.
    case_if~.
  Qed.

  Lemma remove_neq : forall m p q x,
    p <> q ->
    remove (p \> x \u m) q = p \> x \u remove m q.
  Proof using.
    introv H. apply fmap_extens. intro.
    unfold remove, map_remove, union, map_union, single. simpls.
    case_if.
    - subst. rewrite~ If_r.
    - case_if~.
  Qed.

  Lemma remove_eq : forall m p x,
    remove (p \> x \u m) p = remove m p.
  Proof using.
    introv. apply fmap_extens. intros.
    unfold remove, map_remove, union, map_union, single.
    simpls. case_if~.
    rewrite~ If_r.
  Qed.

  Lemma remove_single : forall p x,
    remove (p \> x) p = empty.
  Proof using.
    introv. apply fmap_extens. intro.
    unfold remove, map_remove, single. simpls.
    case_if~. case_if~.
  Qed.

  Lemma remove_single_diff : forall p q x,
    p <> q ->
    remove (p \> x) q = p \> x.
  Proof using.
    introv H. apply fmap_extens. intro.
    unfold remove, map_remove, single. simpls.
    case_if~. case_if~.
  Qed.

  Lemma remove_not_indom : forall m p,
    ~ indom m p ->
    remove m p = m.
  Proof using.
    introv H. apply fmap_extens. intro.
    unfolds remove, map_remove, indom, map_indom.
    simpls. case_if~. subst.
    rewrite not_not_eq in H. auto.
  Qed.

  Lemma disjoint_single_of_not_indom_r : forall m p x,
    disjoint m (p \> x) ->
    ~ indom m p.
  Proof using.
    intros. unfolds disjoint, map_disjoint, indom, map_indom.
    specializes H p. destruct H.
    - rewrite~ not_not_eq.
    - unfolds single. simpls. rewrite If_l in H; auto.
      discriminate.
  Qed.
  
  Lemma disjoint_single_of_not_indom_l : forall m p x,
    disjoint (p \> x) m ->
    ~ indom m p.
  Proof using.
    intros. rewrite disjoint_comm in H.
    applys disjoint_single_of_not_indom_r.
    apply H.
  Qed.
  
  Lemma fmap_eq_read : forall (m1 m2 : F) p,
    m1 = m2 -> read m1 p = read m2 p.
  Proof using. intros. subst~. Qed.

  Lemma fmap_eq_indom : forall (m1 m2 : F) p,
    m1 = m2 -> indom m1 p = indom m2 p.
  Proof using. intros. subst~. Qed.

  Lemma fmap_single_pull : forall m p x,
    indom m p ->
    read m p = x ->
    m = p \> x \u remove m p.
  Proof using.
    intros. subst.
    unfolds read. unfolds single, union, map_union. simpls.
    destruct m. apply fmap_extens. intro.
    simpls. case_if.
    - subst. unfolds indom, map_indom. simpls.
      apply none_not_some in H. destruct H.
      rewrite~ H.
    - unfolds map_remove. rewrite~ If_r.
  Qed.

  Lemma remove_pull : forall m p x,
    indom m p ->
    read m p = x ->
    m = p \> x \u remove m p.
  Proof using.
    intros. rewrite <- remove_union_id.
    apply fmap_extens. intro.
    either (x0 = p).
    - subst. unfold union, map_union, single. simpls.
      rewrite~ If_l. unfold read. unfolds indom, map_indom.
      destruct~ (fmap_data m p). contradiction.
    - subst. unfold union, map_union, single. simpls.
      rewrite~ If_r.
  Qed.

  Lemma indom_not_indom : forall m p q,
    indom m p ->
    ~ indom m q ->
    p <> q.
  Proof using.
    introv H J. contra J. subst~.
  Qed.


  Lemma double_union : forall (x1 x2 y1 y2 : F),
    x1 \u x2 = y1 \u y2 ->
    disjoint x1 x2 ->
    disjoint y1 y2 ->
    disjoint x1 y2 ->
    disjoint x2 y1 ->
    x1 = y1 /\ x2 = y2.
  Proof using.
    intros. split.
    - apply fmap_extens. intro.
      specializes H0 x.
      specializes H1 x.
      specializes H2 x.
      specializes H3 x.
      unfolds disjoint, map_disjoint, union, map_union.
      inverts H. rename x into x'. 
      apply equal_f with (x:=x') in H5.
      destruct H0, H1, H2, H3.
      all: rewrite H in *.
      all: rewrite H0 in *.
      all: try rewrite H1 in *.
      all: try rewrite H2 in *.
      all: try auto.
      all: destruct (fmap_data y1 x'), (fmap_data x1 x').
      all: auto.
    - apply fmap_extens. intro.
      specializes H0 x.
      specializes H1 x.
      specializes H2 x.
      specializes H3 x.
      unfolds disjoint, map_disjoint, union, map_union.
      inverts H. rename x into x'. 
      apply equal_f with (x:=x') in H5.
      destruct H0, H1, H2, H3.
      all: rewrite H in *.
      all: rewrite H0 in *.
      all: try rewrite H1 in *.
      all: try rewrite H2 in *.
      all: try auto.
  Qed.
  

  Lemma union_comm_assoc :
    forall m1 m2 m3,
    disjoint m1 m2 ->
    disjoint m1 m3 ->
    m1 \u (m2 \u m3) =
    m2 \u (m1 \u m3).
  Proof using IB.
    intros.
    rewrite union_comm_of_disjoint.
    rewrite union_assoc.
    rewrite~ (union_comm_of_disjoint m3 m1).
    rewrite~ disjoint_union_eq_r.
  Qed.

  Lemma disjoint_assoc m1 m2 m3 :
    disjoint m1 m2 ->
    disjoint (m1 \u m2) m3 ->
    disjoint m1 (m2 \u m3).
  Proof using IB.
    intros.
    rewrite disjoint_union_eq_l in H0.
    rewrite disjoint_union_eq_r. splits~.
  Qed.


End FMapFacts.

Definition subheap (h h' : heap) :=
  exists k,
  disjoint k h /\
  h' = k \u h.

Definition val_not_null : Type :=
  { v : val | v <> () }.

Section HeapFacts.

  Implicit Type h : heap.
  Implicit Type p : loc.
  Implicit Type x y v : val.
  Implicit Type H : hprop.

  Lemma hsingle_intro_eq : forall p x y,
    x = y ->
    (p ~~> x) (p \> y).
  Proof using. intros. subst. apply hsingle_intro. Qed.

  Lemma hsingle_read : forall H h p v,
    (p ~~> v \* H) h ->
    read h p = v.
  Proof using.
    introv I. destruct I as (?&?&?&?&?&?). subst.
    apply hsingle_inv in H0. subst.
    rewrite read_union_l. apply read_single.
    apply indom_single.
  Qed.

  Lemma hsingle_frame : forall H h p v,
    indom h p ->
    read h p = v ->
    H (remove h p) ->
    (p ~~> v \* H) h.
  Proof using.
    intros. pose proof (@remove_pull _ _ _ h).
    specializes H3 H0 H1. subst. rewrite H3.
    apply hstar_intro.
    - indom_some H0. apply hsingle_intro_eq.
      unfold read. rewrite H0.
      unfold union, map_union, single. simpl.
      rewrite~ If_l.
    - auto.
    - unfold disjoint, map_disjoint. intro.
      simpl. unfold map_remove.
      case_if~. subst. rewrite~ If_l.
  Qed.

  Theorem frame_empty : forall H h,
    H h ->
    (H \* \[]) h.
  Proof using. intros. rewrite~ hstar_hempty_r. Qed.

  Lemma heap_eq_pop :
    forall p v h h',
    ~ indom h p ->
    ~ indom h' p ->
    p \> v \u h = p \> v \u h' ->
    h = h'.
  Proof using.
    unfold single, union. simpls. intros.
    inverts H1. unfolds map_union.
    apply fmap_extens. intro.
    apply equal_f with (x := x) in H3.
    either (p = x).
    - subst. unfolds indom, map_indom.
      contra H0. rewrite H in H0. auto.
    - rewrite~ If_r in H3.
  Qed.


End HeapFacts.




Notation "g '∘' f" := (fun x => g (f x)) (at level 40, left associativity).

Notation "X '?'" := (option X) (at level 5).

(* Subset of T encoded as a predicate *)
Notation "'[' T ']'" := (T -> Prop).


Definition pred_plus (Ψ : [heap]) : [heap] :=
  \exists Φ, Ψ \* Φ.

Notation "Ψ '⁺'" := (pred_plus Ψ) (at level 5, format "Ψ ⁺").


(* Elements within a subset *)
Notation "'∈' sub" := { x : _ | sub x } (at level 6).

Definition subset {T : Type} (A A' : [T]) :=
  forall x, A x -> A' x.

Notation "A ⊆ A'" := (subset A A') (at level 65).

Lemma subset_trans :
  forall {T} (A B C : [T]),
  A ⊆ B ->
  B ⊆ C ->
  A ⊆ C.
Proof using.
  unfold subset. intros.
  specializes H x H1.
Qed.

Definition subset_proper {T : Type} (A A' : [T]) :=
  A ⊆ A' /\
  exists x, A' x /\ ~ A x.

Notation "A ⊂ A'" := (subset_proper A A') (at level 65).

Definition emptyset {T : Type} : [T] :=
  fun _ => False.

Notation "∅" := emptyset.

Lemma emptyset_not_nonempty :
  forall {X} (H : [X]) (x : X),
  ∅ = H -> ~ H x.
Proof using.
  intros. apply equal_f with x in H0.
  rewrite eq_prop_eq_iff in H0.
  exists* H0. either (H x).
  specializes~ H1 H2. auto.
Qed.

Lemma subset_emptyset :
  forall {T} (P : [T]),
  ∅ ⊂ P <->
  exists t, P t.
Proof using.
  unfold subset_proper, subset. intros.
  splits; intros.
  - exists* H. exists~ x.
  - splits. now intros.
    destruct* H.
Qed.

Lemma not_emptyset :
  forall {T} (P : [T]),
  P <> ∅ <->
  exists t,
  P t.
Proof using.
  intros. splits; intros.
  - contra H. rewrite not_exists_eq in H.
    apply functional_extensionality. intro.
    specializes H x. unfold emptyset. contra H.
    rewrite~ prop_neq_False_eq in H.
  - exists* H. intro. now rewrite H0 in H.
Qed.

Lemma eq_not_emptyset :
  forall (T : Type) (x : T),
  eq x = ∅ -> False.
Proof using.
  intros. contradict H.
  rewrite not_emptyset. now exists.
Qed.
  
Lemma emptyset_false :
  forall {T} (t : T),
  ∅ t = False.
Proof using.
  auto.
Qed.


Section SetOps.

Variable T : Type.

Implicit Type P Q R : [T].
Implicit Type t : T.

Definition subset_and P Q : [T] :=
  fun t =>
  P t /\ Q t.

Definition subset_or P Q : [T] :=
  fun t =>
  P t \/ Q t.

End SetOps.

Notation "P '∩' Q" := (subset_and P Q) (left associativity, at level 40).

Notation "P '∪' Q" := (subset_or P Q) (left associativity, at level 40).

(*Section SetOpProperties.




End SetOpProperties.*)



Lemma destruct_if :
  forall B P Q,
  ((B -> P) /\ (~ B -> Q)) =
  If B then P else Q.
Proof using.
  intros. rewrite eq_prop_eq_iff.
  splits; intros.
  - exists* H. either B.
    rewrite~ If_l. rewrite~ If_r.
  - splits; intros. rewrite~ If_l in H.
    rewrite~ If_r in H.
Qed.

Lemma destruct_if2 :
  forall {T} B P Q (x : T),
  (If B then P else Q) x =
  ((B -> P x) /\ (~ B -> Q x)).
Proof using.
  intros. rewrite eq_prop_eq_iff.
  splits; intros.
  - splits; intros. rewrite~ If_l in H.
    rewrite~ If_r in H.
  - exists* H. either B.
    rewrite~ If_l. rewrite~ If_r.
Qed.


Module MapTactics.

  (* Normalize fmaps through associativity *)
  Local Ltac assoc_norm_fmap :=
    repeat match goal with
    | [ |- context[(?h1 \u ?h2) \u ?h3] ] =>
      rewrite (@union_assoc _ _ h1 h2 h3)
    | [ H : context[(?h1 \u ?h2) \u ?h3] |- _ ] =>
      rewrite (@union_assoc _ _ h1 h2 h3) in H
    end.

  Local Ltac simpl_fmap_remove_setup :=
    repeat match goal with
    | [ |- context[?p \> ?x \u (?q \> ?y \u ?m)] ] =>
      rewrite (remove_union_id (q \> y \u m) p x)
    | [ |- context[?p \> ?x \u (?q \> ?y)] ] =>
      rewrite (remove_union_id (q \> y) p x)
    | [ H : context[?p \> ?x \u (?q \> ?y \u ?m)] |- _ ] =>
      rewrite (remove_union_id (q \> y \u m) p x) in H
    | [ H : context[?p \> ?x \u (?q \> ?y)] |- _ ] =>
      rewrite (remove_union_id (q \> y) p x) in H
    end.

  Ltac simpl_fmap_clear_remove := 
    match goal with
    | [ |- context[remove empty ?p] ] =>
      rewrite (@remove_empty _ _ p)
    | [ |- context[remove ?m (make_fresh_loc ?m)] ] =>
      rewrite (remove_not_indom (@indom_fresh_loc m))
    | [ |- context[remove (?p \> ?x \u ?m) ?p] ] =>
      rewrite (@remove_eq _ _ m p x)
    | [ |- context[remove (?p \> ?x) ?p] ] =>
      rewrite (@remove_single _ _ p x)
    | [ |- context[remove (?p \> ?x) ?q] ] =>
      rewrite (@remove_single_diff _ _ p q x); [| auto; fail]
    | [ |- context[remove (?p \> ?x \u ?m) ?q] ] =>
      rewrite (@remove_neq _ _ m p q x); [| auto; fail]
    | [ H : ~ indom ?m ?p |- context[remove ?m ?p] ] =>
      rewrite (@remove_not_indom _ _ m p H)

    | [ H : context[remove empty ?p] |- _ ] =>
      rewrite (@remove_empty _ _ p) in H
    | [ H : context[remove (?p \> ?x \u ?m) ?p] |- _ ] =>
      rewrite (@remove_eq _ _ m p x) in H
    | [ H : context[remove (?p \> ?x) ?p] |- _ ] =>
      rewrite (@remove_single _ _ p x) in H
    | [ H : context[remove (?p \> ?x) ?q] |- _ ] =>
      rewrite (@remove_single_diff _ _ p q x) in H;
      [| auto; fail]
    | [ H : context[remove (?p \> ?x \u ?m) ?q] |- _ ] =>
      rewrite (@remove_neq _ _ m p q x) in H;
      [| auto; fail]
    | [ H' : ~ indom ?m ?p, 
        H :context[remove ?m ?p] |- _ ] =>
      rewrite (@remove_not_indom _ _ m p H') in H
    end.

  Ltac simpl_fmap_read :=
    repeat (rewrite read_single in *);
    assoc_norm_fmap;
    repeat match goal with
    | [ |- context[read (?l \u ?r) ?x] ] =>
      first [
        rewrite (@read_union_l _ _ _ l r x);
        [ | solve_fmap; fail ]
      |
        rewrite (@read_union_r _ _ _ l r x);
        [ | solve_fmap; fail ]
      ]
    | [ H : context[read (?l \u ?r) ?x] |- _ ] =>
      first [
        rewrite (@read_union_l _ _ _ l r x) in H;
        [ | solve_fmap; fail ]
      |
        rewrite (@read_union_r _ _ _ l r x) in H;
        [ | solve_fmap; fail ]
      ]
    end

  with simpl_fmap_elim_empties :=
    repeat (
      try (rewrite union_empty_l in *);
      try (rewrite union_empty_r in *))

  with simpl_fmap_elim_dupes :=
    simpl_fmap_remove_setup;
    repeat simpl_fmap_clear_remove

  with simpl_fmap_elim_updates :=
    repeat (rewrite update_eq_union_single in *)

  with simpl_fmap :=
    simpl_fmap_elim_updates;
    simpl_fmap_elim_empties;
    repeat simpl_fmap_read;
    simpl_fmap_elim_dupes;
    simpl_fmap_elim_empties

  with simpl_disjoint :=
    repeat match goal with
    | [ H : disjoint (_ \> _) (_ \> _) |- _ ] =>
      first [
        apply disjoint_single_single_diff in H
      |
        apply disjoint_single_single_same_inv in H;
        contradiction
      ]
    | [ H : disjoint _ (_ \u _) |- _ ] =>
      rewrite disjoint_union_eq_r in H; destruct H
    | [ H : disjoint (_ \u _) _ |- _ ] =>
      rewrite disjoint_union_eq_l in H; destruct H
    | [ H : disjoint empty _ |- _ ] => clear H
    | [ H : disjoint _ empty |- _ ] => clear H
    | [ H : disjoint (_ \> _) _ |- _ ] =>
      apply disjoint_single_of_not_indom_l in H
    | [ H : disjoint _ (_ \> _) |- _ ] =>
      apply disjoint_single_of_not_indom_r in H
    end

  with destruct_heap H :=
    simpl in H;
    unfold pred_plus in H;
    simpl_disjoint; simpl_fmap;
    try match type of H with
    | \[] _ =>
      apply hempty_inv in H; subst
    | \[_] _ =>
      apply hpure_inv in H;
      destruct H as (H&?); subst
    | (_ ~~> _) _ =>
      apply hsingle_inv in H; subst
    | (_ \* _) _ =>
      let L := fresh "L" in
      let R := fresh "R" in
      apply hstar_inv in H;
      destruct H as (?&?&L&R&?&?); subst;
      destruct_heap L; destruct_heap R
    | (\exists _, _) _ =>
      apply hexists_inv in H;
      destruct H as (?&H);
      destruct_heap H
    end

  with solve_fmap_indom :=
    match goal with
    | [ |- indom (?x \> _) ?x ] =>
      apply indom_single
    | [ |- indom (_ \u _) _ ] =>
      try (apply indom_union_l;
          solve_fmap_indom; auto; fail);
      try (apply indom_union_r;
          solve_fmap_indom; auto; fail)
    | [ |- indom (update _ _ _) _ ] =>
      rewrite update_eq_union_single;
      solve_fmap_indom
    end

  with solve_fmap_not_indom :=
    match goal with
    | [ H : ~ indom ?m ?x |- ~ indom ?m ?x ] =>
      assumption
    | [ |- ~ indom (_ \> _) _ ] =>
      apply indom_single_diff; auto
    | [ |- ~ indom (_ \u _) _ ] =>
      apply indom_not_union;
      solve_fmap_not_indom
    | [ |- ~ indom (update _ )] =>
      rewrite update_eq_union_single;
      solve_fmap_not_indom
    end

  with solve_fmap_disjoint :=
    match goal with
    | [ |- disjoint empty _ ] =>
      apply disjoint_empty_l
    | [ |- disjoint _ empty ] =>
      apply disjoint_empty_r
    | [ |- disjoint (_ \> _) (_ \> _) ] =>
      apply~ disjoint_single_single; fail
    | [ |- disjoint _ (_ \u _) ] =>
      rewrite disjoint_union_eq_r; split;
      solve_fmap_disjoint
    | [ |- disjoint (_ \u _) _ ] =>
      rewrite disjoint_union_eq_l; split;
      solve_fmap_disjoint
    | [ H : ~ indom ?m ?p |- disjoint (?p \> _) ?m ] =>
      apply (disjoint_single_of_not_indom H)
    | [ H : ~ indom ?m ?p |- disjoint ?m (?p \> _) ] =>
      rewrite disjoint_comm;
      apply (disjoint_single_of_not_indom H)
    end

  with solve_fmap :=
    repeat match goal with
    | [ |- disjoint _ _ ] => solve_fmap_disjoint
    | [ |- indom _ _ ]    => solve_fmap_indom
    | [ |- ~ indom _ _ ]  => solve_fmap_not_indom
    end.

  Tactic Notation "solve_fmap" :=
    progress solve_fmap.

  Local Tactic Notation "destruct_heap_unit" constr(H) :=
    progress (destruct_heap H).

  Tactic Notation "destruct_heap" constr(H) :=
    destruct_heap_unit H;
    simpl_disjoint; simpl_fmap.

  Tactic Notation "destruct_heap" constr(H1) "," constr(H2) :=
    destruct_heap_unit H1; 
    destruct_heap_unit H2;
    simpl_disjoint; simpl_fmap.

  Tactic Notation "destruct_heap" constr(H1) "," constr(H2) "," constr(H3) :=
    destruct_heap_unit H1; 
    destruct_heap_unit H2; 
    destruct_heap_unit H3;
    simpl_disjoint; simpl_fmap.


  Ltac hsf :=
    applys hsingle_frame;
    [ solve_fmap | simpl_fmap; auto | simpl_fmap ].

  Ltac fmap_compare_read H p :=
    match type of H with
    | ?h1 = ?h2 =>
      let H' := fresh H in
      pose proof H as H';
      apply (@fmap_eq_read _ _ _ h1 h2 p) in H';
      simpl_fmap;
      try (inj H');
      subst
    end.

  Ltac fmap_compare_indom H p :=
    match type of H with
    | ?h1 = ?h2 =>
      apply (@fmap_eq_indom _ _ _ h1 h2 p) in H;
      simpl_fmap
    end.
    
  Ltac solve_hprop :=
    repeat first
      [ assumption
      | reflexivity
      | progress solve_fmap
      | apply hpure_intro
      | rewrite hstar_assoc
      | rewrite hstar_hexists
      | applys hexists_intro
      | rewrite hstar_hempty_l
      | rewrite hstar_hempty_r
      | rewrite hstar_hpure_l; split
      | rewrite hstar_hpure_r; split
      | apply hsingle_intro
      | apply hsingle_intro_eq
      | hsf
      (*| apply hstar_intro*)
      (*| econstructor*)
      ].

End MapTactics.
Export MapTactics.



Section PredPlus.


  Lemma hstar_plus_assoc :
    forall Ψ1 Ψ2,
    (Ψ1 \* Ψ2)⁺ = Ψ1 \* Ψ2⁺.
  Proof using.
    intros. unfolds pred_plus.
    apply functional_extensionality. intro h.
    apply prop_ext. splits; intros.
    all: destruct_heap H.
    - apply~ hstar_intro. apply hexists_intro with x.
      apply~ hstar_intro.
    - applys hexists_intro. rewrite hstar_assoc.
      apply~ hstar_intro. apply~ hstar_intro.
      apply R0.
  Qed.

  Lemma hstar_plus_comm :
    forall Ψ1 Ψ2,
    Ψ1 \* Ψ2⁺ = Ψ1⁺ \* Ψ2.
  Proof using.
    intros. rewrite <- hstar_plus_assoc.
    rewrite hstar_comm.
    rewrite hstar_plus_assoc.
    apply hstar_comm.
  Qed.

  Lemma pred_plus_double :
    forall Ψ,
    Ψ⁺⁺ = Ψ⁺.
  Proof using.
    intros. unfolds pred_plus.
    apply functional_extensionality. intro h.
    apply prop_ext. splits; intros.
    all: destruct_heap H; simpl_disjoint.
    - applys hexists_intro.
      apply~ hstar_intro. apply~ hstar_intro.
      apply R0. apply R.
    - applys hexists_intro. apply~ hstar_intro.
      applys hexists_intro \[]. solve_hprop.
      apply R.
  Qed.

  Lemma hstar_plus_elim :
    forall Ψ1 Ψ2,
    Ψ1⁺ \* Ψ2⁺ = Ψ1⁺ \* Ψ2.
  Proof using.
    intros. rewrite hstar_plus_comm.
    rewrite~ pred_plus_double.
  Qed.

  Lemma pred_plus_extend :
    forall Ψ1,
    Ψ1 ⊆ Ψ1⁺.
  Proof using.
    unfold subset, pred_plus. intros.
    solve_hprop.
  Qed.

  Lemma pred_plus_union :
    forall (Ψ : [heap]) h h',
    Ψ⁺ h ->
    disjoint h h' ->
    Ψ⁺ (h \u h').
  Proof using.
    intros. rewrite <- pred_plus_double.
    apply hexists_intro with (x:=\Top).
    apply~ hstar_intro. apply htop_intro.
  Qed.
  
  Lemma pred_plus_mono Ψ Ψ' :
    Ψ ⊆ Ψ' -> Ψ⁺ ⊆ Ψ'⁺.
  Proof using.
    introv ? ?. destruct_heap H0.
    applys hexists_intro x0.
    apply~ hstar_intro.
  Qed.


End PredPlus.


Ltac clean :=
  repeat match goal with
  | [ H1 : ?P, H2 : ?P |- _ ] => clear H2
  | [ H : indom (single ?p _) ?p |- _ ] => clear H
  | [ H : ?x = ?x |- _ ] => clear H
  | [ H1 : ?x <> ?y, H2 : ?y <> ?x |- _ ] => clear H2
  | [ H1 : ?x = ?y, H2 : ?y = ?x |- _ ] => clear H2
  end.

  
Ltac clean_vals :=
  match goal with
  | [ |- val_int _ = val_int _ ] =>
    f_equal
  | _ => idtac
  end;
  repeat match goal with
  | [ H : ?u = ?v |- _ ] =>
    match type of u with
    | val => inj H
    end
  end.


(* Via https://stackoverflow.com/questions/62464821/how-to-make-an-inverse-function-in-coq *)
Section Bijection.

  Variables X Y : Type.

  Definition injective (f : X -> Y) := 
    forall x y, f x = f y -> x = y.

  Definition surjective (f : X -> Y) := 
    forall y, exists x, f x = y.

  Definition bijective (f : X -> Y) := 
    injective f /\ surjective f.

  Definition is_inverse (f : X -> Y) (g : Y -> X) :=
    (forall x, g (f x) = x) /\
    (forall y, f (g y) = y).

  Definition inverses (f : X -> Y) : Type :=
    { g : Y -> X 
    | is_inverse f g }.

  Lemma inverse (f : X -> Y) :
    bijective f -> inverses f.
  Proof.
    unfold inverses, is_inverse.
    intros [inj sur].
    apply constructive_definite_description.
    assert (H : forall y, exists x, unique (fun x => f x = y) x).
    { intros y.
      destruct (sur y) as [x xP].
      exists x; split; trivial.
      intros x' x'P.
      now apply inj; rewrite xP, x'P. }
    exists (fun y => proj1_sig (constructive_definite_description _ (H y))).
    split.
    - split.
      + intros x.
        destruct (constructive_definite_description _ _).
        simpl. now apply inj.
      + intros y.
        now destruct (constructive_definite_description _ _).
    - intros g' [H1 H2].
      extensionality y.
      destruct (constructive_definite_description _ _) as [x e].
      simpls. now rewrite <- e, H1.
  Qed.

  Lemma inverse_id_left f (Bij : bijective f) :
    forall x,
    (proj1_sig (inverse Bij)) (f x) = x.
  Proof using.
    intros. destruct (inverse Bij).
    unfolds is_inverse. simpls.
    rename x0 into x'. exists* i.
    apply i.
  Qed.

  Lemma inverse_id_right f (Bij : bijective f) :
    forall x,
    f ((proj1_sig (inverse Bij)) x) = x.
  Proof using.
    intros. destruct (inverse Bij). simpls.
    unfolds is_inverse.
    rename x0 into x'. exists* i.
    apply i0.
  Qed.

End Bijection.

Section BijectionProperties.

  Variable X Y Z : Type.

  Lemma inverse_bijective (f : X -> Y) (Bij : bijective f) :
    bijective (proj1_sig (inverse Bij)).
  Proof using.
    unfolds bijective, injective, surjective.
    destruct (inverse Bij) as (g&(Inv1&Inv2)). simpls.
    destruct Bij as (Inj&Surj).
    splits; intros.
    - sort. dup_hyp Inv2. specializes Inv0 x.
      specializes Inv2 y. rewrite H in Inv0.
      now rewrite <- Inv0, Inv2.
    - specializes Inj y. now exists (f y).
  Qed.

  Lemma bijective_compose (f : X -> Y) (g : Y -> Z) :
    bijective f ->
    bijective g ->
    bijective (g ∘ f).
  Proof using.
    unfolds bijective, injective, surjective.
    intros (Fi&Fs) (Gi&Gs). splits; intros.
    - now apply Fi, Gi.
    - specializes Gs y. exists* Gs.
      specializes Fs x. exists* Fs.
      subst. exists~.
  Qed.

  Lemma inverse_unique (f : X -> Y) (Bij : bijective f) :
    forall g g',
    is_inverse f g ->
    is_inverse f g' ->
    g = g'.
  Proof using.
    unfold is_inverse. introv (Inv1&Inv2) (Inv1'&Inv2').
    sort. extensionality y.
    destruct Bij. specializes H0 y.
    exists* H0. subst.
    now rewrite Inv1, Inv1'.
  Qed.


End BijectionProperties.

Module Star.

  Definition star {T T' : Type} (f : T -> [T']) : [T] -> [T'] :=
    fun S =>
    fun t' =>
    exists t,
    S t /\ f t t'.

  Notation "f '★'" := (star f) (at level 5, format "f ★").

  Definition compose_sub {A : Type} (g f : A -> [A]) : A -> [A] :=
    g★ ∘ f.

  Notation " g '[∘]' f " := (g★ ∘ f)
    (at level 40, left associativity).

  Lemma star_distr :
    forall T T' T'' (f : T -> [T']) (g : T' -> [T'']),
    g★ ∘ f★ =
    (g★ ∘ f)★.
  Proof using.
    intros. unfold star.
    do 2 (apply functional_extensionality; intro).
    apply prop_ext. splits; intros.
    all: exists* H.
    - exists t0. splits~. exists~ t.
    - exists t0. splits~. exists~ t.
  Qed.

  Corollary star_distr_2 :
    forall T (f g : T -> [T]),
    g★ ∘ f★ =
    (g [∘] f)★.
  Proof using.
    intros. apply star_distr.
  Qed.

  Lemma star_monotone :
    forall T (f g : T -> [T]),
    (forall x, f x ⊆ g x) -> 
    forall A, f★ A ⊆ g★ A.
  Proof using.
    unfold star, subset. intros.
    exists* H0. exists t. splits~.
  Qed.

  Lemma star_single :
    forall T (f : T -> [T]) t,
    f t = f★ (fun t' => t = t').
  Proof using.
    intros. apply functional_extensionality. intro t'.
    apply prop_ext. unfold star. splits; intros.
    - exists~ t.
    - exists* H. subst~.
  Qed.

  Lemma star_empty :
    forall T (f : T -> [T]),
    f★ ∅ = ∅.
  Proof using.
    intros. unfolds.
    apply functional_extensionality. intro.
    rewrite eq_prop_eq_iff. splits; intros.
    - now exists* H.
    - easy.
  Qed.

  Definition star_prop {T : Type} (P : [T]) : [[T]] :=
    fun X =>
    forall t,
    X t -> P t.

    
  Lemma star_yields_empty :
    forall {T T' : Type} (f : T -> [T']) C,
    f★ C = ∅ <->
    (C <> ∅ ->
    forall h,
    C h -> f h = ∅).
  Proof using.
    intros. splits; intros.
    - clear H0. contra H. apply not_emptyset.
      apply not_emptyset in H. exists* H.
      unfold star. exists~ t h.
    - either (C = ∅).
      + subst. apply functional_extensionality.
        intro. apply prop_ext. splits; intros.
        * unfolds in H0. now exists* H0.
        * easy.
      + specializes H H0.
        apply functional_extensionality. intro.
        rewrite emptyset_false, prop_eq_False_eq.
        intro. unfolds in H1. exists* H1.
        apply H in H1. now rewrite H1 in H2.
  Qed.


End Star.

Export Star.


Section EquivRelations.

  Variable T : Type.
  Variable R : binary T.

  Definition is_equiv_class (S : [T]) :=
    (exists t, S t) /\
    forall t t', S t -> (R t t' <-> S t').

  Definition quotient (E : equiv R) : Type :=
    { S : [T] | is_equiv_class S }.

  Variable E : equiv R.

  Lemma equiv_class_inhabit (Q : quotient E) :
    exists t, (proj1_sig Q) t.
  Proof using.
    destruct Q. unfolds in i.
    exists* i. simpls. exists~ t.
  Qed.

  (* Get a representative element from an equivalence class *)
  Definition equiv_class_repr (Q : quotient E) :=
    indefinite_description (equiv_class_inhabit Q).

  Lemma canon_project_is_equiv_class :
    forall t,
    is_equiv_class (R t).
  Proof using E.
    intro. unfolds. splits.
    exists t. apply~ equiv_refl.
    intros. splits; intros.
    - eapply equiv_trans. easy. apply H. apply H0.
    - eapply equiv_trans. easy. apply equiv_sym. easy.
      apply H. apply H0.
  Qed.

  Definition canon_project (t : T) : quotient E :=
    exist _ (R t) (canon_project_is_equiv_class t).

  Lemma equiv_class_same (Q Q' : quotient E) :
    forall t t',
    R t t' ->
    (proj1_sig Q) t ->
    (proj1_sig Q') t' ->
    Q = Q'.
  Proof using.
    intros. destruct Q as (?&(?&?)&?), Q' as (?&(?&?)&?).
    simpls. apply exist_eq_exist.
    extensionality k.
    apply prop_ext. splits; intros.
    - specializes i k H0. specializes i0 k H1.
      apply i in H2. apply i0.
      applys~ equiv_trans. apply~ equiv_sym.
      apply H. auto.
    - specializes i k H0. specializes i0 k H1.
      apply i. apply i0 in H2.
      applys~ equiv_trans. apply H. auto.
  Qed.

  Corollary equiv_class_eq (Q Q' : quotient E) :
    forall x,
    (proj1_sig Q) x ->
    (proj1_sig Q') x ->
    Q = Q'.
  Proof using.
    intros. apply equiv_class_same with (t:=x) (t':=x); auto.
    now apply equiv_refl.
  Qed.

End EquivRelations.



Module UnivSet.

  Definition univ_set {T : Type} : [T] :=
    fun (_ : T) => True.

  Notation "⬤" := univ_set.

  Lemma univ_set_true {T} (t : T) :
    ⬤ t = True.
  Proof using.
    auto.
  Qed.

End UnivSet.

Export UnivSet.




Section FmapDifferenceDefinition.

  Variables (A B : Type).
  Implicit Types f : map A B.

  Definition map_diff f1 f2 : map A B :=
    fun (x:A) =>
    match f2 x with
    | Some _ => None
    | _ => f1 x
    end.

  Definition list_diff (L1 L2 : list A) : list A :=
    LibList.filter (fun x => isTrue (~ mem x L2)) L1.

  Lemma map_diff_finite f1 f2 :
    map_finite f1 ->
    map_finite f2 ->
    map_finite (map_diff f1 f2).
  Proof using.
    intros (L1&F1) (L2&F2). exists L1.
    intros. unfolds map_diff.
    destruct (f2 x) eqn:E; try easy.
    now apply F1.
  Qed.

  Definition diff (h1 h2 : fmap A B) : fmap A B :=
    let (f1,fin1) := h1 in
    let (f2,fin2) := h2 in
    make (map_diff f1 f2) (map_diff_finite fin1 fin2).
  
  Definition diff_set (C : [fmap A B]) (h' : fmap A B) :=
    fun k =>
    exists h,
    C h /\
    k = diff h h'.

End FmapDifferenceDefinition.

Notation "h '\-' k" := (diff h k) (at level 35, right associativity) : fmap_scope.

Notation "C \-- k" := (diff_set C k) (at level 40) : fmap_scope.

Notation H := heap.
Implicit Type h : H.

Section HeapDifferenceProperties.

  Open Scope fmap_scope.

  Lemma diff_indom :
    forall h h' p,
    (indom h p /\ ~ indom h' p) <->
    indom (h \- h') p.
  Proof using.
    unfolds indom, map_indom, diff, map_diff.
    intros.
    destruct h as (f&fin), h' as (f'&fin').
    splits.
    - intros (H&H'). simpls. 
      apply none_not_some in H as (?&?).
      rewrite H.
      destruct (f' p); try easy.
      now contradict H'.
    - intros. simpls.
      now destruct (f' p).
  Qed.

  Lemma diff_read :
    forall h h' p,
    indom (h \- h') p ->
    read (h \- h') p = read h p.
  Proof using.
    intros.
    unfolds indom, map_indom, diff, map_diff, read.
    destruct h as (f&fin), h' as (f'&fin'). simpls.
    now destruct (f' p).
  Qed.

  Lemma diff_same h :
    h \- h = Fmap.empty.
  Proof using.
    apply fmap_extens. intros.
    simpls. destruct h as (f&fin).
    simpls. unfold map_diff.
    now destruct (f x).
  Qed.
  
  Lemma diff_union_disjoint h h' :
    disjoint h h' ->
    (h \u h') \- h' = h.
  Proof using.
    intros.
    destruct h as (f&fin), h' as (f'&fin').
    simpls. apply fmap_extens. intros.
    simpls. unfold map_diff, map_union.
    unfolds disjoint, map_disjoint. simpls.
    specializes H x. destruct H.
    - rewrite H. now destruct (f' x).
    - rewrite H. now destruct (f x).
  Qed.
  
  Lemma diff_disjoint h h' :
    disjoint h h' ->
    h \- h' = h.
  Proof using.
    intros.
    destruct h as (f&fin), h' as (f'&fin').
    simpls. apply fmap_extens. intro.
    unfolds disjoint, map_disjoint, map_diff. simpls.
    specializes H x. destruct H.
    - rewrite H. now destruct (f' x).
    - now rewrite H.
  Qed.

  Corollary diff_empty h :
    h \- Fmap.empty = h.
  Proof using.
    apply diff_disjoint, disjoint_empty_r.
  Qed.

  Lemma diff_set_empty C h' :
    C \-- h' = ∅ <->
    C = ∅.
  Proof using.
    unfold diff_set. splits; intros.
    - pose proof I. contra H0.
      rewrite not_emptyset in H0. exists* H0.
      apply equal_f with (t \- h') in H.
      rewrite eq_prop_eq_iff in H. exists* H.
      destruct H. exists t. splits~.
    - subst. extensionality k.
      rewrite emptyset_false, prop_eq_False_eq.
      intro. now exists* H.
  Qed.

  Lemma diff_of_empty h' :
    empty \- h' = empty.
  Proof using.
    apply fmap_extens. intros.
    simpls. destruct h'.
    simpls. unfold map_diff.
    now destruct fmap_data.
  Qed.
  
  Lemma diff_set_of_empty h' :
    ∅ \-- h' = ∅.
  Proof using.
    extensionality h. apply prop_ext.
    splits; intros.
    - unfolds in H. now exists* H.
    - easy.
  Qed.


  Lemma diff_set_single h h' :
    eq h \-- h' = eq (h \- h').
  Proof using.
    extensionality k.
    apply prop_ext. splits; intros.
    - unfolds diff_set. exists* H.
      now subst.
    - unfolds diff_set. now exists h.
  Qed.


End HeapDifferenceProperties.



Lemma eq_eq_eq {T} (a b : T) :
  (eq a) = (eq b) ->
  a = b.
Proof using.
  intros. apply equal_f with a in H.
  rewrite eq_prop_eq_iff in H.
  now apply eq_sym, H.
Qed.

Lemma disj_idempotent P :
  P \/ P <-> P.
Proof using.
  splits; intros; auto.
  destruct~ H.
Qed.


Lemma subset_eq_mem {T} (C : [T]) x :
  eq x ⊆ C <->
  C x.
Proof using.
  splits; intros.
  - now apply H.
  - introv ?. now subst.
Qed.

Lemma remove_union_r h h' p :
  ~ indom h p ->
  remove (h \u h') p = h \u remove h' p.
Proof using.
  intros. apply fmap_extens. intros.
  destruct h, h'. simpls.
  unfold map_remove. case_if.
  2: {
    unfold map_union. destruct fmap_data eqn:E; auto.
    now case_if.
  }
  subst. unfold map_union.
  destruct fmap_data eqn:E.
  2: { now case_if. }
  unfolds indom, map_indom.
  contra H. intro. simpls.
  now rewrite E in H0.
Qed.


Lemma eq_emptyset {T} (P : [T]) :
  (forall x, ~ P x) ->
  P = ∅.
Proof using.
  intros. extensionality x.
  rewrite emptyset_false.
  rewrite prop_eq_False_eq.
  now apply H.
Qed.


Lemma disjoint_remove h h' p :
  disjoint h h' ->
  disjoint (remove h p) h'.
Proof using.
  intros. intro.
  unfold remove. simpls. unfolds map_remove.
  either (x=p). subst.
  left. rewrite~ If_l.
  rewrite~ If_r.
Qed.

Lemma remove_union_l h h' p :
  indom h p ->
  disjoint h h' ->
  remove (h \u h') p = remove h p \u h'.
Proof using.
  intros. rewrite~ union_comm_of_disjoint.
  rewrite~ remove_union_r.
  rewrite~ union_comm_of_disjoint.
  rewrite disjoint_comm. apply~ disjoint_remove.
  intro. applys disjoint_inv_not_indom_both. apply H0.
  apply H. auto.
Qed.



Section TMap.

Variable A B : Type.

Definition tmap : Type := A -> B.

Implicit Type a : A.
Implicit Type b : B.
Implicit Type m : tmap.

Definition upd m a b :=
  fun a' => If a = a' then b else m a'.

Notation "m '[' a '=' b ']'" := (upd m a b) 
  (left associativity, at level 10, a at level 5, b at level 5).

(*Notation "m '[' a1 '=' b1 ',' a2 '=' b2 ',' a3 '=' b3 ']'" := 
  (m[a1=b1][a2=b2][a3=b3])
  (left associativity, at level 10).*)

Lemma upd_shadow1 m (a:A) (b b':B) :
  m[a=b][a=b'] = m[a=b'].
Proof using.
  unfolds upd. extensionality x'.
  case_if~.
Qed.

Lemma upd_shadow2 m a a' c b b' :
  m[a=b][a'=c][a=b'] = m[a'=c][a=b'].
Proof using.
  unfold upd. extensionality x'.
  case_if~.
Qed.

Lemma upd_swap_diff m a a' b b' :
  a <> a' ->
  m[a=b][a'=b'] = m[a'=b'][a=b].
Proof using.
  intros.
  extensionality x''.
  unfolds. case_if~.
  case_if~.
Qed.

Lemma upd_read1 m a b :
  m[a=b] a = b.
Proof using.
  unfolds. case_if~.
Qed.

Lemma upd_read2 m a a' b b' :
  a <> a' ->
  m[a=b][a'=b'] a = b.
Proof using.
  intros.
  unfolds. case_if~. case_if~.
Qed.

Lemma upd_read1_diff m a a' b :
  a <> a' ->
  m[a'=b] a = m a.
Proof.
  intros.
  unfolds.
  case_if~.
Qed.


End TMap.


Notation "m '[' a '=' b ']'" := (upd m a b) 
  (left associativity, at level 10, a at level 5, b at level 5).


(*Ltac simpl_tmap :=
  progress
  repeat match goal with
  | [ |- context[(?m[?a=(?b)][?a=(?b')])] ] =>
    rewrite upd_shadow1
  | [ H : context[(?m[?a=(?b)][?a=(?b')])] |- _ ] =>
    rewrite upd_shadow1 in H
  | [ |- context[(?m[?a=(?b)][][?a=(?b')])] ] =>
    rewrite upd_shadow1
  end.*)