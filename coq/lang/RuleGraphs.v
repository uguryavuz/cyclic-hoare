Set Implicit Arguments.
From Lang Require Export Util.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require FSetList FSetFacts FSetProperties.

Module Node <: UsualOrderedType.
  Include Nat_as_OT.
End Node.

Notation node := Node.t.

Module Import NodeSet := FSetList.Make(Node).
Module NodeSetFacts := FSetFacts.Facts(NodeSet).
Module NodeSetProperties := FSetProperties.Properties(NodeSet).

Section Nodes.

Variable dom : NodeSet.t.

Definition dommem := {nd | NodeSet.In nd dom}.

Definition nodelist := list dommem.

Lemma nodelist_pigeon : 
  forall (l : nodelist),
  length l > cardinal dom ->
  ~ List.NoDup l.
Proof.
  intros. intro.
  assert (List.incl 
    (List.map (@proj1_sig elt (fun nd => NodeSet.In nd dom)) l) 
    (elements dom)
  ). {
    unfolds. intros. sort.
    apply List.in_map_iff in H1.
    exists* H1. destruct x. simpls. subst.
    dup_hyp i.
    rewrite NodeSetFacts.elements_iff in i0.
    apply SetoidList.InA_alt in i0. exists* i0.
    now subst.
  }
  apply (List.NoDup_incl_length) in H1.
  { rewrite cardinal_1 in *.
    rewrite List.map_length in H1.
    rewrite length_datatypes_length in H.
    contradict H. now rewrite ngt_as_le. }
  destruct l.
  { simpls. apply List.NoDup_nil. }
  apply List.NoDup_cons.
  { intro. simpls.
    apply List.NoDup_cons_iff in H0 as (?&?).
    contradict H0.
    apply List.in_map_iff in H2. exists* H2.
    apply eq_sig_hprop in H2. subst~.
    intros. apply proof_irrelevance. }
  apply nodup_inj.
  2: { now apply List.NoDup_cons_iff in H0 as (?&?). }
  unfolds. intros.
  apply eq_sig_hprop; auto.
  intros. apply proof_irrelevance.
Qed.

Lemma nodelist_pigeon' : 
  forall (l : nodelist),
  List.NoDup l ->
  length l <= cardinal dom.
Proof.
  intros. contra H.
  apply nodelist_pigeon. math.
Qed.

Fact nodelist_all_elems :
  forall (l : nodelist),
  length l = cardinal dom ->
  List.NoDup l ->
  forall (x:dommem),
  List.In x l.
Proof.
  intros. destruct x as (e&Ie). sort.
  rewrite cardinal_1 in H.
  assert (List.incl (elements dom)
    (List.map (@proj1_sig elt (fun nd => NodeSet.In nd dom)) l)).
  {
    apply List.NoDup_length_incl.
    - apply nodup_inj; auto.
      unfolds. intros.
      apply eq_sig_hprop in H1. subst~.
      intros. apply proof_irrelevance.
    - rewrite <- H, List.map_length, length_datatypes_length.
      auto.
    - unfolds. intros. sort.
      apply List.in_map_iff in H1.
      exists* H1. destruct x. simpls. subst.
      dup_hyp i.
      rewrite NodeSetFacts.elements_iff in i0.
      apply SetoidList.InA_alt in i0. exists* i0.
      now subst.
  }
  specializes H1 e. specializes H1.
  { apply elements_1 in Ie.
    apply SetoidList.InA_alt in Ie.
    exists* Ie. subst~. }
  apply List.in_map_iff in H1.
  exists* H1. destruct x. simpls.
  subst. replace Ie with i.
  auto. apply proof_irrelevance.
Qed.

End Nodes.

Definition proj_into_subdom
  (dom:t) (e:elt) (e':dommem dom) (H:e <> proj1_sig e') : 
    dommem (remove e dom) :=
  exist (fun e' => In e' (remove e dom)) (proj1_sig e') 
    (@remove_2 dom e (proj1_sig e') H (proj2_sig e')).

Variable stmt : Type.
Variable liftable : stmt -> Prop.
Variable valid_stmt : stmt -> Prop.

Variable rule : Type.
Variable valid_rule : rule -> list stmt -> stmt -> Prop.

Definition sound_rule (r : rule) : Prop :=
  forall (prems : list stmt) (conc : stmt),
    valid_rule r prems conc ->
      List.Forall valid_stmt prems ->
      valid_stmt conc.

Variant rule_or_lift : Type :=
  | Rule (r : rule) 
  | Lift.

Inductive rule_graph : Type := {
  rg_nodes : NodeSet.t;
  rg_node  : Type := {nd | NodeSet.In nd rg_nodes};
  rg_conc  : rg_node -> stmt;
  rg_rule  : rg_node -> rule_or_lift;
  rg_prems : rg_node -> list rg_node;
  rg_wf    : forall nd : rg_node, 
              match rg_rule nd with
              | Rule r => valid_rule r (List.map rg_conc (rg_prems nd)) (rg_conc nd)
              | Lift => liftable (rg_conc nd) /\ (rg_prems nd) = nil
              end
}.

Section RuleGraph.

Variable rg : rule_graph.

Notation rg_node := rg.(rg_node).

Definition rules_in_graph_sound :=
  forall rule, 
  (exists nd, @rg_rule rg nd = Rule rule) -> 
  sound_rule rule.

Definition valid_rule_graph : Prop :=
  forall (nd : rg_node), 
    match rg_rule nd with
    | Lift => valid_stmt (rg_conc nd)
    | _ => True
    end.

Fixpoint is_path (p : list rg_node) : Prop :=
  match p with
  | nd1 :: p => 
    match p with 
    | nd2 :: p' => List.In nd2 (rg_prems nd1) /\ is_path p
    | _ => True
    end
  | _ => True
  end.

Definition path : Type := 
  {p : list rg_node | is_path p}.

Section PathAppending.

Theorem path_appending : forall (p p' : path),
  ListFacts.last (proj1_sig p) = ListFacts.first (proj1_sig p') ->
  is_path ((proj1_sig p) ++ List.tl (proj1_sig p')).
Proof.
  intros.
  destruct p as [p Hp].
  destruct p' as [p' Hp'].
  simpl in *.
  induction p.
  - simpl in H. destruct p'. auto. discriminate.
  - destruct p.
    + simpl in IHp.
      assert (H1 : ([a] ++ List.tl p')%list = p'). {
        destruct p'.
        discriminate.
        simpl in *.
        injects H.
        auto.
      }
      rewrite H1.
      auto.
    + destruct Hp.
      assert (H3 : last (r :: p) = first p') by auto.
      assert (H4 : is_path ((r :: p) ++ List.tl p')) by auto.
      assert (H5 : ((a :: r :: p) ++ List.tl p' = a :: r :: p ++ List.tl p')%list) by auto.
      rewrite H5.
      simpl in *.
      auto.
Qed.

Definition path_append (p p' : path) 
    (H : ListFacts.last (proj1_sig p) = ListFacts.first (proj1_sig p')) : path :=
  exist _ ((proj1_sig p) ++ List.tl (proj1_sig p'))%list (path_appending p p' H).

Fact empty_path_is_path : is_path ([]%list).
Proof. now simpl. Qed.

Definition empty_path : path := 
  exist _ [] empty_path_is_path.

Lemma is_path_single : 
  forall (nd : rg_node),
    is_path ([nd])%list.
Proof.
  intros.
  now simpl.
Qed.

Definition single_path (nd : rg_node) : path :=
  exist _ _ (is_path_single nd).

Lemma path_decomposing : forall (nl1 nl2 : list rg_node),
  is_path (nl1 ++ nl2)%list ->
  is_path nl1 /\ is_path nl2.
Proof.
  intros; split.
  - induction nl1.
    apply empty_path_is_path.
    rewrite app_cons_l in H.
    destruct (nl1 ++ nl2)%list eqn:Hnl.
    + assert (H1 : nl1 = []). {
        destruct nl1; auto. discriminate.
      }
      rewrite H1.
      apply is_path_single.
    + destruct H.
      destruct nl1.
      apply is_path_single.
      replace r0 with r in * by now inverts Hnl.
      specialize (IHnl1 H0).
      unfold is_path.
      auto.
  - induction nl1.
    now rewrite app_nil_l in H.
    rewrite app_cons_l in H.
    destruct (nl1 ++ nl2)%list eqn:Hnl.
    + destruct nl2.
      apply empty_path_is_path.
      contradict Hnl.
      destruct nl1; discriminate.
    + unfold is_path in H.
      destruct H.
      auto.
Qed.

End PathAppending.

Section Reaches.

Definition reaches (nd1 nd2 : rg_node) : Prop :=
  exists (p : path),
    let nodelist := proj1_sig p in
      ListFacts.first nodelist = Some nd1 /\
      ListFacts.last nodelist = Some nd2.

Lemma reaches_refl : forall nd, reaches nd nd.
Proof.
  intros.
  unfold reaches.
  assert (H : is_path ([nd]%list)) by (now unfold is_path).
  exists (exist _ _ H).
  assert (H_NE : [nd]%list <> []) by discriminate.
  split; auto.
Qed.

Lemma reaches_trans nd1 nd2 nd3 :
  reaches nd1 nd2 ->
  reaches nd2 nd3 ->
  reaches nd1 nd3.
Proof.
  intros.
  unfolds reaches. exists* H, H0.
  rewrite <- H0 in H1.
  exists (path_append _ _ H1).
  destruct p, p0. simpls. splits.
  - rewrite~ first_append. intro.
    subst. discriminate.
  - destruct x0. discriminate.
    simpl in H0. injects H0.
    destruct x0.
    + simpls. rewrite app_nil_r.
      now transitivity (Some nd2).
    + simpl. rewrite last_append. 2: discriminate.
      rewrite <- H2.
      remember (r::x0) as l.
      simpl. rewrite~ Heql.
Qed.


End Reaches.

Section LoopingNodelists.

Definition looping_nodelist (p : list rg_node) : Prop :=
  ListFacts.last p = ListFacts.first p.

Fixpoint iterated_looping_nodelist (p : list rg_node) (H : looping_nodelist p) (n : nat) : list rg_node :=
  match n with
  | O     => p
  | S n'  => (@iterated_looping_nodelist p H n') ++ List.tl p
  end.

Lemma iterated_looping_nodelist_loops : 
  forall (p : list rg_node) (H : looping_nodelist p) (n : nat),
    looping_nodelist (iterated_looping_nodelist H n).
Proof.
  intros.
  destruct n as [| n']. 
  simpl; now unfold looping_nodelist.
  simpl.
  induction n'; simpl.
  - unfold looping_nodelist in *.
    destruct p as [| hd tl] eqn:Hp; auto.
    assert (H1 : p <> []) by (now rewrite Hp).
    rewrite <- Hp in *.
    rewrite first_append; auto.
    destruct tl as [| hd' tl'] eqn:Htl.
    rewrite Hp; simpl; now rewrite LibList.app_nil_r.
    rewrite <- Htl in *.
    assert (H2 : tl <> []) by (now rewrite Htl).
    assert (H3 : List.tl p = tl). {
      unfold List.tl.
      destruct p.
      contradiction.
      now inversion Hp.
    }
    rewrite H3.
    clear H3.
    clear Htl.
    rewrite last_append; auto.
    assert (H4 : last p = last tl). {
      unfold last at 1.
      destruct p. contradiction. inverts Hp.
      simpl in *.
      destruct tl. contradiction.
      auto.
    }
    rewrite <- H4.
    auto.
  - unfold looping_nodelist in *.
    destruct p as [| hd tl].
    + rewrite LibList.app_nil_r.
      rewrite LibList.app_nil_r in *.
      auto.
    + unfold List.tl in *.
      destruct tl as [| hd' tl']; 
        [rewrite LibList.app_nil_r; now rewrite LibList.app_nil_r in * |].
      remember (hd' :: tl') as tl.
      assert (H1 : tl <> []) by (now rewrite Heqtl).
      rewrite last_append in *; try auto.
      remember (iterated_looping_nodelist H n') as l.
      clear Heql.
      destruct l. 
      rewrite LibList.app_nil_l in *.
      rewrite first_append; auto.
      remember ((r :: l) ++ tl)%list as l'.
      rewrite first_append in *; try auto.
      now rewrite Heql'.
Qed.

Lemma iterated_looping_nodelist_share_endpoints : 
  forall (p : list rg_node) (H : looping_nodelist p) (n : nat),
    ListFacts.first p = ListFacts.first (iterated_looping_nodelist H n) /\
    ListFacts.last p = ListFacts.last (iterated_looping_nodelist H n).
Proof.
  intros.
  destruct p as [| hd tl] eqn:Hp.
  - induction n as [| n']; auto.
    destruct IHn' as [H1 H2].
    simpl in *.
    rewrite LibList.app_nil_r in *.
    split; auto.
  - induction n as [| n']; [auto|].
    destruct IHn' as [H1 H2].
    split.
    + simpl.
      rewrite first_append; auto.
      destruct n'; [simpl; discriminate|].
      simpl.
      destruct tl as [| hd' tl'] eqn:Htl.
      * simpl in *.
        rewrite LibList.app_nil_r in *.
        remember (iterated_looping_nodelist H n') as l.
        destruct l; [unfold first in H1|]; discriminate.
      * remember (iterated_looping_nodelist H n') as l.
        destruct l; [rewrite LibList.app_nil_l|]; discriminate.
    + destruct tl as [|hd' tl']; [simpl; now rewrite LibList.app_nil_r|].
      remember (hd' :: tl') as tl.
      assert (H3 : last (hd :: tl) = last tl). {
        unfold last.
        destruct tl; [simpl in *; discriminate|].
        auto.
      }
      rewrite H3.
      simpl.
      rewrite last_append; [auto | rewrite Heqtl; discriminate].
Qed.

Lemma iterated_looping_nodelist_length : 
  forall (p : list rg_node) (H : looping_nodelist p) (n : nat),
    length (iterated_looping_nodelist H n) = ((length p) + n * (length (List.tl p)))%nat.
Proof.
  intros.
  induction n as [| n']; [simpl; math|].
  remember (iterated_looping_nodelist H n') as l.
  simpl.
  rewrite LibList.length_app.
  rewrite <- Heql.
  remember (List.tl p) as tl.
  rewrite IHn'.
  math.
Qed.

End LoopingNodelists.

Section LoopingPaths.

Definition looping_path (p : path) : Prop :=
  looping_nodelist (proj1_sig p).

Lemma iterated_looping_path_is_path : 
  forall (p : path) (H : looping_path p) (n : nat),
    is_path (iterated_looping_nodelist H n).
Proof.
  intros.
  induction n as [| n']; [destruct p; now simpl|].
  remember (iterated_looping_nodelist H n') as l.
  destruct p as [p Hp].
  simpl.
  assert (H0 : (iterated_looping_nodelist H n' ++ List.tl p = l ++ List.tl p)%list). {
    apply ListFacts.append_equals.
    now symmetry.
  }
  assert (H1 : is_path (List.tl p)). {
    induction p; auto.
    unfold List.tl.
    simpl in Hp.
    destruct p; auto.
    now destruct Hp as [H1 H2].
  }
  assert (H2 : is_path (l ++ List.tl p)%list). { 
    remember (exist _ l IHn') as l_path.
    assert (H3 : l = (proj1_sig l_path)) by (rewrite Heql_path; auto).
    rewrite H3.
    remember (exist _ p Hp) as p_path.
    assert (H4 : p = (proj1_sig p_path)) by (rewrite Heqp_path; auto).
    rewrite H4.
    apply path_appending.
    clear H1 H0.
    rewrite Heql_path.
    rewrite Heqp_path.
    simpl.
    pose proof iterated_looping_nodelist_loops H n' as G0.
    unfold looping_nodelist in G0.
    rewrite <- Heql in G0.
    pose proof H as G1.
    unfold looping_path in G1.
    unfold looping_nodelist in G1.
    rewrite Heqp_path in G1.
    simpl in G1.
    pose proof (iterated_looping_nodelist_share_endpoints H n') as G2.
    rewrite <- Heql in G2.
    rewrite Heqp_path in G2.
    simpl in G2.
    destruct G2 as [G2 G3].
    symmetry.
    rewrite G0.
    apply G2.
  }
  rewrite Heql in H2.
  auto.
Qed.
  
Definition iterated_looping_path (p : path) (H : looping_path p) (n : nat) : path :=
  let nodelist := proj1_sig p in
    exist _ (iterated_looping_nodelist H n) (iterated_looping_path_is_path H n).

End LoopingPaths.

Section Cycles.

Definition is_cyclic_path (p : path) : Prop :=
  let nodelist := proj1_sig p in
    looping_nodelist nodelist /\
    List.NoDup (List.tl nodelist) /\
    (length nodelist > 1)%nat.

Definition is_cyclic_rule_graph : Prop :=
  exists (p : path), is_cyclic_path p.

Lemma cyclic_graph_implies_longer_path_exists : 
  is_cyclic_rule_graph ->
  forall (p : path), 
    exists (p' : path), 
      length (proj1_sig p') > length (proj1_sig p).
Proof.
  intros.
  destruct p as [p Hp].
  simpl.
  destruct p as [| hd tl] eqn:Hpdef.
  + rewrite LibList.length_nil.
    unfold is_cyclic_rule_graph in H.
    destruct H as [cyclic_path Hcyc].
    destruct Hcyc as [H1 [H2 H3]].
    exists cyclic_path.
    math.
  + rewrite <- Hpdef.
    assert (H1 : (length p > 0)%nat). {
      rewrite Hpdef.
      rewrite LibList.length_cons.
      math.
    }
    remember (length p) as n.
    unfold is_cyclic_rule_graph in H.
    destruct H as [cyclic_path Hcyc].
    destruct Hcyc as [H2 [H3 H4]].
    exists (@iterated_looping_path cyclic_path H2 n).
    simpl.
    rewrite iterated_looping_nodelist_length.
    destruct cyclic_path.
    clear H2 H3 Hpdef Hp hd tl Heqn p.
    simpl in *.
    assert (H2 : (length (List.tl x) > 0)%nat). {
      destruct x.
      rewrite LibList.length_nil in H4; math.
      unfold List.tl; rewrite LibList.length_cons in H4; math.
    }
    remember (length (List.tl x)) as m.
    remember (length x) as k.
    clear Heqm Heqk i x rg.
    destruct n; [math|].
    destruct m; math.
Qed.

Fact path_longer_than_card_has_dupes :
  forall (p : path),
    let nodelist := proj1_sig p in 
      length nodelist > cardinal rg.(rg_nodes) ->
      ~ List.NoDup nodelist.
Proof.
  intros. now apply nodelist_pigeon.
Qed.

Lemma cycle_not_empty p :
  is_cyclic_path p ->
  exists nd1 nd2 p',
  proj1_sig p = nd1::nd2::p'.
Proof.
  intros. destruct H.
  destruct H0. destruct p. simpls.
  destruct x. rewrite length_nil in H1. math.
  destruct x. rewrite length_cons, length_nil in H1. math.
  exists r r0 x. auto.
Qed.

Fact path_with_dupes_helper : 
  forall (n : nat) (p : path),
    let ndlist := proj1_sig p in
      length ndlist < n -> 
      ~ List.NoDup ndlist ->
      exists p1 p2 p3 H1 H2,
        p = path_append (path_append p1 p2 H1) p3 H2 /\
        is_cyclic_path p2.
Proof.
  induction n. math.
  intros.
  assert (H1 : length ndlist <= n) by math.
  apply le_case_eq_lt in H1.
  destruct H1. 2 : now specialize (IHn p H1 H0).
  destruct (classic (is_cyclic_path p)).
  (* Case 1: entire path is simple cycle *)
  { remember (ListFacts.first ndlist) as first_nd.
    remember (ListFacts.last ndlist) as last_nd.
    destruct first_nd. 2 : {
      destruct H2. destruct H3. subst.
      clear H3 H2 H0 IHn H.
      subst ndlist.
      destruct (proj1_sig p).
      rewrite LibList.length_nil in H4. math.
      discriminate.
    }
    destruct last_nd. 2 : {
      destruct H2. destruct H3. subst.
      clear H3 H2 H0 IHn H.
      subst ndlist.
      destruct (proj1_sig p).
      rewrite LibList.length_nil in H4. math.
      contradict Heqlast_nd.
      symmetry.
      apply ListFacts.last_exists.
    }
    exists (single_path r) p (single_path r0).
    assert (last (proj1_sig (single_path r)) = first (proj1_sig p)).
    { subst. subst ndlist. simpls. auto. }
    assert (last (proj1_sig (path_append (single_path r) p H3)) =
        first (proj1_sig (single_path r0))).
    { simpls. rewrite last_append.
      2: {
        destruct p. simpls. destruct x. simpls. discriminate.
        simpls. destruct H2. simpls.
        destruct H4. intro. subst.
        contradict H5. rewrite length_cons.
        rewrite length_nil. math.
      }
      destruct p. simpls. destruct x. simpls. discriminate.
      subst ndlist. simpl.
      rewrite Heqlast_nd. simpls.
      destruct x. simpls. contradict H0.
      apply List.NoDup_cons. auto.
      apply List.NoDup_nil. auto.
    }
    exists H3 H4. split~.
    unfold path_append. simpls.
    subst ndlist. destruct p.
    simpls. apply exist_eq_exist.
    rewrite LibList.app_nil_r.
    rewrite LibList.app_cons_one_r.
    destruct x. discriminate.
    simpls. now injects Heqfirst_nd.
  }
  destruct ndlist as [|hd tl] eqn:Heqn.
  contradict H0. apply List.NoDup_nil.
  rewrite List.NoDup_cons_iff in H0.
  repeat rewrite not_and_eq in H0.
  destruct H0.
  (* Case 2: head of path repeats somewhere *)
  { remember (ListFacts.last tl) as last_nd.
    apply not_not_inv in H0.
    destruct last_nd.
    2: {
      destruct tl. easy.
      contradict Heqlast_nd.
      symmetry. apply last_exists.
    }
    symmetry in Heqlast_nd.
    apply last_app in Heqlast_nd as (l'&?).
    subst tl.
    remember (hd::l') as ndlst'.
    assert (is_path ndlst').
    { subst. subst ndlist.
      destruct p. simpl in Heqn. subst x.
      dup_hyp i. rewrite <- app_cons_l in i0.
      now apply path_decomposing in i0.
    }
    specializes IHn (exist _ _ H3). simpls.
    specializes IHn.
    { subst ndlst'.
      rewrite <- app_cons_l, length_app in H1.
      repeat rewrite length_cons in *. math. }
    { subst ndlist. subst. either (hd = r).
      - subst. contra H2. unfolds. splits.
        + unfolds. rewrite Heqn.
          rewrite <- app_cons_l, last_app'.
          rewrite app_cons_l. simpls~.
        + rewrite Heqn. simpl. clear -H2.
          apply List.NoDup_rev in H2.
          simpl in H2. apply List.NoDup_remove in H2 as (?&?).
          rewrite List.app_nil_r in *.
          rewrite <- List.rev_involutive.
          apply List.NoDup_rev.
          replace (List.rev _) with (r :: List.rev l').
          2: {
            rewrite <- List.rev_unit.
            f_equal. now rewrite app_datatypes_app.
          }
          apply~ List.NoDup_cons.
        + rewrite Heqn. rewrite length_cons.
          rewrite length_app, length_cons. math.
      - intro. apply List.NoDup_cons_iff in H4 as (?&?).
        contradict H4. rewrite app_datatypes_app in H0.
        apply List.in_app_or in H0. destruct~ H0.
        contradict H0. apply List.not_in_cons.
        splits~.
    }
    exists* IHn. sort. subst. subst ndlist.
    assert (is_path (proj1_sig p3 & r)).
    { destruct p as (p&Hp). simpls. subst p.
      apply eq_sig_fst in IHn. dup_hyp Hp.
      rewrite <- app_cons_l, IHn in Hp0. simpls.
      destruct p1 as (p1&?), p2 as (p2&?), p3 as (p3&?).
      simpls. sort. clear H H2 H0 H3 H4 Hp.
      apply cycle_not_empty in IHn0.
      exists* IHn0. simpls.
      assert (exists r, last (p1 ++ List.tl p2) = Some r). {
        rewrite last_append.
        2: { subst. simpls. discriminate. }
        rewrite IHn0. simpl List.tl.
        pose proof last_exists p' nd2.
        now apply none_not_some in H.
      }
      exists* H. sort.
      apply last_app in H as ?.
      exists* H0. sort. rewrite H0 in Hp0.
      rewrite H in H5. destruct p3.
      { simpls. discriminate. }
      simpl in H5. injects H5.
      simpl in Hp0. do 2 rewrite app_assoc in Hp0.
      apply path_decomposing in Hp0 as (?&?).
      rewrite app_cons_one_r in H2. auto.
    }
    destruct p as (p&Hp).
    simpl in Heqn. subst.
    assert (last (proj1_sig p1 ++ List.tl (proj1_sig p2)) =
        first (proj1_sig (exist is_path (proj1_sig p3 & r) H1))). 
    { rewrite H5. simpl.
      destruct p3. simpl. destruct x. simpls.
      { apply cycle_not_empty in IHn0.
        exists* IHn0. destruct p2. subst. simpls.
        subst. simpls. clear IHn.
        rewrite last_append in H5.
        contradict H5. apply last_exists.
        discriminate. }
      rewrite app_cons_l. auto.
    }
    exists p1 p2 (exist _ _ H1) H4 H6.
    splits~.
    apply exist_eq_exist. simpls.
    apply eq_sig_fst in IHn.
    rewrite <- app_cons_l, IHn.
    simpls.
    destruct p1 as (p1&?), p2 as (p2&?), p3 as (p3&?).
    simpls. sort.
    rewrite app_assoc.
    f_equal. destruct p3.
    { simpls. contradict H5.
      assert (List.tl p2 <> []).
      { apply cycle_not_empty in IHn0.
        exists* IHn0. simpls. subst.
        discriminate. }
      rewrite~ last_append.
      { destruct p2. contradiction.
        simpls. destruct p2. contradiction.
        apply last_exists. } }
    simpls. clear.
    rewrite app_cons_l. simpls. auto. }
  (* Case 3: head of path might not repeat somewhere *)
  { assert (H3 : length tl < n).
    { rewrite LibList.length_cons in H1. math. }
    assert (H4 : is_path tl). {
      subst ndlist. destruct p.
      simpls. destruct x. discriminate.
      injects Heqn.
      destruct~ tl.
      simpls. now destruct i.
    } 
    specialize (IHn (exist _ _ H4)).
    simpls.
    specialize (IHn H3 H0).
    exists* IHn. subst ndlist.
    clear H3 H2 H1 H0 H n.
    sort. destruct p as [nl Hp].
    simpls. subst.
    assert (G : is_path (hd :: (proj1_sig p1))). {
      injects IHn.
      rewrite <- app_cons_l in Hp.
      apply path_decomposing in Hp.
      destruct Hp.
      rewrite <- app_cons_l in H.
      now apply path_decomposing in H.
    }
    exists (exist _ _ G) p2 p3.
    assert (last (proj1_sig (exist is_path (hd :: proj1_sig p1) G)) =
          first (proj1_sig p2)).
    { simpl proj1_sig. destruct p1.
      destruct x. simpls.
      { apply cycle_not_empty in IHn0. exists* IHn0.
        clear IHn. rewrite IHn0 in H5.
        simpls. discriminate. }
      simpls. auto. }
    assert (last (proj1_sig (exist is_path (hd :: proj1_sig p1) G) 
          ++ List.tl (proj1_sig p2)) = first (proj1_sig p3)).
    { simpl. apply cycle_not_empty in IHn0.
      exists* IHn0. destruct p2. simpls. subst.
      simpls. clear IHn. rewrite last_append in H6.
      rewrite~ last_append. discriminate.
      discriminate. }
    exists H H0. splits~.
    apply exist_eq_exist. simpls.
    clear G IHn0 Hp.
    rewrite 2!app_cons_l.
    f_equal. injects~ IHn.
  }
Qed.


Fact path_with_dupes_has_cycle :
  forall (p : path),
    let ndlist := proj1_sig p in
      ~ List.NoDup ndlist ->
      exists p1 p2 p3 H1 H2,
        p = path_append (path_append p1 p2 H1) p3 H2 /\
        is_cyclic_path p2.
Proof.
  intros.
  remember (S (length ndlist)) as n.
  assert (H1 : length ndlist < n) by math.
  apply (path_with_dupes_helper p H1 H).
Qed.
 
Lemma longer_path_exists_implies_cyclic_graph : 
  (forall (p : path), 
    exists (p' : path), 
      length (proj1_sig p') > length (proj1_sig p)) ->
  is_cyclic_rule_graph.
Proof.
  intros.
  assert (H_empty : is_path ([])%list) by (now simpl).
  remember (exist _ [] H_empty) as empty_path.
  pose proof H as G.
  specialize (G empty_path).
  rewrite Heqempty_path in G.
  simpl in G.
  rewrite LibList.length_nil in G.
  clear Heqempty_path empty_path H_empty.
  destruct G as [ne_path H_ne].
  assert (H_arb_len_path : forall (n : nat), 
    exists (p : path), length (proj1_sig p) > n). {
    intros.
    induction n as [| n']; [now exists ne_path|].
    destruct IHn' as [p H_p].
    specialize (H p).
    destruct H as [p' H_p'].
    exists p'.
    math.
  }
  clear H_ne ne_path.
  specialize (H_arb_len_path (NodeSet.cardinal rg.(rg_nodes))) as G.
  destruct G as [p H_p].
  unfold is_cyclic_rule_graph.
  apply path_longer_than_card_has_dupes, path_with_dupes_has_cycle in H_p.
  exists* H_p.
  now exists p2.
Qed.

Theorem longer_path_exists_iff_cyclic_graph : 
  (forall (p : path), 
    exists (p' : path), 
      length (proj1_sig p') > length (proj1_sig p)) <->
  is_cyclic_rule_graph.
Proof.
  split.
  apply longer_path_exists_implies_cyclic_graph.
  apply cyclic_graph_implies_longer_path_exists.
Qed.

Theorem acyclic_implies_longest_path : 
  ~ is_cyclic_rule_graph ->
  exists (p : path), 
    forall (p' : path), 
      length (proj1_sig p') <= length (proj1_sig p).
Proof.
  intro.
  contra H.
  apply longer_path_exists_iff_cyclic_graph.
  intros.
  rewrite not_exists_eq in H.
  specialize H with p.
  rewrite not_forall_eq in H.
  exists* H.
  exists x.
  math.
Qed.

Definition longest_path (H : ~ is_cyclic_rule_graph) : path :=
  proj1_sig (constructive_indefinite_description _ (acyclic_implies_longest_path H)).

End Cycles.




Lemma cardinal_nonempty :
  forall (nd : rg_node),
  exists n,
  cardinal (rg_nodes rg) = S n.
Proof.
  intros. destruct nd.
  apply Nat.neq_0_r.
  intro. apply NodeSetProperties.cardinal_inv_1 in H.
  now specializes H i.
Qed.


Section Depth.

Variable A : ~ is_cyclic_rule_graph.

Definition max_option (a b : nat?) : nat? :=
  match a, b with
  | Some n1, Some n2 => Some (Nat.max n1 n2)
  | _, _ => None
  end.

Definition depth_fold (l : list nat?) : nat? :=
  List.fold_left max_option l (Some O).

Fixpoint depth_aux (fuel : nat) (nd : rg_node) : nat? :=
  match fuel with 
  | O => None
  | S fuel =>
    let depths := 
      List.map (@depth_aux fuel)
      (rg_prems nd) in
    option_map S (depth_fold depths)
  end.

Definition depth_opt (nd : rg_node) : nat? :=
  @depth_aux (cardinal rg.(rg_nodes)) nd.

Lemma depth_exists (nd:rg_node) :
  exists (n : nat),
  depth_opt nd = Some n.
Proof.

Admitted.

Definition depth (nd:rg_node) :=
  proj1_sig (constructive_indefinite_description _ (depth_exists nd)).

Notation is_prem prem nd := (List.In prem (rg_prems nd)).


Lemma depth_mono (nd:rg_node) :
  forall (prem:rg_node),
  is_prem prem nd ->
  (depth prem < depth nd)%nat.
Proof.

Admitted.


Definition locally_sound P :=
  forall nd, List.Forall P (@rg_prems rg nd) -> P nd.


Lemma depth_induction_aux (P : [rg_node]) (LS : locally_sound P) :
  forall n nd,
  (depth nd < n)%nat ->
  P nd.
Proof.
  induction n.
  { intros. math. }
  intros. apply LS, List.Forall_forall.
  intros prem HP. sort.
  apply~ IHn.
  pose proof @depth_mono nd prem HP.
  math.
Qed.


Theorem depth_induction (P : [rg_node]) (LS : locally_sound P) :
  forall nd, P nd.
Proof.
  intros.
  pose proof @depth_induction_aux P LS (depth nd).
  apply LS, List.Forall_forall.
  intros prem HP. sort.
  apply~ H. apply~ depth_mono.
Qed.

Corollary acyclic_soundness :
  valid_rule_graph ->
  rules_in_graph_sound ->
  forall nd, valid_stmt (@rg_conc rg nd).
Proof.
  intros.
  pose proof @depth_induction (fun nd => valid_stmt (@rg_conc rg nd)).
  specialize H1 with (nd:=nd).
  specializes~ H1. clear nd.
  unfolds. intros.
  unfold rules_in_graph_sound, sound_rule in H0.
  destruct (rg_rule nd) eqn:E.
  2: { specializes H nd. now rewrite E in H. }
  specializes H0 r (List.map (@rg_conc rg) (@rg_prems rg nd)).
  pose proof (@rg_wf rg).
  apply H0.
  + specializes H2 nd. now rewrite E in H2.
  + now apply List.Forall_map.
Qed.

End Depth.

End RuleGraph.

(* A statement is valid if 
   a graph exists where 
   1. all lifted statements in the graph are valid
   2. all rules used in the graph are locally sound
   3. the statement exists somewhere in the graph
*)
Theorem sound_from_acyclic_graph :
  forall (s:stmt),
  (exists (rg:rule_graph),
    valid_rule_graph rg /\ 
    ~ is_cyclic_rule_graph rg /\
    rules_in_graph_sound rg /\
    exists nd, @rg_conc rg nd = s
  ) ->
  valid_stmt s.
Proof.
  intros. exists* H.
  rewrite <- H2.
  apply~ acyclic_soundness.
Qed.


Print Assumptions sound_from_acyclic_graph.




Section DeepestNodelist.

Variable rg : rule_graph.
Notation rg_node := rg.(rg_node).

Definition folder (f : rg_node -> (list rg_node)?) acc prem := 
  match acc with
  | None => None
  | Some longest_list => 
    match f prem with
    | None => None
    | Some cand_list => 
      If (length cand_list > length longest_list) 
        then Some cand_list
        else Some longest_list
    end
  end.

Definition folder_aux (f : rg_node -> (list rg_node)?) (nd : rg_node) :=
  List.fold_left (folder f) (rg_prems nd).

Fixpoint deepest_nodelist_aux (fuel : nat) (nd : rg_node) {struct fuel} : (list rg_node)? :=
  match fuel with
  | O => None
  | S fuel => 
    match folder_aux (deepest_nodelist_aux fuel) nd (Some nil) with
    | None => None
    | Some l => Some (nd :: l)
    end
  end.

Definition deepest_nodelist (nd : rg_node) : (list rg_node)? :=
  @deepest_nodelist_aux (cardinal rg.(rg_nodes)) nd.

Lemma folding_with_none_yields_none : 
  forall f l,
    List.fold_left (folder f) l None = None.
Proof.
  induction l.
  intros.
  now simpl.
  simpl.
  apply IHl.
Qed.

Lemma folding_with_some_yields_some :
  forall f l l1 l2,
    List.fold_left (folder f) l (Some l1) <> None ->
    List.fold_left (folder f) l (Some l2) <> None.
Proof.
  induction l.
  intros.
  simpl.
  discriminate.
  intros l1 l2.
  simpls.
  destruct (f a). 2 : trivial.
  intro.
  case_if; case_if~; applys IHl H.
Qed.

Lemma folding_shadow :
  forall f l l1 l2 rl1 rl2,
    length l1 >= length l2 ->
    List.fold_left (folder f) l (Some l1) = Some rl1 ->
    List.fold_left (folder f) l (Some l2) = Some rl2 ->
    rl1 = l1 \/ rl1 = rl2.
Proof.
  induction l.
  intros.
  simpls.
  injects~ H0.
  intros.
  simpls.
  destruct (f a).
  2 : {
    now rewrite folding_with_none_yields_none in H0.
  }
  case_if; case_if; try math.
  + rewrite H0 in H1; injects~ H1.
  + specialize (IHl l1 l0 rl1 rl2).
    specializes~ IHl. math.
  + applys IHl H H0 H1.
Qed.

Definition sub {T:Type} (l l' : list T) :=
  forall a, List.In a l -> List.In a l'.

Lemma folder_prem_mem :
  forall fuel nd l,
  sub l (rg_prems nd) ->
  match List.fold_left (folder (deepest_nodelist_aux fuel)) l (Some nil) with
  | None => True
  | Some l' =>
    match l' with
    | nil => True
    | a::l'' => List.In a (rg_prems nd) /\ 
      deepest_nodelist_aux fuel a = Some (a::l'')
    end
  end.
Proof.
  induction fuel.
  { intros. simpls. destruct~ l. simpls~.
    simpls. now rewrite folding_with_none_yields_none. }
  intros nd.
  induction l; intros.
  { simpls~. }
  specializes IHl.
  { intros ??. now apply H, List.in_cons. }
  

  remember (List.fold_left _ (a::l) _) as lf.
  destruct~ lf.
  simpl in Heqlf.
Admitted.


Lemma deepest_nodelist_aux_is_path :  
  forall (fuel : nat) (nd : rg_node),
    match deepest_nodelist_aux fuel nd with
    | None => True
    | Some ndlist => is_path ndlist
    end.
Proof.
  induction fuel.
  { now simpls. }
  intro. simpls.
  unfold folder_aux.
  pose proof @folder_prem_mem fuel nd (rg_prems nd).
  specializes H. { intro. auto. }
  destruct (List.fold_left _ _ _) eqn:E; auto.
  destruct~ l. destruct H.
  simpls. splits~.
  specializes IHfuel r. now rewrite H0 in IHfuel.
Qed.



Lemma deepest_nodelist_aux_is_path_helper :
  forall (max_depth : nat) (fuel : nat) (nd : rg_node),
    match deepest_nodelist_aux fuel nd with
    | None => True
    | Some ndlist => length ndlist < max_depth -> is_path ndlist
    end.
Proof.
  induction max_depth.
  intros.
  destruct (deepest_nodelist_aux _ nd). math. trivial.
  induction fuel.
  intros.
  simpls~.
  intros.
  specialize (IHmax_depth (S fuel) nd).
  specialize (IHfuel nd).
  admit.
  (* simpls.
  unfold folder_aux.
  destruct (deepest_nodelist_aux _ nd) eqn:H. 2 : trivial.
  specialize (IHmax_depth fuel nd).
  unfold deepest_nodelist_aux in H.
  now simpl.
  induction fuel.
  intro.
  destruct (deepest_nodelist_aux (S fuel) nd).
  math.
  trivial.
  intro.
  destruct (deepest_nodelist_aux (S fuel) nd).


  intros.
  simpl.
  unfold folder_aux.
  induction (rg_prems nd).
  now simpl.
  simpl.
  specialize (IHfuel a).
  destruct (deepest_nodelist_aux fuel a) eqn:H2.
  2 : { now rewrite folding_with_none_yields_none. }
  case_if.
  clear IHprems_of_nd.
  destruct (List.fold_left _ _ (Some l0)) eqn:H. 2 : trivial.
  pose proof folding_with_some_yields_some.
  specializes H0 l l0 (@nil rg_node).
  specializes H0.
  rewrite H. discriminate.
  apply none_not_some in H0.
  destruct H0.
  rewrite H0 in IHl.
  pose proof (folding_shadow).
  specializes H1 H H0.
  math.
  destruct H1; subst~.
  unfold is_path.
  destruct l0.
  trivial. *)
Admitted.



Lemma deepest_nodelist_exists : 
  forall (nd : rg_node),
    deepest_nodelist nd <> None.
Proof.
  intro.
  contra A.
  unfold deepest_nodelist in A.
  destruct ((cardinal (rg_nodes rg))); simpl in *.
  Search (LibList.mem _ _ -> LibList.mem _ _).





End DeepestNodelist.
