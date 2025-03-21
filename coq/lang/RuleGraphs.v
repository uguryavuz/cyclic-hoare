Set Implicit Arguments.
From Lang Require Import Util.
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

Module Type ProofSystem.
  Parameter stmt : Type.
  Parameter liftable : stmt -> Prop.
  Parameter valid_stmt : stmt -> Prop.
  Parameter rule : Type.
  Parameter valid_rule : rule -> list stmt -> stmt -> Prop.
End ProofSystem.

Module RuleGraph(PS : ProofSystem).

Include PS.

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

Section RuleGraphInstance.

Variable rg : rule_graph.

Notation rg_node := rg.(rg_node).

Definition rules_in_graph_sound :=
  forall rule, 
  (exists nd, @rg_rule rg nd = Rule rule) -> 
  sound_rule rule.

Definition graph_lift_valid : Prop :=
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

Definition cyclic : Prop :=
  exists (p : path), is_cyclic_path p.

Lemma cyclic_graph_implies_longer_path_exists : 
  cyclic ->
  forall (p : path), 
    exists (p' : path), 
      length (proj1_sig p') > length (proj1_sig p).
Proof.
  intros.
  destruct p as [p Hp].
  simpl.
  destruct p as [| hd tl] eqn:Hpdef.
  + rewrite LibList.length_nil.
    unfold cyclic in H.
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
    unfold cyclic in H.
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
  cyclic.
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
  unfold cyclic.
  apply path_longer_than_card_has_dupes, path_with_dupes_has_cycle in H_p.
  exists* H_p.
  now exists p2.
Qed.

Theorem longer_path_exists_iff_cyclic_graph : 
  (forall (p : path), 
    exists (p' : path), 
      length (proj1_sig p') > length (proj1_sig p)) <->
  cyclic.
Proof.
  split.
  apply longer_path_exists_implies_cyclic_graph.
  apply cyclic_graph_implies_longer_path_exists.
Qed.

Theorem acyclic_implies_longest_path : 
  ~ cyclic ->
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

Definition longest_path (H : ~ cyclic) : path :=
  proj1_sig (constructive_indefinite_description _ (acyclic_implies_longest_path H)).

Lemma cyclic_cardinal :
  cyclic <-> exists (p:path),
  length (proj1_sig p) > cardinal (rg_nodes rg).
Proof.
  splits; intros.
  - destruct H as (p&LN&Dup&?).
    pose proof iterated_looping_nodelist_length LN (S (cardinal (rg_nodes rg))).
    assert (looping_path p) by auto.
    pose proof iterated_looping_path_is_path H1 (S (cardinal (rg_nodes rg))).
    exists (exist _ _ H2). simpls.
    replace H1 with LN by apply proof_irrelevance.
    rewrite H0. remember (length (proj1_sig p)) as l.
    replace (length (List.tl _)) with (pred l).
    2: { 
      destruct p. simpls. subst l. destruct x.
      simpls. rewrite length_nil. math.
      simpls. rewrite length_cons. math. 
    }
    destruct l. simpls. math.
    simpls. destruct l. simpls. math.
    simpls. math.
  - exists* H. apply path_longer_than_card_has_dupes, path_with_dupes_has_cycle in H.
    exists* H. subst. exists~ p2.
Qed.

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

Variable A : ~ cyclic.

Notation is_prem prem nd := (List.In prem (rg_prems nd)).

Definition max_option (a b : nat?) : nat? :=
  match a, b with
  | Some n1, Some n2 => Some (Nat.max n1 n2)
  | _, _ => None
  end.

Definition depth_fold (l : list nat?) : nat? :=
  LibList.fold_left max_option (Some O) l.

Lemma depth_fold_none (l : list nat?) :
  fold_left max_option None l = None.
Proof.
  induction l.
  - intros. apply fold_left_nil.
  - rewrite fold_left_cons.
    destruct a; now simpls.
Qed.   

Lemma depth_fold_some (l : list nat?) :
  forall (n : nat) (acc : nat), 
    (fold_left max_option (Some acc) l) = Some n ->
    List.Forall (<> None) l.
Proof.
  induction l.
  - intros. apply List.Forall_nil.
  - intros.
    constructor.
    + unfold depth_fold in H.
      rewrite fold_left_cons in H.
      contra H.
      subst. 
      simpls.
      rewrite depth_fold_none.
      discriminate.
    + rewrite fold_left_cons in H.
      destruct a; simpls. 2 : now rewrite depth_fold_none in H.
      applys IHl H.
Qed.

Lemma depth_fold_none_in_list (l : list nat?) : 
  forall (acc : nat),
    (fold_left max_option (Some acc) l) = None ->
    List.In None l.
Proof.
  induction l. discriminate.
  destruct a. 2 : now constructor. 
  intros.
  apply List.in_cons.
  rewrite fold_left_cons in H.
  simpls.
  applys IHl H.
Qed.

Lemma depth_bound (l : list nat?) :
  forall (n : nat) (acc : nat),
    (fold_left max_option (Some acc) l) = Some n ->
    acc <= n /\ List.Forall 
      (fun m_opt => 
        match m_opt with 
        | None   => False
        | Some m => m <= n
        end) l.
Proof.
  induction l.
  - intros.
    split. 2: constructor.
    rewrite fold_left_nil in H.
    injects H. math.
  - intros.
    rewrite fold_left_cons in H.
    destruct a. 
    2 : simpls; now rewrite depth_fold_none in H.
    simpls.
    apply IHl in H as [H1 H2].
    split. math.
    constructor; [math | auto].
Qed.

Fixpoint depth_aux (fuel : nat) (nd : rg_node) : nat? :=
  match fuel with 
  | O => None
  | S fuel =>
    let depths := 
      List.map (@depth_aux fuel)
      (rg_prems nd) in
    option_map S (depth_fold depths)
  end.

Lemma depth_aux_decr_fuel (fuel : nat) (nd prem : rg_node) :
  is_prem prem nd ->
  depth_aux (S fuel) nd <> None ->
  depth_aux fuel prem <> None.
Proof.
  intros.
  unfold depth_aux in H0.
  apply none_not_some in H0 as [d H1].
  unfold option_map in H1.
  destruct depth_fold eqn:Heq. 2 : discriminate.
  injects H1.
  apply depth_fold_some in Heq.
  rewrite List.Forall_map, List.Forall_forall in Heq.
  specializes Heq H.
  auto.
Qed.

Lemma depth_aux_incr_fuel (fuel : nat) :
  forall (nd : rg_node) (d : nat),
    depth_aux fuel nd = Some d ->
    depth_aux (S fuel) nd = Some d.
Proof.
  induction fuel; intros. 
  now unfold depth_aux in H.
  rewrite <- H.
  unfold depth_aux.
  f_equal.
  f_equal.
  apply List.map_ext_in_iff.
  intros.
  fold (depth_aux fuel a).
  fold (depth_aux (S fuel) a).
  pose proof depth_aux_decr_fuel.
  specializes H1 fuel H0.
  specializes H1. now rewrite H.
  apply none_not_some in H1 as [? ?].
  specializes IHfuel H1.
  rewrite IHfuel.
  rewrite <- H1.
  reflexivity.
Qed.

Lemma none_depth_cases :
  forall (nd : rg_node) (fuel : nat),
    depth_aux fuel nd = None ->
    fuel = O \/ 
      exists (prem : rg_node),
        is_prem prem nd /\ depth_aux (pred fuel) prem = None.
Proof.
  intros.
  unfold depth_aux in H.
  destruct fuel. left. math. right.
  destruct depth_fold eqn:Heq. discriminate.
  clear H.
  unfold depth_fold in Heq.
  pose proof depth_fold_none_in_list.
  specializes H Heq.
  rewrite List.in_map_iff in H.
  destruct H as [prem [H1 H2]].
  exists prem.
  auto.
Qed.

Lemma none_depth_to_path_of_length : 
  forall (fuel : nat) (nd : rg_node),
    depth_aux fuel nd = None ->
    exists (p : path),
      first (proj1_sig p) = Some nd /\ length (proj1_sig p) = S fuel.
Proof.
  induction fuel.
  - intros nd _.
    exists (single_path nd).
    destruct single_path eqn:Heq.
    unfold single_path in Heq.
    simpls.
    injects Heq. 
    auto.
  - intros. 
    apply none_depth_cases in H as [H1 | H2]. discriminate.
    exists* H2.
    simpls.
    specializes IHfuel H0.
    destruct IHfuel as [[p P] [? ?]].
    simpls.
    assert (is_path (nd :: p)). 2 : { 
      exists (exist _ _ H3). 
      simpls. split. auto.
      rewrite length_cons. math.
    }
    simpl.
    destruct p. discriminate. split~.
    simpls. injects H. auto.
Qed.

Definition depth_opt (nd : rg_node) : nat? :=
  @depth_aux (cardinal rg.(rg_nodes)) nd.

Lemma depth_exists :
  forall (nd : rg_node),
    exists (n : nat),
      depth_opt nd = Some n.
Proof.
  pose proof none_depth_to_path_of_length.
  intros.
  apply none_not_some.
  intro.
  specializes H H0.
  exists* H.
  contradict A.
  pose proof path_longer_than_card_has_dupes.
  specializes H2 p.
  simpls.
  specializes H2. math.
  pose proof path_with_dupes_has_cycle.
  specializes H3 H2.
  exists* H3.
  now exists p2.
Qed.

Definition depth (nd:rg_node) :=
  proj1_sig (constructive_indefinite_description _ (depth_exists nd)).

Lemma depth_mono (nd:rg_node) :
  forall (prem:rg_node),
  is_prem prem nd ->
  (depth prem < depth nd)%nat.
Proof.
  intros.
  unfold depth.
  destruct constructive_indefinite_description as [d_prem Heq_dprem].
  destruct constructive_indefinite_description as [d Heq_d].
  simpls.
  unfold depth_opt in *.
  pose proof cardinal_nonempty nd as [n].
  pose proof Heq_d.
  rewrite H0 in Heq_d.
  simpls.
  unfold option_map in Heq_d.
  destruct depth_fold eqn:E. 2 : discriminate.
  inverts Heq_d.
  rename n0 into d.
  unfold depth_fold in E.
  pose proof E.
  apply depth_bound in H2 as [_ H2].
  rewrite List.Forall_forall in H2.
  specializes H2 (Some d_prem).
  specializes H2. 2 : math.
  apply List.in_map_iff.
  exists prem.
  splits~.
  pose proof depth_aux_decr_fuel.
  pose proof depth_aux_incr_fuel.
  specializes H2 n H.
  specializes H2. rewrite H0 in H1. now rewrite H1.
  apply none_not_some in H2 as [? ?].
  specializes H3 H2.
  rewrite H0 in Heq_dprem.
  rewrite H2. rewrite <- Heq_dprem.
  auto.
Qed.

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
  graph_lift_valid ->
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

End RuleGraphInstance.

Definition derives rg s :=
  graph_lift_valid rg /\
  exists nd, @rg_conc rg nd = s.

End RuleGraph.