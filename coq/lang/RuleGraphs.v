Set Implicit Arguments.
From Lang Require Export Util.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require FSetList FSetFacts FSetProperties.

Variable stmt : Type.
Variable liftable : stmt -> Prop.
Variable valid_stmt : stmt -> Prop.

Variable rule : Type.
Variable valid_rule : rule -> list stmt -> stmt -> Prop.

Definition sound_rule (r : rule) : Prop :=
  forall (prems : list stmt) (conc : stmt),
    valid_rule r prems conc ->
      LibList.Forall valid_stmt prems ->
      valid_stmt conc.  

Module Node <: UsualOrderedType.
  Include Nat_as_OT.
End Node.

Notation node := Node.t.

Module Import NodeSet := FSetList.Make(Node).
Module NodeSetFacts := FSetFacts.Facts(NodeSet).
Module NodeSetProperties := FSetProperties.Properties(NodeSet).

Section Pigeon.

Definition dommem dom := {nd | NodeSet.In nd dom}.

Definition proj_into_subdom
  (dom:t) (e:elt)
  (e':dommem dom) (H:e <> proj1_sig e') 
  : dommem (remove e dom) :=
  exist (fun e' => In e' (remove e dom)) (proj1_sig e') 
  (@remove_2 dom e (proj1_sig e') H (proj2_sig e')).



Lemma nodelist_pigeon_aux : 
  forall (dom : NodeSet.t) (l : list (dommem dom)),
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
  rewrite cardinal_1 in *.
  rewrite List.map_length in H1.
  replace (length l) with (Datatypes.length l) in *.
  contradict H. rewrite ngt_as_le. auto.
  { clear. induction l. auto.
    rewrite length_cons. simpls.
    math. }
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



  apply List.NoDup_cons_iff in H1 as (?&?).
  Search List.NoDup List.map.

  contra H. apply List.in_map_iff in H.
  exists* H.
  apply eq_sig_hprop in H. subst~.
  intros. apply proof_irrelevance.

   generalize dependent l.
  induction l.
  { simpls. intros. apply List.NoDup_nil. }
  intros. simpls. apply List.NoDup_cons.
  2: { 
    apply IHl.
    now apply List.NoDup_cons_iff in H1 as (?&?).
    now apply List.incl_cons_inv in H2 as (?&?). 
  }
  apply List.NoDup_cons_iff in H1 as (?&?).
  contra H. apply List.in_map_iff in H.
  exists* H.
  apply eq_sig_hprop in H. subst~.
  intros. apply proof_irrelevance.
Qed.

   Search (proj1_sig _ = proj1_sig _). eq. injects H. destruct x. inverts H. simpls. subst.

  remember (List.map _) as f.
  apply List.incl_cons_inv in H2 as (?&?).

  intro. specializes IHl H0.
  
  


  induction n. { math. }
  intros.
  pose proof cardinal_1. rewrite H1 in *.
  destruct (choose dom) eqn:E.
  2: {
    apply choose_2 in E. unfolds in E.
    destruct l. contradict H0.
    rewrite length_nil. math.
    destruct d. now specializes E x.
  }
  sort. apply choose_1 in E.
  remember (exist (fun nd => In nd dom) e E) as x.
  assert (List.In x l).
  { apply absurds_lemma. intro.
    admit. }
  assert (forall (a a' : dommem dom), {a=a'} + {a<>a'}).
  { intros. destruct a, a'. pose proof Node.eq_dec x0 x1.
    destruct H3. subst. left. apply~ exist_eq_exist.
    right. intro. injects~ H3. }
  remember (remove e dom) as dom'.
  remember (List.remove X x l) as l'. sort.
  intro.
  assert (forall el, List.In el l' -> e <> proj1_sig el).
  { admit. }
  remember (mapmem l' (
    fun e' H =>
    @proj_into_subdom dom e e' (H4 e' H)
  )) as l''. subst dom'.

  specializes IHn (remove e dom) l''.
  assert (cardinal (remove e dom) = pred (cardinal dom)).
  { admit. }
  specializes IHn.
  { rewrite H5, cardinal_1. 
    destruct (Datatypes.length (elements dom)) eqn:F.
    2: math. false.
    apply List.length_zero_iff_nil in F.
    apply elements_1 in E as ?.
    rewrite F in *.
    now apply SetoidList.InA_nil in H6. }
  { rewrite H5, cardinal_1.
    rewrite Heql''.
    replace (length (mapmem l' _)) with (length l').
    2: {
      admit.
    }
    contra H0. rewrite ngt_as_le in *.
    clear Heql''.
    repeat rewrite cardinal_1 in H5.
    rewrite <- H5 in H0.
    pose proof List.remove_length_lt X l x H2.
    rewrite <- Heql' in *.
    Search Datatypes.length List.NoDup.
    

    rewrite Heql'.
    admit. }
  contra IHn. admit.
Admitted.



Lemma nodelist_pigeon : 
  forall (dom : NodeSet.t) (l : list {nd | NodeSet.In nd dom}),
  length l > cardinal dom ->
  ~ List.NoDup l.
Proof.
  intros.
  applys~ nodelist_pigeon_aux (S (cardinal dom)). math.
Qed.



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

Lemma path_decomposing : forall (nl1 nl2 : list rg_node),
  is_path (nl1 ++ nl2)%list ->
  is_path nl1 /\ is_path nl2.
Proof.
  induction nl1.
  { easy. }
  intro. generalize dependent nl1.
  induction nl2.
  { intros. rewrite app_nil_r in H. now splits~. }
  intros.
  
    
Admitted.

End PathAppending.

Section Reaches.

Definition reaches (nd1 nd2 : rg_node) : Prop :=
  exists (p : path),
    let nodelist := proj1_sig p in
      ListFacts.first nodelist = Some nd1 /\
      ListFacts.last nodelist = Some nd2.

Lemma reaches_refl : forall nd, reaches nd nd.
  intros.
  unfold reaches.
  assert (H : is_path ([nd]%list)) by (now unfold is_path).
  exists (exist _ _ H).
  assert (H_NE : [nd]%list <> []) by discriminate.
  split; auto.
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

Fact no_dup_list_of_length_card_contains_all_elements :
  forall (n : nat) (node_set : NodeSet.t),
    n = cardinal node_set -> 
    forall (l : list {nd | NodeSet.In nd node_set}),
      n = length l ->
      List.NoDup l ->
      forall (nd : {nd | NodeSet.In nd node_set}),
        List.In nd l.
Proof.
  clear rg.
  induction n.
  intros.
  destruct nd.
  contradict i.
  assert (H2 : Empty node_set). {
    rewrite cardinal_1 in H.
    unfold Datatypes.length in H.
    destruct (elements node_set) eqn:Heq; [|math].
    now apply NodeSetProperties.elements_Empty.
  }
  now specialize (H2 x).
  intros.
  remember (NodeSet.remove (proj1_sig nd) node_set) as node_set'.
  specialize (IHn node_set').
  assert (H3 : n = cardinal node_set'). {
    rewrite Heqnode_set'.
    pose proof NodeSetProperties.remove_cardinal_1 as G.
    specialize (G node_set (proj1_sig nd)).
    rewrite <- H in G.
    rewrite Nat.succ_inj_wd in G.
    symmetry.
    apply G.
    destruct nd.
    now simpl.
  }
  specialize (IHn H3).
  assert (H4 : forall n1 n2 : {nd : elt | In nd node_set }, {n1 = n2} + {n1 <> n2}). {
    clear H3 Heqnode_set' nd H1 H0 l H IHn node_set' n.
    intros.
    destruct n1 as [n1 Hn1], n2 as [n2 Hn2].
    destruct (Node.eq_dec n1 n2).
    + left.
      apply exist_eq_exist.
      auto.
    + right.
      intros G.
      injects G.
      contradiction.
  }
  remember (List.remove H4 nd l) as l'.
  clear H3 H.
  sort.
  (* Should map l' to type {nd | NodeSet.In nd node_set'} first *)
  assert (H5 : n = length l'). {
    admit.
  }
Admitted.

Fact path_longer_than_card_has_dupes :
  forall (p : path),
    let nodelist := proj1_sig p in 
      length nodelist > cardinal rg.(rg_nodes) ->
      ~ List.NoDup nodelist.
Proof.
  intros. now apply nodelist_pigeon.
Qed.
  
  (*intros.
  contra H.
  rewrite ngt_as_le.
  generalize dependent nodelist.
  induction nodelist. { rewrite LibList.length_nil. math. }
  intros.
  inverts H.
  specialize (IHnodelist H3).
  rewrite length_cons.
  simpl.
  apply le_case_eq_lt in IHnodelist.
  destruct IHnodelist. 2 : math.
  contradict H2.
  rewrite cardinal_1 in H.
Admitted.*)

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

Fact path_with_dupes_helper : 
  forall (n : nat) (p : path),
    let nodelist := proj1_sig p in
      length nodelist < n -> 
      ~ List.NoDup nodelist ->
      exists p1 p2 p3 H1 H2,
        p = path_append (path_append p1 p2 H1) p3 H2 /\
        is_cyclic_path p2.
Proof.
  induction n.
  math.
  intros.
  assert (H1 : length nodelist <= n) by math.
  apply le_case_eq_lt in H1.
  destruct H1. 2 : now specialize (IHn p H1 H0).
  destruct (classic (is_cyclic_path p)). {
    remember (ListFacts.first nodelist) as first_nd.
    remember (ListFacts.last nodelist) as last_nd.
    destruct first_nd. 2 : {
      destruct H2.
      destruct H3.
      subst.
      clear H3 H2 H0 IHn H.
      subst nodelist.
      destruct (proj1_sig p).
      rewrite LibList.length_nil in H4. math.
      discriminate.
    }
    destruct last_nd. 2 : {
      destruct H2.
      destruct H3.
      subst.
      clear H3 H2 H0 IHn H.
      subst nodelist.
      destruct (proj1_sig p).
      rewrite LibList.length_nil in H4. math.
      contradict Heqlast_nd.
      symmetry.
      apply ListFacts.last_exists.
    }
    exists (single_path r) p (single_path r0).
    exists.
    split. 2 : auto.
    unfold path_append.
    simpls.
    subst nodelist.
    destruct p.
    simpls.
    apply exist_eq_exist.
    rewrite LibList.app_nil_r.
    rewrite LibList.app_cons_one_r.
    destruct x.
    discriminate.
    simpls.
    now injects Heqfirst_nd.
  }
  destruct nodelist as [|hd tl] eqn:Heqn.
  contradict H0.
  apply List.NoDup_nil.
  rewrite List.NoDup_cons_iff in H0.
  rewrite not_and_eq in H0.
  rewrite not_not_eq in H0.
  destruct H0. 2 : {
    assert (H3 : length tl < n).
    rewrite LibList.length_cons in H1.
    math.
    assert (H4 : is_path tl). {
      subst nodelist.
      destruct p.
      simpls.
      destruct x.
      discriminate.
      injects Heqn.
      destruct tl.
      auto.
      simpls.
      destruct i.
      auto.
    } 
    specialize (IHn (exist _ _ H4)).
    simpls.
    specialize (IHn H3 H0).
    exists* IHn.
    subst nodelist.
    clear H3 H2 H1 H0 H n.
    sort.
    destruct p as [nl Hp].
    simpls.
    subst.
    assert (G : is_path (hd :: (proj1_sig p1))). {
      injects IHn.
      rewrite <- app_cons_l in Hp.
      apply path_decomposing in Hp.
      destruct Hp.
      rewrite <- app_cons_l in H.
      apply path_decomposing in H.
      destruct H.
      auto.
    }
    exists (exist _ _ G) p2 p3.
    exists.
    splits~.
    apply exist_eq_exist.
    simpls.
    clear G IHn0 Hp.
    rewrite 2!app_cons_l.
    f_equal.
    injects IHn.
    auto.
  }

Admitted.

Fact path_with_dupes_has_cycle :
  forall (p : path),
    let nodelist := proj1_sig p in
      ~ List.NoDup nodelist ->
      exists p1 p2 p3 H1 H2,
        p = path_append (path_append p1 p2 H1) p3 H2 /\
        is_cyclic_path p2.
Proof.
  intros.
  remember (S (length nodelist)) as n.
  assert (H1 : length nodelist < n) by math.
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

End Cycles.

End RuleGraph.
