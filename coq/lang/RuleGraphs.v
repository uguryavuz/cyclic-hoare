Set Implicit Arguments.
From Lang Require Export Util.
From Coq Require Import Structures.OrderedTypeEx.
From Coq Require FSetList FSetFacts.

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

Variant rule_or_lift : Type :=
  | Rule (r : rule) 
  | Lift.

Inductive rule_graph : Type := {
  rg_nodes : NodeSet.t;
  rg_node  : Type := {nd | NodeSet.mem nd rg_nodes};
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
    ListFacts.last nodelist = ListFacts.first nodelist /\
    List.NoDup (List.tl nodelist) /\
    (List.length nodelist > 1)%nat.

Definition is_cyclic_rule_graph : Prop :=
  exists (p : path), is_cyclic_path p.

Lemma cyclic_graph_implies_longer_path_exists : 
  is_cyclic_rule_graph ->
  forall (p : path), 
    exists (p' : path), 
      List.length (proj1_sig p') > List.length (proj1_sig p).
Proof.
Admitted.

Lemma longer_path_exists_implies_cyclic_graph : 
  (forall (p : path), 
    exists (p' : path), 
      List.length (proj1_sig p') > List.length (proj1_sig p)) ->
  is_cyclic_rule_graph.
Admitted.

End Cycles.

End RuleGraph.
