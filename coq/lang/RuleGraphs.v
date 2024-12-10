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

Theorem is_path_implies_prems_relation:
  forall (p : list rg_node),
    is_path p ->
    forall (i : nat),
      (i < length p - 1)%nat ->
      match List.nth_error p i, List.nth_error p (S i) with
      | Some n1, Some n2 => List.In n2 (rg_prems n1)
      | _, _ => True
      end.
Proof.
  intros p H.
  induction p.
  - intros.
    assert (@length rg_node ([])%list = 0%nat) by auto.
    rewrite H1 in H0.
    simpl in H0.
    math.
  - destruct i.
    + intros.
      simpl in H0.
      simpl.
      destruct p.
      * simpl in H.
        destruct H.
        auto.
      * simpl in H.
        destruct H.
        auto.
    + intros.
      simpl in H0.
      simpl.
      destruct p.
      * simpl in H.
        destruct H.
        assert (H1 : (length ([a])%list = 1)%nat) by auto.
        rewrite H1 in H0.
        math.
      * simpl in H.
        destruct H.
        apply IHp; auto.
        assert (H2 : (length (a :: r :: p)%list = S (S (length p)))%nat) by auto.
        rewrite H2 in H0.
        assert (H3 : (length (r :: p)%list = S (length p))%nat) by auto.
        math.
Qed.

Lemma prems_relation_implies_is_path:
  forall (p : list rg_node),
    (forall (i : nat),
      (i < length p - 1)%nat ->
      match List.nth_error p i, List.nth_error p (S i) with
      | Some n1, Some n2 => List.In n2 (rg_prems n1)
      | _, _ => True
      end) ->
    is_path p.
Proof.
  intros p H.
  induction p; simpl; auto.
  simpl.
  destruct p; auto.
  split.
  - assert (H1 : (0 < length (a :: r :: p)%list - 1)%nat).
    { simpl.
      assert (H2 : (length (a :: r :: p)%list = S (S (length p)))%nat) by auto.
      rewrite H2.
      math. }
    apply H in H1.
    simpl in H1.
    auto.
  - apply IHp.
    intros.
    assert (H1 : (S i < length (a :: r :: p)%list - 1)%nat).
    { simpl.
      assert (H2 : (length (a :: r :: p)%list = S (S (length p)))%nat) by auto.
      rewrite H2.
      assert (H3 : (S (length p) = length (r :: p)%list)%nat) by auto.
      rewrite H3.
      math. }
    apply H in H1.
    simpl in H1.
    auto.
Qed.

Theorem prems_relation_iff_is_path:
  forall (p : list rg_node),
    (forall (i : nat),
      (i < length p - 1)%nat ->
      match List.nth_error p i, List.nth_error p (S i) with
      | Some n1, Some n2 => List.In n2 (rg_prems n1)
      | _, _ => True
      end) <->
    is_path p.
Proof.
  intros.
  split.
  - apply prems_relation_implies_is_path.
  - apply is_path_implies_prems_relation.
Qed.

Lemma empty_path_is_path : is_path ([])%list.
Proof.
  simpl.
  auto.
Qed.

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

Definition reaches (nd1 nd2 : rg_node) : Prop :=
  exists (p : path),
    let node_list := proj1_sig p in
      ListFacts.first node_list = Some nd1 /\
      ListFacts.last node_list = Some nd2.

Lemma reaches_refl : forall nd, reaches nd nd.
  intros.
  unfold reaches.
  assert (H : is_path ([nd]%list)) by (now unfold is_path).
  exists (exist _ _ H).
  assert (H_NE : [nd]%list <> []) by discriminate.
  split; auto.
Qed.

Definition is_cyclic_path (p : path) : Prop :=
  let node_list := proj1_sig p in
    ListFacts.last node_list = ListFacts.first node_list /\
    List.NoDup (List.tl node_list) /\
    (List.length node_list > 1)%nat.

Definition is_cyclic_rule_graph : Prop :=
  exists (p : path), is_cyclic_path p.

Lemma cyclic_graph_implies_longer_path_exists : 
  is_cyclic_rule_graph ->
  forall (p : path), 
    exists (p' : path), 
      List.length (proj1_sig p') > List.length (proj1_sig p).
Proof.
  intros.
  destruct H as [p' H].
Admitted.

Lemma longer_path_exists_implies_cyclic_graph : 
  (forall (p : path), 
    exists (p' : path), 
      List.length (proj1_sig p') > List.length (proj1_sig p)) ->
  is_cyclic_rule_graph.
Admitted.

(* Holding area *)

Lemma appending_cycle_preserves_endpoints : 
  forall (p : path) 
      (H : ListFacts.last (proj1_sig p) = ListFacts.first (proj1_sig p)),
    let appended_path := path_append p p H in
      ListFacts.last (proj1_sig appended_path) = ListFacts.first (proj1_sig appended_path).
Proof.
  intros.
  destruct p as [p Hp].
  simpl in *.
  destruct p; auto.
  simpl.
  assert (H0 : ((r :: p) ++ p = r :: (p ++ p))%list) by auto.
  rewrite H0.
  pose proof (ListFacts.last_repeat p).
  simpl.
  destruct (p ++ p)%list eqn:Hp'; auto.
  rewrite H1.
  simpl in H.
  destruct p; auto.
  discriminate.
Qed.

Fixpoint iterated_cycle (p : path) (H : is_cyclic_path p) (n : nat) : path :=
  match n with
  | O     => exist _ ([])%list empty_path_is_path
  | 1%nat => p
  | S n'  => path_append (@iterated_cycle p H n') p (appending_cycle_preserves_endpoints p (proj1 H))
  end.

End RuleGraph.
