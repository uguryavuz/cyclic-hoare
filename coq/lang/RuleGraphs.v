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

Definition reaches (nd1 nd2 : rg_node) : Prop :=
  exists (p : path),
    match classicT (proj1_sig p <> []) with
    | left H => ListFacts.get_nonempty_first H = nd1 /\ ListFacts.get_nonempty_last H = nd2
    | _ => False
    end.

Lemma reaches_refl nd : reaches nd nd.
  unfolds.
  assert (is_path (nd :: nil)) by (now unfold is_path). 
  exists (exist _ _ H).
  destruct (classicT (proj1_sig (exist is_path [nd]%list H) <> [])).
  simpls.
  + split.
    - unfold get_nonempty_first.
      destruct (constructive_definite_description _ _).
      simpl.
      unfold first in e.
      injects e.
      reflexivity.
    - unfold get_nonempty_last.
      destruct (constructive_definite_description _ _).
      simpl.
      unfold last in e.
      injects e.
      reflexivity.
  + simpls. 
    contradict n.
    discriminate.
Qed.

End RuleGraph.
