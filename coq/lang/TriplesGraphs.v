Set Implicit Arguments.
From Lang Require Export Assertions.

Implicit Type m : mem.
Implicit Type n : int.
Implicit Type I : binding.
Implicit Type c : cmd.


Inductive stmt : Type :=
| StmtTriple (c:cmd) (P Q : assrt)
| StmtAssrt (P:assrt).


Notation "'|-' c ':' P '=>' Q" := 
  (StmtTriple c P%A Q%A)
  (at level 50, c at next level, no associativity).

Notation "'|-' P" :=
  (StmtAssrt P%A)
  (at level 50, no associativity).


(*Section Graphs.

  Variable rule : Type.

  Variable ruleID : rule.

  Definition nodeID := nat.

  Definition node : Type := 
    nodeID * stmt * rule * list nodeID.

  Definition graph := fmap nodeID node.

  Definition node_dummy : node := (O,|-true,ruleID,[]).

  Global Instance Inhab_node : Inhab node.
  Proof using ruleID.
    constructor. exists~ node_dummy.
  Qed.

  Variable node_valid : graph -> node -> Prop.

End Graphs.*)



Inductive rule :=
| HL_CSQ
| HL_Case
| HL_Skip
| HL_Assn
| HL_Seq
| HL_IfTrue
| HL_IfFalse
| HL_WhileTrue
| HL_WhileFalse
| HL_AssrtLift.

From Coq Require Import Structures.OrderedTypeEx.

Module NodeID <: UsualOrderedType.

Include Nat_as_OT.

End NodeID.

Notation nodeID := NodeID.t.

From Coq Require FMapList FMapFacts.

Module Import NodeMap := FMapList.Make(NodeID).
Module NodeMapFacts := FMapFacts.Facts(NodeMap).


Inductive node : Type := mkNode {
  nid : nodeID;
  conc : stmt;
  rulename : rule;
  prems : list nodeID 
}.

Definition _graph : Type := NodeMap.t node.

Definition node_closed (g : _graph) (node:node) :=
  forall nid,
  List.In nid node.(prems) ->
  In nid g.

Definition Image node (g : _graph) :=
  exists nid, MapsTo nid node g.

Definition graph_closed g :=
  forall node,
  Image node g ->
  node_closed g node.

Definition graph :=
  { g | graph_closed g }.

Implicit Type g : graph.

Definition proj1_graph g := proj1_sig g.
Coercion proj1_graph : graph >-> _graph.


(* If nid is in g, then g maps nid to a unique node *)
Lemma node_from_in (g:_graph) nid (H:In nid g) :
  exists nd, unique (fun nd => MapsTo nid nd g) nd.
Proof.
  apply NodeMapFacts.in_find_iff in H.
  apply none_not_some in H. exists* H.
  exists j. unfolds.
  splits.
  - apply~ NodeMapFacts.find_mapsto_iff.
  - intros. applys NodeMapFacts.MapsTo_fun.
    apply~ NodeMapFacts.find_mapsto_iff.
    apply~ H. auto.
Qed.


Section Nodes.

Variable g : graph.

(* node of graph *)
Definition nog : Type := { nd : node | Image nd g }.

(* Convert nid and node to which it maps into nog *)
Local Definition get_prems_aux nid (x : {nd : node | MapsTo nid nd (proj1_sig g)}) 
: nog.
  destruct x. econstructor. unfolds.
  exists nid. apply m.
Defined.

(* Get nodes that are premises of node *)
Definition get_prems (nd:nog)
: list nog :=
  let graph_closed := proj2_sig g in
  let node_closed := graph_closed (proj1_sig nd) (proj2_sig nd) in
  mapmem (proj1_sig nd).(prems) (
    fun nid nid_mem =>  (* Node ID, and witness that it is member of prems list *)
    let nid_in := node_closed nid nid_mem in
    let node := @node_from_in g nid nid_in in
    get_prems_aux (constructive_definite_description _ node)
  ).

Definition max_option (a b : nat?) : nat? :=
  match a, b with
  | Some n1, Some n2 => Some (Nat.max n1 n2)
  | _, _ => None
  end.

Definition depth_fold (l : list nat?) : nat? :=
  List.fold_left max_option l (Some O).

Fixpoint depth_aux (fuel:nat) (nd:nog) : nat? :=
  match fuel with 
  | O => None
  | S fuel =>
    let depths := 
      LibList.map (@depth_aux fuel)
      (get_prems nd) in
    option_map S (depth_fold depths)
  end.

Definition depth nd : nat? :=
  @depth_aux (NodeMap.cardinal (proj1_sig g)) nd.

(* No path longer than the number of nodes exists *)
Definition graph_acyclic :=
  forall (nd:nog),
  depth nd <> None.



Definition path := list nodeID.

Inductive is_path : path -> Prop :=
  | Path0 : is_path nil
  | Path1 nid1 (H : In nid1 (proj1_graph g)) 
    : is_path (nid1::[])
  | Path2 nid1 nid2 p node (H : MapsTo nid1 node (proj1_graph g)) 
    (HM : LibList.mem nid2 node.(prems))
    (HP : is_path (nid2::p))
    : is_path (nid1::nid2::p)
  .



Definition has_conc nid s :=
  match find nid (proj1_sig g) with
  | None => False
  | Some node => node.(conc) = s
  end.

Inductive node_valid : node -> Prop :=
  | Rule_HL_CSQ nid id1 id2 id3 P P' Q Q' c
    (H1 : has_conc id1 (|- (P->P'))) 
    (H2 : has_conc id2 (|- c : P' => Q'))
    (H3 : has_conc id3 (|- (Q'->Q)))
    : node_valid (mkNode nid (|- c : P => Q) HL_CSQ [id1;id2;id3])
  | Rule_HL_Case nid id1 id2 P P' Q c
    (H1 : has_conc id1 (|- c : P /\ P' => Q))
    (H2 : has_conc id2 (|- c : P /\ ~ P' => Q))
    : node_valid (mkNode nid (|- c : P => Q) HL_Case [id1;id2])

  | Rule_HL_Skip nid P
    : node_valid (mkNode nid (|- CSkip : P => P) HL_Skip [])

  | Rule_HL_Assn nid x a P
    : node_valid (mkNode nid (|- CAssn x a : P[a/x] => P) HL_Assn [])

  | Rule_HL_Seq nid id1 id2 P Q R c1 c2
    (H1 : has_conc id1 (|- c1 : P => Q))
    (H2 : has_conc id2 (|- c2 : Q => R))
    : node_valid (mkNode nid (|- CSeq c1 c2 : P => R) HL_Seq [id1;id2])
  
  | Rule_HL_IfTrue nid id1 P Q (b:bexp) c c'
    (H1 : has_conc id1 (|- c : P /\ b => Q))
    : node_valid (mkNode nid (|- CIf b c c' : P /\ b => Q) HL_IfTrue [id1]%list)

  | Rule_HL_IfFalse nid id1 P Q (b:bexp) c c'
    (H1 : has_conc id1 (|- c' : P /\ ~b => Q))
    : node_valid (mkNode nid (|- CIf b c c' : P /\ ~b => Q) HL_IfFalse [id1]%list)

  | Rule_HL_WhileTrue nid id1 P Q (b:bexp) c
    (H : has_conc id1 (|- CSeq c (CWhile b c) : P /\ b => Q))
    : node_valid (mkNode nid (|- CWhile b c : P /\ b => (Q /\ ~b)) HL_WhileTrue [id1]%list)

  | Rule_HL_WhileFalse nid P b c
    : node_valid (mkNode nid (|- CWhile b c : P /\ ~b => (P /\ ~b)) HL_WhileFalse [])

  | Rule_AssrtLift nid P
    (H : (|= P)%V)
    : node_valid (mkNode nid (|- P) HL_AssrtLift [])
.


Definition graph_valid :=
  forall (nd:nog),
  node_valid (proj1_sig nd).

Definition derives (H:graph_valid) (s:stmt) :=
  exists (nd:nog), (proj1_sig nd).(conc) = s.

End Nodes.


Definition derivable (s:stmt) :=
  exists (g:graph) (H:graph_valid g),
  @derives g H s.




Lemma acyclic_path_equiv g :
  graph_acyclic g <->
  exists n,
  forall p,
  is_path g p ->
  List.length p < n.
Proof.
Abort.

Section Soundness.

Open Scope valid_scope.

Lemma soundness0 g c P Q nid rule :
  graph_valid g ->
  MapsTo nid (mkNode nid (|-c:P=>Q) rule []) (proj1_sig g) ->
  |=c:P=>Q.
Proof.
  unfolds graph_valid.
  intros.
  simpls. remember (mkNode _ _ _ _) as nd.
  assert (Image nd g). { destruct g. simpls. exists~ nid. }
  remember (exist _ nd H1 : nog g) as N'.
  specializes H N'. subst. clear H0.
  simpls.
  inverts~ H; subst.
  apply skip_sound.
  apply assn_sound.
  apply while_false_sound.
Qed.



(*Definition oget {A:Type} (X : option A) (H : X <> None) : A :=
  indefinite_description _ (none_not_some H).
*)

Lemma local_soundness g (AC : graph_acyclic g) (nd:nog g) :
  forall c P Q,
  (proj1_sig nd).(conc) = |- c : P => Q ->
  |= c : P => Q.
Proof.
  unfolds in AC.
  induction (depth nd) using (well_founded_induction lt_wf).




Lemma soundness_acyclic g :
  graph_acyclic g ->
  forall (H : graph_valid g),
  forall c P Q,
  derives H (|- c : P => Q) ->
  |= c : P => Q.
Proof.
  induction (cardinal (proj1_sig g)) eqn:C.
  
  (* Base: empty graph *)
  { destruct g. simpls. unfolds cardinal.
    destruct x. simpls. destruct this0.
    2: { simpls. discriminate. }
    simpls. intros.
    unfolds in H1. exists* H1.
    destruct nd. simpls. unfolds in i.
    exists* i. unfolds in i.
    unfolds in i. simpls. inverts i. }

  

  
  
   (* using (well_founded_induction lt_wf).*)
  (*
  intros (max&Cyc).
  unfolds in H1. exists* H1.
  destruct (read _ _) eqn:E. simpls.
  subst.
  apply H in E. induction E as [?????????c].
  admit. admit.
  *)
Abort.


End Soundness.