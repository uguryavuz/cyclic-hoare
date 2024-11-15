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

Record node : Type := mkNode {
  nid : nodeID;
  conc : stmt;
  rulename : rule;
  prems : list nodeID
}.


From Coq Require FMapList FMapFacts.

Module Import NodeMap := FMapList.Make(NodeID).
Module NodeMapFacts := FMapFacts.Facts(NodeMap).

Definition graph := NodeMap.t node.

Implicit Type g : graph.

(*Definition node_dummy : node := mkNode O (|-true) HL_Skip [].

Global Instance Inhab_node : Inhab node.
Proof using.
  constructor. exists~ node_dummy.
Qed.
*)

Definition has_conc g nid s :=
  match NodeMap.find nid g with
  | None => False
  | Some node => node.(conc) = s
  end.

Inductive node_valid (g:graph) : node -> Prop :=
  | Rule_HL_CSQ nid id1 id2 id3 P P' Q Q' c
    (H1 : has_conc g id1 (|- (P->P'))) 
    (H2 : has_conc g id2 (|- c : P' => Q'))
    (H3 : has_conc g id3 (|- (Q'->Q)))
    : node_valid g (mkNode nid (|- c : P => Q) HL_CSQ [id1;id2;id3])
  | Rule_HL_Case nid id1 id2 P P' Q c
    (H1 : has_conc g id1 (|- c : P /\ P' => Q))
    (H2 : has_conc g id2 (|- c : P /\ ~ P' => Q))
    : node_valid g (mkNode nid (|- c : P => Q) HL_Case [id1;id2])

  | Rule_HL_Skip nid P
    : node_valid g (mkNode nid (|- CSkip : P => P) HL_Skip [])

  | Rule_HL_Assn nid x a P
    : node_valid g (mkNode nid (|- CAssn x a : P[a/x] => P) HL_Assn [])

  | Rule_HL_Seq nid id1 id2 P Q R c1 c2
    (H1 : has_conc g id1 (|- c1 : P => Q))
    (H2 : has_conc g id2 (|- c2 : Q => R))
    : node_valid g (mkNode nid (|- CSeq c1 c2 : P => R) HL_Seq [id1;id2])
  
  | Rule_HL_IfTrue nid id1 P Q (b:bexp) c c'
    (H1 : has_conc g id1 (|- c : P /\ b => Q))
    : node_valid g (mkNode nid (|- CIf b c c' : P /\ b => Q) HL_IfTrue [id1]%list)

  | Rule_HL_IfFalse nid id1 P Q (b:bexp) c c'
    (H1 : has_conc g id1 (|- c' : P /\ ~b => Q))
    : node_valid g (mkNode nid (|- CIf b c c' : P /\ ~b => Q) HL_IfFalse [id1]%list)

  | Rule_HL_WhileTrue nid id1 P Q (b:bexp) c
    (H : has_conc g id1 (|- CSeq c (CWhile b c) : P /\ b => Q))
    : node_valid g (mkNode nid (|- CWhile b c : P /\ b => (Q /\ ~b)) HL_WhileTrue [id1]%list)

  | Rule_HL_WhileFalse nid P b c
    : node_valid g (mkNode nid (|- CWhile b c : P /\ ~b => (P /\ ~b)) HL_WhileFalse [])

  | Rule_AssrtLift nid P
    (H : (|= P)%V)
    : node_valid g (mkNode nid (|- P) HL_AssrtLift [])
.

Definition Image node g :=
  exists nid, MapsTo nid node g.

Definition graph_valid (g:graph) :=
  forall node,
  Image node g ->
  node_valid g node.

Lemma graph_valid_node_in g (H : graph_valid g) :
  forall node,
  Image node g ->
  forall prem,
  LibList.mem prem node.(prems) ->
  In prem g.
Proof.
  intros. specializes H H0.
  apply NodeMapFacts.in_find_iff. intro.
  inverts~ H; simpls; unfolds has_conc.
  all: try easy.
  - inverts H1. now rewrite H2 in *.
    inverts H6. now rewrite H2 in *.
    inverts H1. now rewrite H2 in *.
    inverts H6.
  - inverts H1. now rewrite H2 in *.
    inverts H5. now rewrite H2 in *.
    easy.
  - inverts H1. now rewrite H2 in *.
    inverts H5. now rewrite H2 in *.
    easy.
  - inverts~ H1. now rewrite H2 in *.
    easy.
  - inverts~ H1. now rewrite H2 in *.
    easy.
  - inverts~ H1. now rewrite H2 in *.
    easy.
Qed.


Definition derives (g:graph) (H:graph_valid g) (s:stmt) :=
  exists node, Image node g /\ node.(conc) = s.

Definition derivable (s:stmt) :=
  exists (g:graph) (H:graph_valid g),
  @derives g H s.

Definition path := list nodeID.

Inductive is_path (g:graph) : path -> Prop :=
  | Path0 : is_path g []
  | Path1 nid1 (H : In nid1 g) 
    : is_path g [nid1]%list
  | Path2 nid1 nid2 p node (H : MapsTo nid1 node g) 
    (HM : LibList.mem nid2 node.(prems))
    (HP : is_path g (nid2::p))
    : is_path g (nid1::nid2::p)
  .

Definition graph_acyclic (g:graph) :=
  exists (n:nat),
  forall p,
  is_path g p ->
  LibList.length p <= n.


(*Section Trees.

Inductive tree : Type :=
  Tree (conc:stmt) (rule:rule) (prems:list tree).


Definition graph_to_tree g (H:graph_acyclic g) (nid:nodeID) : tree. Admitted.


End Trees.
*)

(*Inductive _depth g nid p : nat -> Prop :=
  | DepthC (HC : LibList.mem nid p) 
    : _depth g nid p n_pos_inf
  | Depth0 node (HN : MapsTo nid node g) 
    (HF : ~ LibList.mem nid p)
    (H : node.(prems) = []) : _depth g nid p O
  | DepthN node l (m:nat) (HN : MapsTo nid node g)
    (HF : ~ LibList.mem nid p)
    (H : node.(prems) = l) 
    (HM : exists nid', LibList.mem nid' l /\ _depth g nid' (nid::p) m)
    (HL : forall nid' (m':nat), LibList.mem nid' l -> 
          _depth g nid' (nid::p) m' -> m' <= m)
    : _depth g nid p (S m)
.
    
Definition depth g nid n :=
*)

Section Soundness.

Open Scope valid_scope.

Lemma soundness0 g c P Q nid rule :
  graph_valid g ->
  MapsTo nid (mkNode nid (|-c:P=>Q) rule []) g ->
  |=c:P=>Q.
Proof.
  intros. specializes H.
  exists nid. apply H0.
  inverts H.
  apply skip_sound.
  apply assn_sound.
  apply while_false_sound.
Qed.


(*Inductive depth g (Cyc : graph_acyclic g) nid (I : In nid g) : nat -> Prop :=
  | Depth0 node (HN : MapsTo nid node g) (H : node.(prems) = []) : depth Cyc I O
  | DepthN n (H : (read g nid).(prems) = l)
    (R : exists prem, LibList.mem prem l /\ depth Cyc 
    forall prem (I':indom g prem), 
         LibList.mem prem l -> depth Cyc I' n ->
          
      )


Definition depth g (H : graph_acyclic g) :=
  let max := indefinite_description H in
  fix rec d nid :=
    match d with
    | O => O
  .
*)


Lemma soundness c P Q g (H : graph_valid g) :
  graph_acyclic g ->
  derives H (|- c : P => Q) ->
  |= c : P => Q.
Proof.
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