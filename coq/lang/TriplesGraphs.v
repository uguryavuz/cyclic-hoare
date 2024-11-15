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

Definition node_of_graph g : Type := { nd : node | Image nd g }.


Section MapMem.

  Variable A B : Type.
  Variable l : list A.
  Variable f : forall (a:A), List.In a l -> B.

  Definition sub l' :=
    forall a, List.In a l' -> List.In a l.

  Inductive _mapmem : list A -> list B -> Prop :=
  | MapMemNil
    : _mapmem nil nil
  | MapMemCons a l' l'' (H: List.In a l) (R : _mapmem l' l'') 
    : _mapmem (a::l') (f a H :: l'').

  Lemma mapmem_ex : forall l',
    sub l' ->
    exists l'', unique (_mapmem l') l''.
  Proof.
    induction l'.
    { intro. exists (@nil B). constructor~. constructor~.
      intros. inverts~ H0. }
    intros. specializes IHl'.
    { introv ?. apply H. apply~ List.in_cons. }
    exists* IHl'.
    specializes H List.in_eq.
    exists (f a H :: l'').
    constructor~.
    constructor~. unfolds in IHl'. easy.
    intros. inverts H0. sort.
    unfolds in IHl'. exists* IHl'.
    f_equal. f_equal. apply proof_irrelevance.
    apply~ IHl'0.
  Qed.

  Lemma sub_refl : sub l.
  Proof. unfolds. auto. Qed.

  Definition mapmem : list B :=
    proj1_sig (constructive_definite_description _ (mapmem_ex sub_refl)).
    
End MapMem.


Check mapmem.


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

Definition helper g nid (x : {nd : node | MapsTo nid nd (proj1_sig g)}) 
: node_of_graph g.
  destruct x. econstructor. unfolds.
  exists nid. apply m.
Defined.

Definition get_prems (g:graph) (nd:node_of_graph g)
: list (node_of_graph g) :=
  let nc := (proj2_sig g) (proj1_sig nd) (proj2_sig nd) in
  mapmem (proj1_sig nd).(prems) (
    fun nid nid_mem =>
    let nid_in := nc nid nid_mem in
    helper g (constructive_definite_description _ (@node_from_in g nid nid_in))
  ).


(*  Lemma mapmem_helper a' l' l'' :
    l' = a'::l'' ->
    (forall a, List.In a l' -> List.In a l) ->
    (forall a, List.In a l'' -> List.In a l).
  Proof.
    intros. subst.
    apply H0. apply~ List.in_cons.
  Qed.

  Lemma mapmem_helper2 :
    forall a, List.In a l -> List.In a l.
  Proof. auto. Qed.

  Lemma mapmem_helper3 l' a (l'' : list A) :
    l' = a::l'' ->
    List.In a l'.
  Proof.
    intro. subst. apply List.in_eq.
  Qed.

  Fixpoint _mapmem (l' : list A) (H : forall a, List.In a l' -> List.In a l)
  : list B.
    refine (
    (match l' as l'0 return l' = l'0 -> list B with
    | [] => fun _ => []
    | a::l'' => 
      fun Hyp =>
      f a (H a (mapmem_helper3 Hyp)) :: _mapmem l'' (mapmem_helper Hyp H)
    end)
    (eq_refl l')).

  Fixpoint _mapmem (l' : list A) (H : forall a, List.In a l' -> List.In a l) 
  : list B :=
    match l' with
    | [] => []
    | a::l'' => f (H a (List.in_eq a l'')) :: _mapmem l f l'' (mapmem_helper a l'')
    end.
  
  Definition mapmem :=
    _mapmem l f l mapmem_helper2.

End MapMem.*)





Definition max_option (a b : nat?) : nat? :=
  match a, b with
  | Some n1, Some n2 => Some (Nat.max n1 n2)
  | _, _ => None
  end.

Definition depth_fold (l : list nat?) : nat? :=
  List.fold_left max_option l (Some O).

Fixpoint depth (g:graph) (fuel:nat) (nd:node_of_graph g) : nat? :=
  match fuel with 
  | O => None
  | S fuel =>
    let depths := 
      LibList.map (@depth g fuel)
      (get_prems nd) in
    option_map S (depth_fold depths)
  end.



Definition has_conc g nid s :=
  match find nid (proj1_sig g) with
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


Definition graph_valid (g:graph) :=
  forall node,
  Image node g ->
  node_valid g node.

Lemma graph_valid_node_in g (H : graph_valid g) :
  forall node,
  Image node g ->
  forall prem,
  LibList.mem prem node.(prems) ->
  In prem (proj1_sig g).
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
  | Path1 nid1 (H : In nid1 (proj1_graph g)) 
    : is_path g [nid1]%list
  | Path2 nid1 nid2 p node (H : MapsTo nid1 node (proj1_graph g)) 
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