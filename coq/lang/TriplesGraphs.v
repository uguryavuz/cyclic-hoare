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

  Variable is_rule_instance : graph -> node -> Prop.

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

Definition nodeID := nat.

Definition node : Type := 
  nodeID * stmt * rule * list nodeID.

Definition graph := fmap nodeID node.

Definition node_dummy : node := (O,|-true,HL_Seq,[]).

Global Instance Inhab_node : Inhab node.
Proof using.
  constructor. exists~ node_dummy.
Qed.

Inductive is_rule_instance (g:graph) : node -> Prop :=
  | Rule_HL_CSQ nid id1 id2 id3 P P' Q Q' c r1 r2 r3 prems1 prems2 prems3
    (H1 : read g id1 = (id1,|- (P->P'),r1,prems1)) 
    (H2 : read g id2 = (id2,|- c : P' => Q',r2,prems2))
    (H3 : read g id3 = (id3,|- (Q'->Q),r3,prems3))
    : is_rule_instance g (nid,|- c : P => Q,HL_CSQ,[id1;id2;id3])

  | Rule_HL_Case nid id1 id2 P P' Q c r1 r2 prems1 prems2
    (H1 : read g id1 = (id1,|- c : P /\ P' => Q,r1,prems1))
    (H2 : read g id2 = (id2,|- c : P /\ ~ P' => Q,r2,prems2))
    : is_rule_instance g (nid,|- c : P => Q,HL_Case,[id1;id2])

  | Rule_HL_Skip nid P
    : is_rule_instance g (nid,|- CSkip : P => P,HL_Skip,[])

  | Rule_HL_Assn nid x a P
    : is_rule_instance g (nid,|- CAssn x a : P[a/x] => P,HL_Assn,[])

  | Rule_HL_Seq nid id1 id2 P Q R c1 c2 r1 r2 prems1 prems2
    (H1 : read g id1 = (id1, |- c1 : P => Q, r1, prems1))
    (H2 : read g id2 = (id2, |- c2 : Q => R, r2, prems2))
    : is_rule_instance g (nid, |- CSeq c1 c2 : P => R, HL_Seq, [id1;id2])
  
  | Rule_HL_IfTrue nid id1 P Q (b:bexp) c c' r1 prems1
    (H1 : read g id1 = (id1, |- c : P /\ b => Q, r1, prems1))
    : is_rule_instance g (nid, |- CIf b c c' : P /\ b => Q, HL_IfTrue, [id1]%list)

  | Rule_HL_IfFalse nid id1 P Q (b:bexp) c c' r1 prems1
    (H1 : read g id1 = (id1, |- c' : P /\ ~b => Q, r1, prems1))
    : is_rule_instance g (nid, |- CIf b c c' : P /\ ~b => Q, HL_IfFalse, [id1]%list)

  | Rule_HL_WhileTrue nid id1 P Q (b:bexp) c r1 prems1
    (H : read g id1 = (id1, |- CSeq c (CWhile b c) : P /\ b => Q, r1, prems1))
    : is_rule_instance g (nid, |- CWhile b c : P /\ b => (Q /\ ~b), HL_WhileTrue, [id1]%list)

  | Rule_HL_WhileFalse nid P b c
    : is_rule_instance g (nid, |- CWhile b c : P /\ ~b => (P /\ ~b), HL_WhileFalse, [])

  | Rule_AssrtLift nid P
    (H : (|= P)%V)
    : is_rule_instance g (nid, |- P, HL_AssrtLift, [])
.
