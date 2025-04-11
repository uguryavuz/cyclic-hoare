Set Implicit Arguments.
From Lang Require Import Util Nodes RuleGraphs.

Section RuleTree.

  
Variable univ : universe.

Notation stmt := univ.(stmt).
Notation valid_stmt := univ.(valid_stmt).

Variable ps : proof_system univ.

Notation rule := ps.(rule).
Notation liftable := ps.(liftable).
Notation valid_rule := ps.(valid_rule).

Reserved Notation "conc_of_tree." (at level 80).

(*Inductive rule_tree : Type :=
  | TLift (conc : stmt) (Hlift : liftable conc)
  | TRule (conc : stmt) (*(prems : list stmt)*) (tprems : list rule_tree)
    (*(Hprems : )*)
    (r : rule) (Hval : valid_rule r conc (List.map (conc_of_tree.) tprems))
where
  "conc_of_tree." :=
  (fun (rt : rule_tree) => match rt with
    | TLift conc _ => conc
    | TRule conc _ _ _ _ => conc end).
*)

(*Inductive rule_tree : Prop :=
  | TLift (conc : stmt) (Hlift : liftable conc) : rule_tree
  | TRule (conc : stmt) (prems : list stmt)
    (r : rule) (Hr : valid_rule r prems conc)
    (Hprems : List.Forall rule_tree prems) : rule_tree conc.

Definition root (rt : rule_tree) :=
  match rt with
  | TLift conc _ => conc
  | TRule conc _ _ _ _ => conc
  end.

Definition re_root (tprems : List rule_tree) (conc : stmt)
  ()


    (r : rule) (Hprems : valid_rule r (List.map root tprems) conc) :
    rule_tree_valid (TRule conc tprems r)
  .*)

Inductive _rule_tree : Type :=
  | TLift (conc : stmt) 
  | TRule (conc : stmt) (tprems : list _rule_tree) (r : rule)
  .

Definition root (rt : _rule_tree) :=
  match rt with
  | TLift conc => conc
  | TRule conc _ _ => conc
  end.

Inductive rule_tree_valid : _rule_tree -> Prop :=
  | VTLift (conc : stmt) (Hlift : liftable conc) : rule_tree_valid (TLift conc)
  | VTRule (conc : stmt) (tprems : list _rule_tree)
    (r : rule) (Hprems : valid_rule r (List.map root tprems) conc) :
    rule_tree_valid (TRule conc tprems r)
  .

Definition rule_tree := { rt : _rule_tree | rule_tree_valid rt }.
Notation get_tree := (@proj1_sig _rule_tree rule_tree_valid).

Definition re_root (conc : stmt) (tprems : list rule_tree) (r : rule)
  (Hprems : valid_rule r (List.map (root ∘ get_tree) tprems) conc) : rule_tree.
pose (TRule conc (List.map get_tree tprems) r) as _rt.
assert (rule_tree_valid _rt).
2: { refine (exist _ _ H). }
apply VTRule. now rewrite List.map_map.
Defined.




End RuleTree.