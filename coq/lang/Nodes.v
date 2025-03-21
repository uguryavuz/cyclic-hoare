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
