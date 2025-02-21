Set Implicit Arguments.
From Lang Require Import Assertions TriplesGraphs.

Notation "c1 ;; c2" := (CSeq c1 c2) (at level 39, right associativity).
Notation "x @@ z w" := (x (z w)) (at level 38, right associativity, only parsing).
Notation "# n" := (AVal n) (at level 5).

Local Definition c1 : cmd :=
  CAssn "x" (AMul (AVal 5) (AVal 10)).

Local Lemma ex1_eval m :
  yields c1 m (m["x"=50]).
Proof.
  unfolds. exists.
  repeat econstructor.
Qed.


Local Lemma infinite_loop_aux :
  forall n m c m',
  multistep (CWhile true CSkip) m c m' n ->
  c <> CSkip.
Proof.
  induction n using (well_founded_induction lt_wf).
  intros. destruct n.
  { inverts H0. discriminate. }
  inverts H0. inverts H6.
  2: { contradict Hg. auto. }
  inverts H'. discriminate.
  inverts H0. { inverts H6. }
  applys H H'0. math.
Qed.

Local Lemma infinite_loop_valid P Q :
  (|= (CWhile true CSkip) : P => Q)%V.
Proof.
  unfold valid_triple, triple, yields.
  intros. exists* H0. now apply infinite_loop_aux in H0.
Qed.