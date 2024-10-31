Set Implicit Arguments.
From Lang Require Import TriplesMeta.

Section Example.

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

Local Lemma ex1_proof :
  |- c1 : true => AssrtEqA (AVar "x") (AVal 50).
Proof.
  unfold c1.
  apply HL_Assn'.
  simpls. unfolds.
  intros. simpls. intros.
  case_if~.
Qed.


Local Definition c2 : cmd :=
  (*CAssn "x" #n ;;*)
  CAssn "i" #3 ;;
  CWhile (BLt #0 (AVar "i"))
  (CAssn "x" (AMul (AVar "x") #2);;
   CAssn "i" (ASub (AVar "i") #1)).

Local Lemma ex2_eval m :
  yields c2 m (m["x"=8*m "x"]["i"=0]).
Proof.
  econstructor.
  econstructor. econstructor. econstructor.
  simpls. econstructor.
  apply StepSeqSkip. econstructor.
  econstructor.
  simpls. now rewrite upd_read1.
  econstructor. repeat econstructor.
  simpls. rewrite upd_read1_diff; [|discriminate].
  remember (m "x") as x0.
  econstructor. econstructor.
  apply StepSeqSkip.
  econstructor. econstructor.
  econstructor. econstructor.
  apply StepSeqSkip.
  simpls. rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. econstructor.
  simpls. now rewrite upd_read1.
  econstructor. econstructor.
  econstructor. econstructor.
  simpls. rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. econstructor.
  apply StepSeqSkip.
  econstructor. econstructor.
  econstructor. simpls.
  rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. apply StepSeqSkip.
  econstructor. econstructor.
  simpls. now rewrite upd_read1.
  econstructor. econstructor.
  econstructor. econstructor.
  simpls. rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. econstructor.
  apply StepSeqSkip.
  econstructor. econstructor.
  econstructor. simpls.
  rewrite upd_shadow2, upd_read2; [|discriminate].
  econstructor. apply StepSeqSkip.
  econstructor. apply StepWhileFalse.
  simpls. now rewrite upd_read1.
  replace (x0*2*2*2) with (8*x0). 2: math.
  replace (3-1-1-1) with 0. 2: math.
  constructor.
Qed.

Notation EQ x n := (AssrtEqA (AVar x) #n).

Lemma ex2_proof n :
  |- c2 : 
    EQ "x" n =>
    (EQ "x" (8*n) /\ EQ "i" 0).
Proof.
  unfold c2.
  apply HL_Seq with (Q:=(EQ "x" n /\ EQ "i" 3)%A).
  { simpls. apply HL_Assn'.
    introv ?. simpls.
    case_if~. simpls. splits~.
    case_if~. }
  apply HL_WhileTrue'.
  { simpls. introv (?&?).
    simpls. math. }
  apply HL_Seq with (Q:=(EQ "x" (n*2) /\ EQ "i" 2)%A).
  { apply HL_Seq with (Q:=(EQ "x" (n*2) /\ EQ "i" 3)%A).
    { apply HL_Assn'. simpls.
      introv (?&?&?). simpls.
      case_if~. simpls. splits~. math.
      case_if~. simpls. math. }
    apply HL_Assn'.
    introv ?. simpls.
    case_if~. simpls. splits~. math.
    case_if~. simpls. math. }
  
  apply HL_WhileTrue'.
  { simpls. introv (?&?).
    simpls. math. }
  apply HL_Seq with (Q:=(EQ "x" (n*4) /\ EQ "i" 1)%A).
  { apply HL_Seq with (Q:=(EQ "x" (n*4) /\ EQ "i" 2)%A).
    { apply HL_Assn'. simpls.
      introv (?&?&?). simpls.
      case_if~. simpls. splits~. math.
      case_if~. simpls. math. }
    apply HL_Assn'.
    introv ?. simpls.
    case_if~. simpls. splits~. math.
    case_if~. simpls. math. }

  apply HL_WhileTrue'.
  { simpls. introv (?&?).
    simpls. math. }
  apply HL_Seq with (Q:=(EQ "x" (n*8) /\ EQ "i" 0)%A).
  { apply HL_Seq with (Q:=(EQ "x" (n*8) /\ EQ "i" 1)%A).
    { apply HL_Assn'. simpls.
      introv (?&?&?). simpls.
      case_if~. simpls. splits~. math.
      case_if~. simpls. math. }
    apply HL_Assn'.
    introv ?. simpls.
    case_if~. simpls. splits~. math.
    case_if~. simpls. math. }

  apply HL_WhileFalse'.
  { introv (?&?). simpls. math. }
  introv (?&?). simpls. math.
Qed.


    
End Example.

