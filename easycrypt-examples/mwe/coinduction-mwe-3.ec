
prover quorum=2 ["Alt-Ergo" "Z3"].
prover timeout=5.

require import AllCore FSet.

type dest = [A | B | Env].

module type ENT = {
  proc f(x : int) : dest * int
}.


section.


declare module L <: ENT.
declare module R <: ENT{-L}.

module M = {
  
  proc a_loop(d : dest, x : int) : dest * int = {
    while (d = A) { (d, x) <@ L.f(x); }
    return (d, x);
  }

  proc b_loop(d : dest, x : int) : dest * int = {
    while (d = B) { (d, x) <@ R.f(x); }
    return (d, x);
  }

  proc run1(d : dest, x : int) : int = {
    while (d = A \/ d = B) {
      if (d = A) { (d, x) <@ L.f(x); }
      else       { (d, x) <@ b_loop(d, x); }
    }
    return x;
  }

  proc run2(d : dest, x : int) : int = {
    while (d = A \/ d = B) {
      if (d = B) { (d, x) <@ R.f(x); } 
      else       { (d, x) <@ a_loop(d, x); }
    }
    return x;
  }

  proc unroll1(d : dest, x : int) : int = {
    (d, x) <@ b_loop(d, x);
    x <@ run1(d, x);
    return x;
  }

  proc unroll2(d : dest, x : int) : int = {
    (d, x) <@ a_loop(d, x);
    x <@ run2(d, x);
    return x;
  }
}.

op eq1 = equiv
  [M.run1 ~ M.run2 :
    ={d, x, glob L, glob R} ==>
    ={res}].

op eq2 = equiv
  [M.run1 ~ M.unroll2 :
    ={d, x, glob L, glob R} ==>
    ={res}].

op eq3 = equiv
  [M.unroll1 ~ M.run2 :
    ={d, x, glob L, glob R} ==>
    ={res}].

op IH = eq1 /\ eq2 /\ eq3.



lemma ind1 : IH => eq1.
proof.
move => [_ [IH2 IH3]] @/eq1.
proc.

(* Env case *)
case (d{1} = Env).
rcondf{1} 1; auto.
rcondf{2} 1; auto.


(* A case *)
case (d{1} = A).
rcondt{1} 1 => //.
rcondt{1} 1 => //.
rcondt{2} 1 => //.
rcondf{2} 1 => //.
inline. sp.
rcondt{2} 1 => //.
seq 1 1 : (={glob L, glob R} /\ d{1} = d0{2} /\ x{1} = x0{2}).
call (_ : true); auto.


transitivity{1} {
  x <@ M.run1(d,x);
} (={d, x, glob L, glob R} ==> ={x})
  (={glob L, glob R} /\ d{1} = d0{2} /\ x{1} = x0{2} ==> ={x}).
progress. smt().
smt().
inline. sim.

symmetry.
transitivity{1} {
  x <@ M.unroll2(d0,x0);
} (={d0, x0, glob L, glob R} ==> ={x})
  (={glob L, glob R} /\ d{2} = d0{1} /\ x{2} = x0{1} ==> ={x}).
progress. smt().
smt().
inline. sim.
symmetry.

move : IH2 => @/eq2 IH2.
call IH2 => //.


(* B case *)
conseq (_ : ={glob L, glob R, d, x} /\ d{1} = B ==> ={x}).
smt().
rcondt{1} 1 => //.
rcondf{1} 1 => //.
rcondt{2} 1 => //.
rcondt{2} 1 => //.
inline. sp.

rcondt{1} 1 => //.
seq 1 1 : (={glob L, glob R} /\ d0{1} = d{2} /\ x0{1} = x{2}).
call (_ : true); auto.

transitivity{1} {
  x <@ M.unroll1(d0,x0);
} (={d0, x0, glob L, glob R} ==> ={x})
  (={glob L, glob R} /\ d0{1} = d{2} /\ x0{1} = x{2} ==> ={x}).
progress. smt().
smt().
inline. sim.

symmetry.
transitivity{1} {
  x <@ M.run2(d,x);
} (={d, x, glob L, glob R} ==> ={x})
  (={glob L, glob R} /\ d{1} = d0{2} /\ x{1} = x0{2} ==> ={x}).
progress. smt().
smt().
inline. sim.
symmetry.

move : IH3 => @/eq3 IH3.
call IH3 => //.

qed.





lemma ind2 : IH => eq2.
proof.
move => [_ [IH2 IH3]] @/eq2.
proc.
inline. wp. sp.

(* Env case *)
case (d{1} = Env).
rcondf{1} 1; auto.
rcondf{2} 1; auto.
sp. rcondf{2} 1; auto.

(* A case *)
case (d{1} = A).
rcondt{1} 1 => //.
rcondt{1} 1 => //.
rcondt{2} 1 => //.
seq 1 1 : (={glob L, glob R} /\ d{1} = d0{2} /\ x{1} = x0{2}).
call (_ : true); auto.

transitivity{1} {
  x <@ M.run1(d,x);
} (={d, x, glob L, glob R} ==> ={x})
  (={glob L, glob R} /\ d{1} = d0{2} /\ x{1} = x0{2} ==> x{1} = x1{2}).
progress. smt().
smt().
inline. sim.

symmetry.
transitivity{1} {
  x1 <@ M.unroll2(d0,x0);
} (={d0, x0, glob L, glob R} ==> ={x1})
  (={glob L, glob R} /\ d0{1} = d{2} /\ x0{1} = x{2} ==> x{2} = x1{1}).
progress. smt().
smt().
inline. sim.
symmetry.

move : IH2 => @/eq2 IH2.
call IH2 => //.

(* B case *)
conseq (_ : ={glob L, glob R, d, x} /\ d{1} = d0{2} /\ x{1} = x0{2} /\ d{1} = B ==> x{1} = x1{2}).
progress. smt().
rcondt{1} 1 => //.
rcondf{1} 1 => //.
rcondf{2} 1 => //.
sp. elim* => ? ?.
conseq (_ : ={glob L, glob R, d0, x0} /\ d0{1} = d1{2} /\ x0{1} = x1{2} /\ d0{1} = B 
    ==> x{1} = x1{2}) => //.

transitivity{1} {
  x <@ M.unroll1(d0,x0);
} (={glob L, glob R, d0, x0} ==> ={x})
  (={glob L, glob R, d0, x0} /\ d0{1} = d1{2} /\ x0{1} = x1{2} /\ d0{1} = B ==> x{1} = x1{2}).
progress. smt().
smt().
inline. sim.

symmetry.
transitivity{1} {
  x1 <@ M.run2(d1,x1);
} (={glob L, glob R, d1, x1} ==> ={x1})
  (={glob L, glob R, d0, x0} /\ d0{2} = d1{1} /\ x0{2} = x1{1} ==> x{2} = x1{1}).
progress. smt().
smt().
inline. sim.
symmetry.

move : IH3 => @/eq3 IH3.
call IH3 => //.

qed.


lemma ind3 : IH => eq3.
proof.
move => [_ [IH2 IH3]] @/eq3.
proc.
inline. wp. sp.

(* Env case *)
case (d{1} = Env).
rcondf{1} 1; auto.
rcondf{2} 1; auto.
sp. rcondf{1} 1; auto.

(* B case *)
case (d{1} = B).
rcondt{1} 1 => //.
rcondt{2} 1 => //.
rcondt{2} 1 => //.
seq 1 1 : (={glob L, glob R} /\ d0{1} = d{2} /\ x0{1} = x{2}).
call (_ : true); auto.

transitivity{1} {
  x1 <@ M.unroll1(d0,x0);
} (={d0, x0, glob L, glob R} ==> ={x1})
  (={glob L, glob R} /\ d0{1} = d{2} /\ x0{1} = x{2} ==> x1{1} = x{2}).
progress. smt().
smt().
inline. sim.

symmetry.
transitivity{1} {
  x <@ M.run2(d,x);
} (={glob L, glob R, d, x} ==> ={x})
  (={glob L, glob R} /\ d0{2} = d{1} /\ x0{2} = x{1} ==> x1{2} = x{1}).
progress. smt().
smt().
inline. sim.
symmetry.

move : IH3 => @/eq3 IH3.
call IH3 => //.

(* A case *)
conseq (_ : ={glob L, glob R, d, x} /\ d0{1} = d{2} /\ x0{1} = x{2} /\ d{1} = A ==> x1{1} = x{2}).
progress. smt().
rcondt{2} 1 => //.
rcondf{2} 1 => //.
rcondf{1} 1 => //.
sp. elim* => ? ?.
conseq (_ : ={glob L, glob R, d0, x0} /\ d1{1} = d0{2} /\ x1{1} = x0{2} /\ d0{1} = A 
    ==> x1{1} = x{2}) => //.

transitivity{1} {
  x1 <@ M.run1(d1,x1);
} (={glob L, glob R, d1, x1} ==> ={x1})
  (={glob L, glob R, d0, x0} /\ d1{1} = d0{2} /\ x1{1} = x0{2} /\ d0{1} = A ==> x1{1} = x{2}).
progress. smt().
smt().
inline. sim.

symmetry.
transitivity{1} {
  x <@ M.unroll2(d0,x0);
} (={glob L, glob R, d0, x0} ==> ={x})
  (={glob L, glob R, d0, x0} /\ d1{2} = d0{1} /\ x1{2} = x0{1} ==> x1{2} = x{1}).
progress. smt().
smt().
inline. sim.
symmetry.

move : IH2 => @/eq2 IH2.
call IH2 => //.

qed.


axiom lob H : (H => H) => H.


lemma overall : eq1.
proof.
have H : (eq1 /\ eq2 /\ eq3 => eq1). auto.
apply H. clear H.
apply lob => IH.
split; last split.
by apply ind1.
by apply ind2.
by apply ind3.
qed.








module N = {

  var ctr : int
  
  proc a_loop(d : dest, x : int) : dest * int = {
    while (d = A /\ 0 < ctr) { 
      (d, x) <@ L.f(x);
      ctr <- ctr - 1;
    }
    return (d, x);
  }

  proc b_loop(d : dest, x : int) : dest * int = {
    while (d = B /\ 0 < ctr) { 
      (d, x) <@ R.f(x);
      ctr <- ctr - 1;
    }
    return (d, x);
  }

  proc run1(d : dest, x : int) : int = {
    while ((d = A \/ d = B) /\ 0 < ctr) {
      if (d = A) {
        (d, x) <@ L.f(x);
        ctr <- ctr - 1;
      }
      else { 
        (d, x) <@ b_loop(d, x);
      }
    }
    return x;
  }

  proc run2(d : dest, x : int) : int = {
    while ((d = A \/ d = B) /\ 0 < ctr) {
      if (d = B) { 
        (d, x) <@ R.f(x); 
        ctr <- ctr - 1;
      } 
      else { 
        (d, x) <@ a_loop(d, x); 
      }
    }
    return x;
  }

  proc unroll1(d : dest, x : int) : int = {
    (d, x) <@ b_loop(d, x);
    x <@ run1(d, x);
    return x;
  }

  proc unroll2(d : dest, x : int) : int = {
    (d, x) <@ a_loop(d, x);
    x <@ run2(d, x);
    return x;
  }
}.



op eq1' ctr = equiv
  [N.run1 ~ N.run2 :
    ={glob L, glob R, d, x, N.ctr} /\ ctr = N.ctr{1} ==>
    ={res}].

op eq2' ctr = equiv
  [N.run1 ~ N.unroll2 :
    ={glob L, glob R, d, x, N.ctr} /\ ctr = N.ctr{1} ==>
    ={res}].

op eq3' ctr = equiv
  [N.unroll1 ~ N.run2 :
    ={glob L, glob R, d, x, N.ctr} /\ ctr = N.ctr{1} ==>
    ={res}].

op IH' ctr = eq1' ctr /\ eq2' ctr /\ eq3' ctr.



lemma ind_ctr (ctr : int) :
  IH' ctr.
proof.
case (ctr < 0) => [lt0_ctr | ge0_ctr].

(* Negative counter *)
split; last split.
move => @/eq1'. proc.
rcondf{1} 1 => //. auto. smt().
rcondf{2} 1 => //. auto. smt().
move => @/eq2'. proc.
rcondf{1} 1 => //. auto. smt().
inline. sp.
rcondf{2} 1 => //. auto. smt().
sp. rcondf{2} 1 => //. auto. smt().
sp. auto. 
move => @/eq3'. proc.
rcondf{2} 1 => //. auto. smt().
inline. sp.
rcondf{1} 1 => //. auto. smt().
sp. rcondf{1} 1 => //. auto. smt().
auto.

(* Non-negative counter *)
have : 0 <= ctr by smt().
clear ge0_ctr.
elim ctr => [| ctr get0_n IH].

(* Base case *)
split; last split.
move => @/eq1'. proc.
rcondf{1} 1 => //. auto. smt().
rcondf{2} 1 => //. auto. smt().
move => @/eq2'. proc.
rcondf{1} 1 => //. auto. smt().
inline. sp.
rcondf{2} 1 => //. auto. smt().
sp. rcondf{2} 1 => //. auto. smt().
sp. auto. 
move => @/eq3'. proc.
rcondf{2} 1 => //. auto. smt().
inline. sp.
rcondf{1} 1 => //. auto. smt().
sp. rcondf{1} 1 => //. auto. smt().
auto.

(* Inductive step *)
move : IH => [_ [IH2 IH3]].
split; last split.

(* Case 1 *)

move => @/eq1'. proc.
case (d{1} = Env).

(* Case 1.Env *)
rcondf{1} 1. auto.
rcondf{2} 1. auto.
auto.
case (d{1} = A).

(* Case 1.A *)
admit.

(* Case 1.B *)
admit.

(* Case 2 *)

move => @/eq2'. proc.
admit.


(* Case 3 *)

move => @/eq3'. proc.
admit.

abort.
