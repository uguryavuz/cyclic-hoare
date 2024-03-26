(* example proving a pRHL judgement relating structurally
   dissimilar programs

   the proof involves lots of symbolic evaluation

   because the program executions settle into three mutually
   recursive configurations, the proof involves mutual
   induction *)

prover quorum=2 ["Alt-Ergo" "Z3"].
prover timeout=5.

require import AllCore FSet.

(* destinations: A, B and C - plus the environment *)

type dest = [A | B | Env].

(* an entity implements a procedure f taking in a destination and
   integer, and returning a new integer plus the destination it should
   be sent to *)

module type ENT = {
  proc f(x : int) : dest * int
}.


section.

abstract theory M.

op lim : {int | 0 <= lim} as ge0_lim.

module M1(L : ENT, R : ENT) = {
  var ctr : int

  proc run(d : dest, x : int) : int = {
    while ((d = A \/ d = B) (*/\ 0 < ctr*) ) {
      if (d = A) {
        (d, x) <@ L.f(x);
        ctr <- ctr - 1;
      } else {
        while (d = B (*/\ 0 < ctr*) ) {
          (d, x) <@ R.f(x);
          ctr <- ctr - 1;
        }
      }
    }
    return x;
  }
}.

module M2(L : ENT, R : ENT) = {
  var ctr : int

  proc run(d : dest, x : int) : int = {
    while ((d = A \/ d = B) (*/\ 0 < ctr*) ) {
      if (d = B) {
        (d, x) <@ R.f(x);
        ctr <- ctr - 1;
      } else {
        while (d = A (*/\ 0 < ctr*) ) {
          (d, x) <@ L.f(x);
          ctr <- ctr - 1;
        }
      }
    }
    return x;
  }
}.

end M.

clone M as N.


declare module L <: ENT{-N.M1, -N.M2}.
declare module R <: ENT{-N.M1, -N.M2, -L}.


lemma ind :
  equiv
  [N.M1(L,R).run ~ N.M2(L,R).run :
    ={d, x, glob L, glob R} ==>
    ={res}]
  =>
  equiv
  [N.M1(L,R).run ~ N.M2(L,R).run :
    ={d, x, glob L, glob R} ==>
    ={res}].
proof.

move => IH.
proc.


(* PERFORMING COMPUTATION *)

case (d{1} = Env).
rcondf{1} 1; auto.
rcondf{2} 1; auto.

(* A case *)
case (d{1} = A).
rcondt{1} 1 => //.
rcondt{1} 1 => //.
rcondt{2} 1 => //.
rcondf{2} 1 => //.
rcondt{2} 1 => //.
seq 1 1 : (={d, x, glob L, glob R}).
call (_ : true); auto.
sp.

admit.

(* B case *)
conseq (_ : ={glob L, glob R, d, x} /\ d{1} = B ==> ={x}).
progress. smt().
admit.

(* APPLY INDUCTIVE HYPOTHESIS *)

transitivity{1} {
  x <@ N.M1.run(d,x);
} (={d, x, glob L, glob R} ==> ={x})
  (={d, x, glob L, glob R} ==> ={x}).
progress. smt().
smt().
inline. sim.

symmetry.
transitivity{1} {
  x <@ N.M2.run(d,x);
} (={d, x, glob L, glob R} ==> ={x})
  (={d, x, glob L, glob R} ==> ={x}).
progress. smt().
smt().
inline. sim.

symmetry.
call IH. 
auto.

abort.



