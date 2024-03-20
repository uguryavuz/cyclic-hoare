(* example proving a pRHL judgement relating structurally
   dissimilar programs

   the proof involves lots of symbolic evaluation

   because the program executions settle into three mutually
   recursive configurations, the proof involves mutual
   induction *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore FSet.

(* destinations: A, B and C - plus the environment *)

type dest = [A | B | C | Env].

op _A_  : dest fset = fset1 A.
op _B_  : dest fset = fset1 B.
op _C_  : dest fset = fset1 C.
op _AB_ : dest fset = fset1 A `|` fset1 B.
op _BC_ : dest fset = fset1 B `|` fset1 C.

(* an entity implements a procedure f taking in a destination and
   integer, and returning a new integer plus the destination it should
   be sent to *)

module type ENT = {
  proc f(d : dest, x : int) : dest * int
}.

(* abstract theory for combining two entities *)

abstract theory Combine.

op lefts, rights : dest fset.

module Comb (L : ENT, R : ENT) = {
  proc f(d : dest, x : int) : dest * int = {
    while (d \in lefts `|` rights) {
      if (d \in lefts) {
        (d, x) <@ L.f(d, x);
      }
      else {
        (d, x) <@ R.f(d, x);
      }
    }
    return (d, x);
  }
}.

end Combine.

clone Combine as AB with
  op lefts  <- _A_,
  op rights <- _B_
proof *.

clone Combine as BC with
  op lefts  <- _B_,
  op rights <- _C_
proof *.

clone Combine as A_BC with
  op lefts  <- _A_,
  op rights <- _BC_
proof *.

clone Combine as AB_C with
  op lefts  <- _AB_,
  op rights <- _C_
proof *.

(* We would like to prove:

lemma overall (A <: ENT) (B <: ENT{-A}) (C <: ENT{-A, -B}) :
  equiv
  [A_BC.Comb(A, BC.Comb(B, C)).f ~ AB_C.Comb(AB.Comb(A, B), C).f :
   ={d, x, glob A, glob B, glob C} ==> ={res}].

But instead we prove a version of this lemma that limits the number
of times A.f, B.f and C.f may be called *)

abstract theory Lim.

op lim : {int | 0 <= lim} as ge0_lim.

module Lim (E : ENT) : ENT = {
  var ctr : int

  proc f(d : dest, x : int) : dest * int = {
    if (0 < ctr) {
      ctr <- ctr - 1;
      (d, x) <@ E.f(d, x);
    }
    else {
      (* send default value of 0 to environment *)
      d <- Env; x <- 0;
    }
    return (d, x);
  }
}.

end Lim.

(* clone Lim for use with A, B and C *)

clone Lim as LimA.
clone Lim as LimB.
clone Lim as LimC.

section.

declare module A <: ENT{-LimA.Lim, -LimB.Lim, -LimC.Lim}.
declare module B <: ENT{-A, -LimA.Lim, -LimB.Lim, -LimC.Lim}.
declare module C <: ENT{-A, -B, -LimA.Lim, -LimB.Lim, -LimC.Lim}.

(* modules that support our mutual induction *)

local module M1 = {
  proc f(d : dest, x : int) : dest * int = {
    while (d \in _B_ `|` _C_) {
      if (d \in _B_) {
        (d, x) <@ LimB.Lim(B).f(d, x);
      }
      else {
        (d, x) <@ LimC.Lim(C).f(d, x);
      }
    }
    while (d \in _A_ `|` _BC_) {
      if (d \in _A_) {
        (d, x) <@ LimA.Lim(A).f(d, x);
      }
      else {
        (d, x) <@ BC.Comb(LimB.Lim(B), LimC.Lim(C)).f(d, x);
      }
    }
    return (d, x);
  }
}.

local module M2 = {
  proc f(d : dest, x : int) : dest * int = {
    while (d \in _A_ `|` _B_) {
      if (d \in _A_) {
        (d, x) <@ LimA.Lim(A).f(d, x);
      }
      else {
        (d, x) <@ LimB.Lim(B).f(d, x);
      }
    }
    while (d \in _AB_ `|` _C_) {
      if (d \in _AB_) {
        (d, x) <@ AB.Comb(LimA.Lim(A), LimB.Lim(B)).f(d, x);
      }
      else {
        (d, x) <@ LimC.Lim(C).f(d, x);
      }
    }
    return (d, x);
  }
}.

(* lemma proved by induction

   note that the P(n) is the conjunction of three pRHL judgements,
   one for each of three mutually recursive configurations

   first read overall', below *)

local lemma ind (n : int) :
  equiv
  [M1.f ~ M2.f :
   ={d, x, glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n ==>
   ={res}] /\
  equiv
  [M1.f ~ AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f :
   ={d, x, glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n ==>
   ={res}] /\
  equiv
  [A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f ~ M2.f :
   ={d, x, glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n ==>
   ={res}].
proof.
case (n < 0) => [le0_n | not_le_n].
split; first exfalso => /#.
split; first exfalso => /#.
exfalso => /#.
have : 0 <= n by smt().
clear not_le_n.
elim n => [| n ge0_n IH].
(* basis step *)
split; last split.
(* first conjunct *)
proc.
case (d{1} = A).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimA.Lim(A).f.
sp.
rcondf{1} 1; first auto; smt().
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimA.Lim(A).f.
sp.
rcondf{2} 1; first auto; smt().
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = B).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimB.Lim(B).f.
sp.
rcondf{1} 1; first auto; smt().
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimB.Lim(B).f.
sp.
rcondf{2} 1; first auto; smt().
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = C).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimC.Lim(C).f.
sp.
rcondf{1} 1; first auto; smt().
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimC.Lim(C).f.
sp.
rcondf{2} 1; first auto; smt().
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* case d{1} = Env *)
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* second conjunct *)
proc.
case (d{1} = A).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimA.Lim(A).f.
sp.
rcondf{1} 1; first auto; smt().
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) AB.Comb(LimA.Lim(A), LimB.Lim(B)).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimA.Lim(A).f.
sp.
rcondf{2} 1; first auto; smt().
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = B).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimB.Lim(B).f.
sp.
rcondf{1} 1; first auto; smt().
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) AB.Comb(LimA.Lim(A), LimB.Lim(B)).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimB.Lim(B).f.
sp.
rcondf{2} 1; first auto; smt().
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = C).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimC.Lim(C).f.
sp.
rcondf{1} 1; first auto; smt().
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimC.Lim(C).f.
sp.
rcondf{2} 1; first auto; smt().
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* case d{1} = Env *)
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* third conjunct *)
proc.
case (d{1} = A).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimA.Lim(A).f.
sp.
rcondf{1} 1; first auto; smt().
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimA.Lim(A).f.
sp.
rcondf{2} 1; first auto; smt().
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = B).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) BC.Comb(LimB.Lim(B), LimC.Lim(C)).f.
sp.
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimB.Lim(B).f.
sp.
rcondf{1} 1; first auto; smt().
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimB.Lim(B).f.
sp.
rcondf{2} 1; first auto; smt().
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = C).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) BC.Comb(LimB.Lim(B), LimC.Lim(C)).f.
sp.
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimC.Lim(C).f.
sp.
rcondf{1} 1; first auto; smt().
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimC.Lim(C).f.
sp.
rcondf{2} 1; first auto; smt().
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* case d{1} = Env *)
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* inductive step *)
split; last split.
(* first conjunct *)
proc.
case (d{1} = A).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimA.Lim(A).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimA.Lim(A).f.
sp.
if => //.
sp.
seq 1 1 :
  (={d0, x0, glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n).
call (_ : true); first auto; smt().
sp.
transitivity*{1}
{ (d, x) <@ A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f(d, x); }
  => //; first progress; smt().
inline{2} (1) A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f.
sim.
transitivity*{2} { (d, x) <@ M2.f(d, x); } => //; first progress; smt().
have [_ [_ third]] := IH.
call third; first auto.
inline{1} (1) M2.f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = B).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimB.Lim(B).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimB.Lim(B).f.
sp.
if => //.
sp.
seq 1 1 :
  (={d0, x0, glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n).
call (_ : true); first auto; smt().
sp.
transitivity*{1} { (d, x) <@ M1.f(d, x); } => //; first progress; smt().
inline{2} (1) M1.f.
sim.
transitivity*{2} { (d, x) <@ M2.f(d, x); } => //; first progress; smt().
have [first [_ _]] := IH.
call first; first auto.
inline{1} (1) M2.f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = C).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimC.Lim(C).f.
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimC.Lim(C).f.
sp.
if => //.
sp.
seq 1 1 :
  (={d0, x0, glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n).
call (_ : true); first auto; smt().
sp.
transitivity*{1} { (d, x) <@ M1.f(d, x); } => //; first progress; smt().
inline{2} (1) M1.f.
sim.
transitivity*{2}
{ (d, x) <@ AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f(d, x); }
  => //; first progress; smt().
have [_ [second _]] := IH.
call second; first auto.
inline{1} (1) AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* case d{1} = Env *)
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* second conjunct *)
proc.
case (d{1} = A).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimA.Lim(A).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) AB.Comb(LimA.Lim(A), LimB.Lim(B)).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimA.Lim(A).f.
sp.
if => //.
sp.
seq 1 1 :
  (={glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   d0{1} = d1{2} /\ x0{1} = x1{2} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n).
call (_ : true); first auto; smt().
sp.
transitivity*{1}
{ (d, x) <@ A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f(d, x); }
  => //; first progress; smt().
inline{2} (1) A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f.
sim.
transitivity*{2} { (d, x) <@ M2.f(d0, x0); } => //; first progress; smt().
have [_ [_ third]] := IH.
call third; first auto.
inline{1} (1) M2.f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = B).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimB.Lim(B).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) AB.Comb(LimA.Lim(A), LimB.Lim(B)).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimB.Lim(B).f.
sp.
if => //.
sp.
seq 1 1 :
  (={glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   d0{1} = d1{2} /\ x0{1} = x1{2} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n).
call (_ : true); first auto; smt().
sp.
transitivity*{1} { (d, x) <@ M1.f(d, x); } => //; first progress; smt().
inline{2} (1) M1.f.
sim.
transitivity*{2} { (d, x) <@ M2.f(d0, x0); } => //; first progress; smt().
have [first [_ _]] := IH.
call first; first auto.
inline{1} (1) M2.f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = C).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimC.Lim(C).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimC.Lim(C).f.
sp.
if => //.
sp.
seq 1 1 :
  (={glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   ={d0, x0} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n).
call (_ : true); first auto; smt().
sp.
transitivity* {1} { (d, x) <@ M1.f(d, x); } => //; first progress; smt().
inline{2} (1) M1.f.
sim.
transitivity*{2}
{ (d, x) <@ AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f(d, x); }
  => //; first progress; smt().
have [_ [second _]] := IH.
call second; first auto.
inline{1} (1) AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* case d{1} = Env *)
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* third conjunct *)
proc.
case (d{1} = A).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimA.Lim(A).f.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimA.Lim(A).f.
sp.
if => //.
sp.
seq 1 1 :
  (={glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   ={d0, x0} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n).
call (_ : true); first auto; smt().
sp.
transitivity*{1}
{ (d, x) <@ A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f(d, x); }
  => //; first progress; smt().
inline{2} (1) A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f.
sim.
transitivity*{2} { (d, x) <@ M2.f(d, x); } => //; first progress; smt().
have [_ [_ third]] := IH.
call third; first auto.
inline{1} (1) M2.f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = B).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) BC.Comb(LimB.Lim(B), LimC.Lim(C)).f.
sp.
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimB.Lim(B).f.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimB.Lim(B).f.
sp.
if => //.
sp.
seq 1 1 :
  (={glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   d1{1} = d0{2} /\ x1{1} = x0{2} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n).
call (_ : true); first auto; smt().
sp.
transitivity*{1} { (d, x) <@ M1.f(d0, x0); } => //; first progress; smt().
inline{2} (1) M1.f.
sim.
transitivity*{2} { (d, x) <@ M2.f(d, x); } => //; first progress; smt().
have [first [_ _]] := IH.
call first; first auto.
inline{1} (1) M2.f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = C).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) BC.Comb(LimB.Lim(B), LimC.Lim(C)).f.
sp.
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimC.Lim(C).f.
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimC.Lim(C).f.
sp.
if => //.
sp.
seq 1 1 :
  (={glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   d1{1} = d0{2} /\ x1{1} = x0{2} /\
   0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} /\ 
   LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1} = n).
call (_ : true); first auto; smt().
sp.
transitivity*{1} { (d, x) <@ M1.f(d0, x0); } => //; first progress; smt().
inline{2} (1) M1.f.
sim.
transitivity*{2}
{ (d, x) <@ AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f(d, x); }
  => //; first progress; smt().
have [_ [second _]] := IH.
call second; first auto.
inline{1} (1) AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* case d{1} = Env *)
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
qed.

(* now we can use the result of our induction to prove our overall
   result *)

lemma overall' :
  equiv
  [A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f ~
   AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f :
   ={d, x, glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   LimA.Lim.ctr{1} = LimA.lim /\ LimB.Lim.ctr{1} = LimB.lim /\ 
   LimC.Lim.ctr{1} = LimC.lim ==>
   ={res}].
proof.
proc.
case (d{1} = A).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimA.Lim(A).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) AB.Comb(LimA.Lim(A), LimB.Lim(B)).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimA.Lim(A).f.
sp.
if => //.
sp.
seq 1 1 :
  (={glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   d0{1} = d1{2} /\ x0{1} = x1{2} /\
   LimA.Lim.ctr{1} = LimA.lim - 1 /\ LimB.Lim.ctr{1} = LimB.lim /\ 
   LimC.Lim.ctr{1} = LimC.lim /\
   0 < LimA.lim).
call (_ : true); first auto.
sp.
(* apply third conjunct of ind *)
transitivity{1}
{ (d, x) <@ A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f(d, x); }
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 ={d, x} ==>
 ={d, x})
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 d{1} = d0{2} /\ x{1} = x0{2} /\
 0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} ==>
 ={d, x}) => //.
progress; smt(LimA.ge0_lim LimB.ge0_lim LimC.ge0_lim).
inline{2} (1) A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f.
sim.
transitivity{2}
{ (d, x) <@ M2.f(d0, x0); }
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 d{1} = d0{2} /\ x{1} = x0{2} /\
 0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} ==>
 ={d, x})
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 ={d0, x0} ==>
 ={d, x}) => //.
progress; smt().
exlim (LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1}) => n.
have [_ [_ third]] := (ind n).
call third; first auto.
inline{1} (1) M2.f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = B).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) BC.Comb(LimB.Lim(B), LimC.Lim(C)).f.
sp.
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimB.Lim(B).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) AB.Comb(LimA.Lim(A), LimB.Lim(B)).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimB.Lim(B).f.
sp.
if => //.
sp.
seq 1 1 :
  (={glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   ={d1, x1} /\
   LimA.Lim.ctr{1} = LimA.lim /\ LimB.Lim.ctr{1} = LimB.lim - 1 /\ 
   LimC.Lim.ctr{1} = LimC.lim /\
   0 < LimB.lim).
call (_ : true); first auto.
sp.
(* apply first conjunct of ind *)
transitivity{1}
{ (d, x) <@ M1.f(d, x); }
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 d0{1} = d{2} /\ x0{1} = x{2} ==>
 ={d, x})
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 d{1} = d0{2} /\ x{1} = x0{2} /\
 0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} ==>
 ={d, x}) => //.
progress; smt(LimA.ge0_lim LimB.ge0_lim LimC.ge0_lim).
inline{2} (1) M1.f.
sim.
transitivity{2}
{ (d, x) <@ M2.f(d0, x0); }
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 d{1} = d0{2} /\ x{1} = x0{2} /\
 0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} ==>
 ={d, x})
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 ={d0, x0} ==>
 ={d, x}) => //.
progress; smt().
exlim (LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1}) => n.
have [first [_ _]] := (ind n).
call first; first auto.
inline{1} (1) M2.f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
case (d{1} = C).
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) BC.Comb(LimB.Lim(B), LimC.Lim(C)).f.
sp.
rcondt{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
inline{1} (1) LimC.Lim(C).f.
sp.
rcondt{2} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
inline{2} (1) LimC.Lim(C).f.
sp.
if => //.
sp.
seq 1 1 :
  (={glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   d1{1} = d0{2} /\ x1{1} = x0{2} /\
   LimA.Lim.ctr{1} = LimA.lim /\ LimB.Lim.ctr{1} = LimB.lim /\ 
   LimC.Lim.ctr{1} = LimC.lim - 1 /\
   0 < LimC.lim).
call (_ : true); first auto.
sp.
(* apply second conjunct of ind *)
transitivity{1}
{ (d, x) <@ M1.f(d0, x0); }
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 ={d0, x0} ==>
 ={d, x})
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 d0{1} = d{2} /\ x0{1} = x{2} /\
 0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} ==>
 ={d, x}) => //.
progress; smt(LimA.ge0_lim LimB.ge0_lim LimC.ge0_lim).
inline{2} (1) M1.f.
sim.
transitivity{2}
{ (d, x) <@ AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f(d, x); }
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 d0{1} = d{2} /\ x0{1} = x{2} /\
 0 <= LimA.Lim.ctr{1} /\ 0 <= LimB.Lim.ctr{1} /\ 0 <= LimC.Lim.ctr{1} ==>
 ={d, x})
(={glob A, glob B, glob C, LimA.Lim.ctr, LimB.Lim.ctr, LimC.Lim.ctr} /\
 ={d, x} ==>
 ={d, x}) => //.
progress; smt().
exlim (LimA.Lim.ctr{1} + LimB.Lim.ctr{1} + LimC.Lim.ctr{1}) => n.
have [_ [second _]] := (ind n).
call second; first auto.
inline{1} (1) AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f.
sim.
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
sp.
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
(* case d{1} = Env *)
rcondf{1} 1; first auto; smt(in_fset1 in_fsetU).
rcondf{2} 1; first auto; smt(in_fset1 in_fsetU).
auto.
qed.

end section.

lemma overall
      (A <: ENT{-LimA.Lim, -LimB.Lim, -LimC.Lim})
      (B <: ENT{-A, -LimA.Lim, -LimB.Lim, -LimC.Lim})
      (C <: ENT{-A, -B, -LimA.Lim, -LimB.Lim, -LimC.Lim}) :
  equiv
  [A_BC.Comb(LimA.Lim(A), BC.Comb(LimB.Lim(B), LimC.Lim(C))).f ~
   AB_C.Comb(AB.Comb(LimA.Lim(A), LimB.Lim(B)), LimC.Lim(C)).f :
   ={d, x, glob A, glob B, glob C,
     glob LimA.Lim, glob LimB.Lim, glob LimC.Lim} /\
   LimA.Lim.ctr{1} = LimA.lim /\ LimB.Lim.ctr{1} = LimB.lim /\ 
   LimC.Lim.ctr{1} = LimC.lim ==>
   ={res}].
proof.
apply (overall' A B C).
qed.

