
prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore FSet.


module type STRM = {
  proc poll () : int option
}.

abstract theory Lim.

op lim : {int | 0 <= lim} as ge0_lim.

module M (S : STRM) = {
  var ctr : int

  proc f (sum : int) : int = {
    var x : int option;
    
    x <@ S.poll ();
    while (x <> None /\ 0 < ctr) {
      sum <- sum + oget x;
      ctr <- ctr - 1;
      x <@ S.poll ();
    }

    return sum;
  }

  proc sum () : int = {
    var r : int;
    r <@ f (0);
    return r;
  }

}.

end Lim.


abstract theory LimPos.

op lim : {int | 0 <= lim} as ge0_lim.

module M (S : STRM) = {
  var ctr : int

  proc f (sum : int) : int = {
    var x : int option;
    
    x <@ S.poll ();
    while (x <> None /\ 0 < ctr) {
      if (0 < oget x) {
        sum <- sum + oget x;
      }
      ctr <- ctr - 1;
      x <@ S.poll ();
    }

    return sum;
  }

  proc sum () : int = {
    var r : int;
    r <@ f (0);
    return r;
  }

}.

end LimPos.


clone Lim as L.
clone LimPos as P.



lemma overall (S <: STRM{-L.M, -P.M}) :
  equiv [ L.M(S).sum ~ P.M(S).sum :
      L.M.ctr{1} = L.lim /\
      P.M.ctr{2} = P.lim /\
      L.lim = P.lim /\
      ={glob S}
      ==>
      res{1} <= res{2}
    ].
proof.
proc.
inline.
sp. wp.
seq 1 1 : (#pre /\ ={x}).
call (_ : true) => //.

while (={glob S} /\ ={x} /\ L.M.ctr{1} = P.M.ctr{2} /\ sum{1} <= sum{2}).
if{2}.
sp.
call (_ : true).
auto. progress.
smt().

sp. call (_ : true).
auto. progress.
smt().

auto. progress => /#.
qed.







abstract theory NoLim.

module M (S : STRM) = {

  proc f (sum : int) : int = {
    var x : int option;
    
    x <@ S.poll ();
    while (x <> None) {
      sum <- sum + oget x;
      x <@ S.poll ();
    }

    return sum;
  }

  proc sum () : int = {
    var r : int;
    r <@ f (0);
    return r;
  }

}.

end NoLim.


abstract theory NoLimPos.

module M (S : STRM) = {

  proc f (sum : int) : int = {
    var x : int option;
    
    x <@ S.poll ();
    while (x <> None) {
      if (0 < oget x) {
        sum <- sum + oget x;
      }
      x <@ S.poll ();
    }

    return sum;
  }

  proc sum () : int = {
    var r : int;
    r <@ f (0);
    return r;
  }

}.

end NoLimPos.

clone NoLim as NL.
clone NoLimPos as NP.

lemma overall_nolim (S <: STRM{-NL.M, -NP.M}) :
  equiv [ NL.M(S).sum ~ NP.M(S).sum :
      ={glob S}
      ==>
      res{1} <= res{2}
    ].
proof.
proc.
inline.
sp. wp.
seq 1 1 : (#pre /\ ={x}).
call (_ : true) => //.

while (={glob S, x} /\ sum{1} <= sum{2}).
if{2}.
sp.
call (_ : true).
auto. progress.
smt().

sp. call (_ : true).
auto. progress.
smt().

auto.
qed.










lemma ind (n : int) (S <: STRM{-L.M, -P.M}) :
 equiv [ L.M(S).f ~ P.M(S).f :
   ={glob S, sum} /\
   0 <= n /\
   L.M.ctr{1} = n /\
   P.M.ctr{2} = n
   ==>
   res{1} <= res{2}
 ].
proof.
case (n < 0) => [le0_n | not_le_n].
exfalso => /#.
have : 0 <= n by smt().
clear not_le_n.
elim n => [| n ge0_n IH].

(* base case *)
proc.
seq 1 1 : (#pre /\ ={x}).
call (_ : true); auto.

rcondf{1} 1; auto.
rcondf{2} 1; auto.

(* inductive *)
proc.
seq 1 1 : (#pre /\ ={x}).
call (_ : true); auto.

case (x{1} = None).

rcondf{1} 1; auto.
rcondf{2} 1; auto.

(* x is not none *)
(*case (0 < L.M.ctr{1}).*)
rcondt{1} 1; auto. progress; smt().
rcondt{2} 1; auto. progress; smt().

if{2}.
(* if true *)
sp.

(* clean up pre *)
elim*; auto.
conseq (_ : ={glob S, sum} /\ 0 <= n /\ L.M.ctr{1} = n /\ P.M.ctr{2} = n ==> sum{1} <= sum{2}).
smt().

(* get LHS closer to IH *)
transitivity{1} { 
  sum <@ L.M(S).f (sum);
} 
(={glob S, sum, L.M.ctr} /\ 0 <= n /\ L.M.ctr{1} = n
  ==> ={sum}) 
(={glob S, sum} /\ 0 <= n /\ L.M.ctr{1} = n /\ P.M.ctr{2} = n
  ==> sum{1} <= sum{2}).
smt(). smt().
inline L.M(S).f.
sim.

(* get RHS closer to IH *)
symmetry.
transitivity{1} {
  sum <@ P.M(S).f (sum);
}
(={glob S, sum, P.M.ctr} /\ 0 <= n /\ P.M.ctr{1} = n
  ==> sum{1} = sum{2})
(={glob S, sum} /\ 0 <= n /\ P.M.ctr{1} = n /\ L.M.ctr{2} = n
  ==> sum{2} <= sum{1}).
smt(). smt().
inline P.M(S).f.
sim.
symmetry.
call IH => //.

(* if false *)
sp. admit.

qed.

lemma overall_ind (S <: STRM{-L.M, -P.M}) :
  equiv [ L.M(S).sum ~ P.M(S).sum :
      L.M.ctr{1} = L.lim /\
      P.M.ctr{2} = P.lim /\
      L.lim = P.lim /\
      ={glob S}
      ==>
      res{1} <= res{2}
    ].
proof.
proc.
call (ind L.lim S).
auto; progress; smt(L.ge0_lim).
qed.

