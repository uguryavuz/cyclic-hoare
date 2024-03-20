
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
sp. admit.

(* if false *)
sp. admit.

qed.

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
call (ind L.lim S).
auto; progress; smt(L.ge0_lim).
qed.

