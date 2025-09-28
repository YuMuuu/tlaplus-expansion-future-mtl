----------------------------- MODULE future_mtl -----------------------------
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(* interval（区間）の定義／ユーティリティ                                      *)
(***************************************************************************)
Interval ==
  [type : {"closed"}, l : Nat, u : Nat]         \cup
  [type : {"from"},   l : Nat]                  

Closed(l, u) == [type |-> "closed", l |-> l, u |-> u]
From(l)       == [type |-> "from",  l |-> l]

IsClosed(I) == I.type = "closed"
IsFrom(I)   == I.type = "from"

Min(a, b) == IF a <= b THEN a ELSE b

(***************************************************************************)
(* 区間の上端（検査地平 MaxT を考慮）                                      *)
(***************************************************************************)
Upper(I, t, MaxT) ==
  IF IsClosed(I)
  THEN Min(I.u, MaxT - t)
  ELSE MaxT - t


(***************************************************************************)
(* Metric Finally, Globally, Until                                          *)
(***************************************************************************)
F_I(I, Phi(_), t, MaxT) ==
  \E k \in I.l .. Upper(I, t, MaxT): Phi(t + k)

G_I(I, Phi(_), t, MaxT) ==
  \A k \in I.l .. Upper(I, t, MaxT): Phi(t + k)

U_I(I, Phi(_), Psi(_), t, MaxT) ==
  \E k \in I.l .. Upper(I, t, MaxT): /\ Psi(t + k)
                                     /\ \A m \in I.l .. k - 1: Phi(t + m)

(***************************************************************************)
(* ちょうど k ステップ後に Psi が到達し、それまで Phi が保たれる                *)
(* UntilAt(k, Phi, Psi, t, MaxT)                                           *)
(* - 時間は整数。現在時刻は t、終端は MaxT。                                *)
(* - k は 0..(MaxT - t) の範囲内にある必要がある。                           *)
(***************************************************************************)
WithinRange(k, t, MaxT) == k \in 0..(MaxT - t)

UntilAt(k, Phi(_), Psi(_), t, MaxT) ==
  /\ WithinRange(k, t, MaxT)
  /\ Psi(t + k)
  /\ \A m \in 0..k-1: Phi(t + m)

=============================================================================