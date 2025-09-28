----------------------------- MODULE future_mtl -----------------------------
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(* interval（区間）の定義／ユーティリティ                                      *)
(***************************************************************************)
Interval == [type : {"closed", "from"}, l : Nat, u : Nat]

Closed(l, u) == [type |-> "closed", l |-> l, u |-> u]
From(l)      == [type |-> "from",   l |-> l, u |-> 0]

Min(a, b) == IF a <= b THEN a ELSE b

(*
  Upper(I, t, MaxT):
  - "closed" のとき: 上端 u と (MaxT - t) の小さい方
  - "from"   のとき: t からの残り時間 MaxT - t
*)
Upper(I, t, MaxT) ==
  IF I.type = "closed" THEN Min(I.u, MaxT - t) ELSE MaxT - t

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

=============================================================================
