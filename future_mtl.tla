------------------------------ MODULE future_mtl -----------------------------
EXTENDS Naturals, Sequences, TLC

VARIABLES p, q, t

(***************************************************************************)
(* interval（区間） の定義                                                               *)
(***************************************************************************)
Interval == [type : {"closed", "from"}, l : Nat, u : Nat]

MaxT == 6 \* 実行したいモデルによってtimeの最大値は調整する
\* future-MTLでは本来は未来時間は無限を扱えるが、TLCで実行する場合は有限時間にしなければ実行が終わらない

Closed(l, u) == [type |-> "closed", l |-> l, u |-> u]
From(l)      == [type |-> "from",   l |-> l, u |-> 0]
Min(a, b) == IF a <= b THEN a ELSE b
Upper(I) == IF I.type = "closed" THEN Min(I.u, MaxT - t) ELSE MaxT - t

(***************************************************************************)
(* Metric Finally, Globally, Until                                          *)
(***************************************************************************)
F_I(I, Phi(_)) ==
  \E k \in I.l .. Upper(I): Phi(t + k)

G_I(I, Phi(_)) ==
  \A k \in I.l .. Upper(I): Phi(t + k)

U_I(I, Phi(_), Psi(_)) ==
  \E k \in I.l .. Upper(I): /\ Psi(t + k)
                           /\ \A m \in I.l .. k - 1: Phi(t + m)

(***************************************************************************)
(* untilAt の定義: 長さ k ちょうどで ψ が起こる展開                          *)
(***************************************************************************)
\* Omit UntilAt in minimal model


P(i) == p[i]
Q(i) == q[i]

\* 追加のテスト用オペレータ
From2True(i) == i >= 2
PhiU(i) == i < 3
PsiU(i) == i = 3

\* 時間カウンタ付きの最小実行モデル
Init == /\ p = [i \in 0..MaxT |-> IF i \in 1..3 THEN TRUE ELSE FALSE]
        /\ q = [i \in 0..MaxT |-> i = 3]
        /\ t = 0

Step == /\ UNCHANGED <<p, q>>
        /\ IF t < MaxT THEN t' = t + 1 ELSE t' = t

vars == <<p, q, t>>

Spec == Init /\ [][Step]_vars /\ WF_vars(Step)

\* テスト用プロパティ（すべて PROPERTIES で検査）
\* F_I: t<=2 なら [1,3] に t+k ∈ {1,2,3} があり P(t+k)=TRUE が見つかる → 成立
Prop_FI_Closed_Pos == [](t <= 2 => F_I(Closed(1,3), P))
\* F_I: t>=3 では [t+1,t+3] ⊆ {4,5,6} で P は常に FALSE → 不成立
Prop_FI_Closed_Neg == [](t >= 3 => ~F_I(Closed(1,3), P))
\* F_I: From(2) では述語 From2True(i) == (i>=2)。t<=MaxT-2 なら必ず満たす i がある → 成立
Prop_FI_From_Pos   == [](t <= MaxT - 2 => F_I(From(2), From2True))
\* F_I: From(4) で P は未来に二度と TRUE にならない（P は 1..3 のみ TRUE）→ 不成立
Prop_FI_From_Neg   == [](~F_I(From(4), P))

\* G_I: From(2) は任意の k>=2 で i>=2 が真 → 常に成立
Prop_GI_From_Pos   == []G_I(From(2), From2True)
\* G_I: t=0 の [1,3] は全て P=TRUE → 成立
Prop_GI_Closed_Pos == [](t = 0 => G_I(Closed(1,3), P))
\* G_I: 3<=t<=MaxT-1 では窓に 4 以上が含まれ P=FALSE の点が存在 → 不成立
Prop_GI_Closed_Neg == []((t >= 3 /\ t <= MaxT - 1) => ~G_I(Closed(1,3), P))

\* 端点・空区間の挙動確認
\* t=MaxT では Upper([1,3])=0 → 存在量化は空集合で偽、全称は空集合で真
Prop_FI_Closed_VacuousNeg == [](t = MaxT => ~F_I(Closed(1,3), P))
Prop_GI_Closed_VacuousPos == [](t = MaxT => G_I(Closed(1,3), P))
\* t=MaxT-1 では From(2) の k>=2 を満たす余地がなくなる → 不成立
Prop_FI_From_Boundary_Neg == [](t = MaxT - 1 => ~F_I(From(2), From2True))

\* U_I: [0,3] のどこか（k=3）で Psi(i)==(i=3) が生起し、それ以前は PhiU(i)==(i<3) が連続して成り立つ → 成立
Prop_UI_Pos        == [](t <= 3 => U_I(Closed(0,3), PhiU, PsiU))
\* U_I: [0,2] の窓内には Psi(i)==(i=3) が出現しない → 不成立
Prop_UI_Neg        == [](t = 0 => ~U_I(Closed(0,2), PhiU, PsiU))

=============================================================================
=============================================================================
