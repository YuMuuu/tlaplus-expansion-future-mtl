---------------------------- MODULE future_mtl_spec -------------------------
EXTENDS Naturals, Sequences, TLC, future_mtl

CONSTANT MaxT
VARIABLES p, q, t

(***************************************************************************)
(* 最小実行モデル                                                             *)
(***************************************************************************)
P(i) == p[i]
Q(i) == q[i]

\* 追加のテスト用オペレータ
From2True(i) == i >= 2
PhiU(i) == i < 3
PsiU(i) == i = 3

Init ==
  /\ p = [i \in 0..MaxT |-> IF i \in 1..3 THEN TRUE ELSE FALSE]
  /\ q = [i \in 0..MaxT |-> i = 3]
  /\ t = 0

Step ==
  /\ UNCHANGED <<p, q>>
  /\ IF t < MaxT THEN t' = t + 1 ELSE t' = t

vars == <<p, q, t>>
Spec == Init /\ [][Step]_vars /\ WF_vars(Step)


\* F_I
Prop_FI_Closed_Pos == [](t <= 2 => F_I(Closed(1,3), P, t, MaxT))
Prop_FI_Closed_Neg == [](t >= 3 => ~F_I(Closed(1,3), P, t, MaxT))
Prop_FI_From_Pos   == [](t <= MaxT - 2 => F_I(From(2), From2True, t, MaxT))
Prop_FI_From_Neg   == [](~F_I(From(4), P, t, MaxT))

\* G_I
Prop_GI_From_Pos   == []G_I(From(2), From2True, t, MaxT)
Prop_GI_Closed_Pos == [](t = 0 => G_I(Closed(1,3), P, t, MaxT))
Prop_GI_Closed_Neg == []((t >= 3 /\ t <= MaxT - 1) => ~G_I(Closed(1,3), P, t, MaxT))

\* 端点・空区間の挙動
Prop_FI_Closed_VacuousNeg == [](t = MaxT => ~F_I(Closed(1,3), P, t, MaxT))
Prop_GI_Closed_VacuousPos == [](t = MaxT =>  G_I(Closed(1,3), P, t, MaxT))
Prop_FI_From_Boundary_Neg == [](t = MaxT - 1 => ~F_I(From(2), From2True, t, MaxT))

\* U_I
Prop_UI_Pos == [](t <= 3 => U_I(Closed(0,3), PhiU, PsiU, t, MaxT))
Prop_UI_Neg == [](t = 0 => ~U_I(Closed(0,2), PhiU, PsiU, t, MaxT))

\* untilAt の性質                                                             *)
\* k=3 で PsiU が発生、直前の 0..2 区間は PhiU が連続で真 → 成立
Prop_UA_k3_Pos == [](t = 0 => UntilAt(3, PhiU, PsiU, t, MaxT))

\* k=2 では PsiU が現れない → 不成立
Prop_UA_k2_Neg == [](t = 0 => ~UntilAt(2, PhiU, PsiU, t, MaxT))

\* t を 1 だけ進めると、k=3 における PsiU は (t+3)=4 で偽、かつ PhiU 連続性も崩れる → 不成立
Prop_UA_k3_Neg_Shift == [](t = 1 => ~UntilAt(3, PhiU, PsiU, t, MaxT))

\* 範囲外ガード: t=MaxT ではいかなる k>=1 も範囲外 → 不成立
Prop_UA_OutOfRange_Neg == [](t = MaxT => ~UntilAt(1, PhiU, PsiU, t, MaxT))

\* U_I([0,3]) と「k=0..3 のいずれかで untilAt 成立」の同値性
Prop_UA_Equiv_UI == [](
  U_I(Closed(0,3), PhiU, PsiU, t, MaxT)
  <=> (\E k \in 0..3: UntilAt(k, PhiU, PsiU, t, MaxT))
)

=============================================================================
