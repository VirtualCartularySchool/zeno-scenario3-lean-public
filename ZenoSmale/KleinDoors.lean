/-
# ZenoSmale.KleinDoors : D7 — 形成写像、二つの扉、複素表示と、動く面の上の比較の関係

構想の記録の「実数解を持たない」「非実数解で交叉」（第 3.1 版 付録 C.3、C.4）について、第 3.1 版が
すでに定義している対象（形成写像 X = 1/w ∈ ℝ ∪ {∞}、命題 2.3 の二つの扉、射影座標 x̂、複素表示 𝔾）だけを
使って、どの方程式がどこに解をもつかを定理として述べる。新しい方程式は導入しない。

1. **形成後の追いつきの方程式（助変数の水準）**。X_A(t) = 1/g(t)、X_T(t) = 1/(r g(t)) を ℝ ∪ {∞} の値と
   すると、X_A(t) = X_T(t) の解は t∗ だけであり、そこでの値は ∞ である。二人の X が同じ実数になる時刻は
   ない（`formed_meeting_iff`、`formed_meeting_value`、`formed_no_real_solution`）。差 X_A − X_T は t∗ の
   前で負、後で正である。これは競走と形成写像だけで決まり、面の模型によらない。
2. **扉 0（位置の水準、一般形）**。℘ を通らない連続な道の x̂ が正から負へ移るなら、x̂ = 0 となる時刻が
   あり、そのとき点は対称面 q₁ = 0 の上にあって、ホーン対 G の像の上にはない（`door_zero`）。℘ を
   通らない二つの連続な道の x̂ の比較が正から負へ移るなら、x̂ が一致する時刻がある
   （`xhat_compare_zero_of_avoid`）。対偶として、比較が零点を持たなければ、どちらかの道が ℘ を通る
   （`passes_wp_of_no_compare_zero`）。理想形は後者の場合であり、t∗ に二人とも ℘ にいて、t ≠ t∗ では
   x̂ は一致しない（`ideal_door_infty`）。
3. **静的な面の上の走者**。二人のどちらにも、t∗ の前に、対称面 q₁ = 0 を ℘ でない点で横切る時刻が
   ある（`static_door_zero_T`、`static_door_zero_A`）。t∗ には二人は q₁ = −aa₀ < 0 の中央円の上にいて、
   x̂ は一致する（既存の `compare_xhat`）。
4. **動く面の上の走者**。アキレスには t∗ の前に、亀には t∗ の後に、首の中で対称面を ℘ でない点で
   横切る時刻がある。その点はホーン対の上にない（`door_zero_A`、`door_zero_T`）。零点が一つだけで
   あることは主張しない。形成後の方程式のただ一つの解 t∗ には、
   二人の助変数はともに w = 0 であり、二人は段 F_{1/2} の中央円 {F_{1/2}(0, v)} の上の異なる点にいる
   （`dyn_centre`）。
5. **自由度**。中央での二人の角度が 2π の整数倍だけ違えば、二人は t∗ に同じ点にいる
   （`dyn_collision_of_centre_angle`、`run_collision_of_centre_angle`）。したがって非衝突は中央の角度の
   選び方による（`DynamicPassage.centre_angle_ne`）。主定理の導線では角度の差は π + 2πn₁ である
   （`centre_angle_diff`）。
6. **複素表示との関係**。第 3.1 版の複素表示 𝔾（`GG`）で、純虚数の助変数 z = iy の点は対称面の上に
   ある。逆に、対称面の上の ℘ でない点で ℘ からの距離が 1/2 以下のものは、ある y ∈ (0, 1] と v について
   𝔾(iy, v) に等しい（`GG_imaginary_fst`、`mirror_point_imaginary`）。したがって、首が ℘ の半径 1/2 の
   球に入るとき、動く面の上の二人が対称面を横切る点は、𝔾 の純虚数の助変数の点である
   （`door_zero_T_imaginary`、`door_zero_A_imaginary`）。
7. **複素迂回の形との非両立**。第 3.1 版 定理 8.9 の (i) の形（同じ時刻に、共通の複素助変数 z について
   A = κ𝔾(z, ·)、T = κ𝔾(rz, ·)）では、x̂(T) と x̂(A) は同じ符号をもつ。動く面の上では t∗ に
   x̂(T) > 0 > x̂(A) なので、t∗ の二人の位置はこの形に書けない（`no_common_complex_parameter`）。
-/
import ZenoSmale.KleinConception
import Zeno.Flex

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open Zeno.Model

/-! ### 形成後の追いつきの方程式（助変数の水準。面の模型によらない） -/

/-- **形成後の追いつきの方程式**：X_A(t) = X_T(t)（X = 1/w ∈ ℝ ∪ {∞}）の解は t∗ だけである。 -/
theorem formed_meeting_iff (R : Race) (t : ℝ) :
    invOP (R.g t) = invOP (R.r * R.g t) ↔ t = R.tstar := by
  constructor
  · intro h
    by_contra hne
    have hg : R.g t ≠ 0 := fun h0 => hne ((R.g_eq_zero_iff t).mp h0)
    have hrg : R.r * R.g t ≠ 0 := mul_ne_zero R.r_pos.ne' hg
    rw [invOP_of_ne hg, invOP_of_ne hrg] at h
    have h2 : (R.g t)⁻¹ = (R.r * R.g t)⁻¹ := OnePoint.coe_injective h
    have h3 : R.g t = R.r * R.g t := inv_injective h2
    have h4 : (1 - R.r) * R.g t = 0 := by linarith
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith [R.r_lt_one]
    · exact hg h5
  · rintro rfl
    rw [R.g_tstar, mul_zero]

/-- その解での値は ∞ である。 -/
theorem formed_meeting_value (R : Race) :
    invOP (R.g R.tstar) = OnePoint.infty ∧ invOP (R.r * R.g R.tstar) = OnePoint.infty := by
  rw [R.g_tstar, mul_zero]
  exact ⟨invOP_zero, invOP_zero⟩

/-- **形成後の追いつきの方程式は実数解を持たない**：二人の射影座標 X が同じ実数になる時刻はない。 -/
theorem formed_no_real_solution (R : Race) :
    ¬ ∃ t x : ℝ, invOP (R.g t) = (x : OnePoint ℝ) ∧ invOP (R.r * R.g t) = (x : OnePoint ℝ) := by
  rintro ⟨t, x, hA, hT⟩
  have ht : t = R.tstar := (formed_meeting_iff R t).mp (hA.trans hT.symm)
  rw [ht, (formed_meeting_value R).1] at hA
  exact OnePoint.infty_ne_coe x hA

/-- t ≠ t∗ での差：X_A − X_T = (r − 1)/(r g)。 -/
theorem formed_diff (R : Race) {t : ℝ} (ht : t ≠ R.tstar) :
    (R.g t)⁻¹ - (R.r * R.g t)⁻¹ = (R.r - 1) / (R.r * R.g t) := by
  have hg : R.g t ≠ 0 := fun h0 => ht ((R.g_eq_zero_iff t).mp h0)
  have hr := R.r_pos.ne'
  field_simp

/-- 差 X_A − X_T は t∗ の前で負である。 -/
theorem formed_diff_neg (R : Race) {t : ℝ} (ht : t < R.tstar) :
    (R.g t)⁻¹ - (R.r * R.g t)⁻¹ < 0 := by
  have hT := R.tstar_pos
  have hg : 0 < R.g t := by
    rw [R.g_eq]
    have : t / R.tstar < 1 := by rw [div_lt_one hT]; exact ht
    linarith
  rw [formed_diff R ht.ne]
  exact div_neg_of_neg_of_pos (by linarith [R.r_lt_one]) (mul_pos R.r_pos hg)

/-- 差 X_A − X_T は t∗ の後で正である。 -/
theorem formed_diff_pos (R : Race) {t : ℝ} (ht : R.tstar < t) :
    0 < (R.g t)⁻¹ - (R.r * R.g t)⁻¹ := by
  have hT := R.tstar_pos
  have hg : R.g t < 0 := by
    rw [R.g_eq]
    have : 1 < t / R.tstar := by rw [lt_div_iff₀ hT]; linarith
    linarith
  rw [formed_diff R ht.ne']
  exact div_pos_of_neg_of_neg (by linarith [R.r_lt_one]) (mul_neg_of_pos_of_neg R.r_pos hg)

/-! ### 扉 0：℘ を通らない道の x̂ は、対称面 q₁ = 0 で符号を変える -/

theorem continuousOn_xhat {f : ℝ → V3} {s : Set ℝ} (hf : ContinuousOn f s)
    (hne : ∀ t ∈ s, f t ≠ wp) : ContinuousOn (fun t => xhat (f t)) s := by
  have h1 : ContinuousOn (fun t => (f t).1) s := continuous_fst.comp_continuousOn hf
  have h2 : ContinuousOn (fun t => nsq (f t)) s := continuous_nsq.comp_continuousOn hf
  exact h1.div h2 fun t ht => (nsq_pos_of_ne (hne t ht)).ne'

/-- ℘ でない点で x̂ = 0 なら、その点は対称面 q₁ = 0 の上にある。 -/
theorem fst_eq_zero_of_xhat {q : V3} (hq : q ≠ wp) (h : xhat q = 0) : q.1 = 0 := by
  unfold xhat at h
  rcases div_eq_zero_iff.mp h with h1 | h1
  · exact h1
  · exact absurd h1 (nsq_pos_of_ne hq).ne'

/-- 対称面の上の ℘ でない点は、ホーン対 G の像の上にない。 -/
theorem G_ne_of_fst_zero {q : V3} (hq : q ≠ wp) (h : q.1 = 0) (w v : ℝ) : G w v ≠ q := by
  intro hG
  have h2 : w / Zeno.Model.D w = 0 := by
    have h1 : (G w v).1 = 0 := by rw [hG]; exact h
    exact h1
  have hw : w = 0 := by
    rcases div_eq_zero_iff.mp h2 with h3 | h3
    · exact h3
    · exact absurd h3 (Zeno.Model.D_ne w)
  rw [hw, G_zero] at hG
  exact hq hG.symm

/-- **扉 0（一般形）**：℘ を通らない連続な道の x̂ が正から負へ移るなら、x̂ = 0 となる時刻がある。そのとき
道の点は対称面 q₁ = 0 の上にあり、ホーン対 G の像の上にはない。 -/
theorem door_zero {f : ℝ → V3} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hne : ∀ t ∈ Icc a b, f t ≠ wp) (ha : 0 < xhat (f a)) (hb : xhat (f b) < 0) :
    ∃ t ∈ Ioo a b, xhat (f t) = 0 ∧ (f t).1 = 0 ∧ ∀ w v : ℝ, G w v ≠ f t := by
  have hcont := continuousOn_xhat hf hne
  obtain ⟨t, ht, hval⟩ := intermediate_value_Ioo' hab hcont (show (0 : ℝ) ∈ Ioo _ _ from ⟨hb, ha⟩)
  have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have h0 : xhat (f t) = 0 := hval
  have h1 := fst_eq_zero_of_xhat (hne t htI) h0
  exact ⟨t, ht, h0, h1, G_ne_of_fst_zero (hne t htI) h1⟩

/-- **実の比較の零点の必然性**：℘ を通らない二つの連続な道について、x̂ の比較が正から負へ移るなら、
x̂ が一致する時刻がある。 -/
theorem xhat_compare_zero_of_avoid {T A : ℝ → V3} {a b : ℝ} (hab : a ≤ b)
    (hT : ContinuousOn T (Icc a b)) (hA : ContinuousOn A (Icc a b))
    (hT0 : ∀ t ∈ Icc a b, T t ≠ wp) (hA0 : ∀ t ∈ Icc a b, A t ≠ wp)
    (ha : xhat (A a) < xhat (T a)) (hb : xhat (T b) < xhat (A b)) :
    ∃ t ∈ Ioo a b, xhat (T t) = xhat (A t) := by
  have hcont := (continuousOn_xhat hT hT0).sub (continuousOn_xhat hA hA0)
  have hmem : (0 : ℝ) ∈ Ioo (xhat (T b) - xhat (A b)) (xhat (T a) - xhat (A a)) :=
    ⟨by linarith, by linarith⟩
  obtain ⟨t, ht, hval⟩ := intermediate_value_Ioo' hab hcont hmem
  have h3 : xhat (T t) - xhat (A t) = 0 := hval
  exact ⟨t, ht, by linarith⟩

/-- **対偶**：x̂ の比較が正から負へ移るのに零点を持たなければ、どちらかの道が ℘ を通る。 -/
theorem passes_wp_of_no_compare_zero {T A : ℝ → V3} {a b : ℝ} (hab : a ≤ b)
    (hT : ContinuousOn T (Icc a b)) (hA : ContinuousOn A (Icc a b))
    (ha : xhat (A a) < xhat (T a)) (hb : xhat (T b) < xhat (A b))
    (hno : ∀ t ∈ Ioo a b, xhat (T t) ≠ xhat (A t)) :
    ∃ t ∈ Icc a b, T t = wp ∨ A t = wp := by
  by_contra hcon
  push Not at hcon
  obtain ⟨t, ht, he⟩ := xhat_compare_zero_of_avoid hab hT hA (fun t ht => (hcon t ht).1)
    (fun t ht => (hcon t ht).2) ha hb
  exact hno t ht he

/-- **理想形は扉 ∞ を通る**：t∗ に二人とも ℘ にいて、t ≠ t∗ では x̂ は一致しない。 -/
theorem ideal_door_infty (R : Race) :
    R.idealT R.tstar = wp ∧ R.idealA R.tstar = wp ∧
      ∀ t, t ≠ R.tstar → xhat (R.idealT t) ≠ xhat (R.idealA t) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [Race.idealT, R.g_tstar, mul_zero, G_zero]
  · simp only [Race.idealA, R.g_tstar, G_zero]
  · intro t ht h
    have hg : R.g t ≠ 0 := fun h0 => ht ((R.g_eq_zero_iff t).mp h0)
    have hrg : R.r * R.g t ≠ 0 := mul_ne_zero R.r_pos.ne' hg
    rw [Race.idealT, Race.idealA, xhat_G hrg, xhat_G hg] at h
    have h3 := (div_eq_div_iff hrg hg).mp h
    have h4 : (1 - R.r) * R.g t = 0 := by linarith
    rcases mul_eq_zero.mp h4 with h5 | h5
    · linarith [R.r_lt_one]
    · exact hg h5

/-! ### 動く面の上の走者：対称面の通過と、t∗ での中央円 -/

section DynDoors

variable {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3} {F : ℝ → ℝ → ℝ → V3}
  {Vt Va : ℝ → ℝ}

/-- **亀には、t∗ の後に、首の中で対称面を横切る時刻がある**：x̂ = 0、q₁ = 0 となる時刻が (t∗, 2t∗) に
あり、その点はホーン対の上にない（零点の一意性は主張しない）。 -/
theorem door_zero_T
    (P : DynamicPassage R w₀ (R.r ^ n₁) ε n₁ S X F (VtR (R.r ^ n₁)) (VaR R.r w₀ (R.r ^ n₁) n₁))
    (E : DynamicEffects R w₀ n₁ F) (hn : 1 ≤ n₁) :
    ∃ t ∈ Ioo R.tstar (2 * R.tstar),
      xhat (dynT R w₀ F (VtR (R.r ^ n₁)) t) = 0 ∧ (dynT R w₀ F (VtR (R.r ^ n₁)) t).1 = 0 ∧
      (∀ w v : ℝ, G w v ≠ dynT R w₀ F (VtR (R.r ^ n₁)) t) ∧ |R.r * R.g t| < R.r ^ n₁ := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hc : 0 < R.r ^ n₁ := pow_pos hr0 n₁
  have hpow : R.r ^ n₁ ≤ R.r := pow_le_of_le_one hr0.le hr1.le (by omega)
  have hsub : Icc R.tstar (2 * R.tstar) ⊆ Icc 0 (2 * R.tstar) := Icc_subset_Icc_left hT.le
  have hg2 : R.g (2 * R.tstar) = -1 := by rw [R.g_eq]; field_simp; ring
  have h2mem : 2 * R.tstar ∈ Icc 0 (2 * R.tstar) := ⟨by linarith, le_rfl⟩
  have hTe := P.xhat_shore_T hc h2mem
    (by rw [hg2, mul_neg, mul_one, abs_neg, abs_of_pos hr0]; exact hpow)
  have hb : xhat (dynT R w₀ F (VtR (R.r ^ n₁)) (2 * R.tstar)) < 0 := by
    rw [hTe, hg2, mul_neg, mul_one, div_neg]
    have : 0 < 1 / R.r := by positivity
    linarith
  obtain ⟨t, ht, h0, h1, hG⟩ := door_zero (by linarith : R.tstar ≤ 2 * R.tstar)
    P.smooth_T.continuous.continuousOn (fun t ht => E.avoids_T t (hsub ht)) E.xhat_sign.1 hb
  refine ⟨t, ht, h0, h1, hG, ?_⟩
  by_contra hcon
  push Not at hcon
  have htI : t ∈ Icc 0 (2 * R.tstar) := hsub (Ioo_subset_Icc_self ht)
  rw [P.xhat_shore_T hc htI hcon] at h0
  have h3 : R.r * R.g t = 0 := by
    rcases div_eq_zero_iff.mp h0 with h4 | h4
    · exact absurd h4 one_ne_zero
    · exact h4
  rw [h3, abs_zero] at hcon
  linarith

/-- **アキレスには、t∗ の前に、首の中で対称面を横切る時刻がある**（零点の一意性は主張しない）。 -/
theorem door_zero_A
    (P : DynamicPassage R w₀ (R.r ^ n₁) ε n₁ S X F (VtR (R.r ^ n₁)) (VaR R.r w₀ (R.r ^ n₁) n₁))
    (E : DynamicEffects R w₀ n₁ F) :
    ∃ t ∈ Ioo 0 R.tstar,
      xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) = 0 ∧
      (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t).1 = 0 ∧
      (∀ w v : ℝ, G w v ≠ dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) ∧ |R.g t| < R.r ^ n₁ := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hc : 0 < R.r ^ n₁ := pow_pos hr0 n₁
  have hpow : R.r ^ n₁ ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have hsub : Icc 0 R.tstar ⊆ Icc 0 (2 * R.tstar) := Icc_subset_Icc_right (by linarith)
  have hg0 : R.g 0 = 1 := by rw [R.g_eq]; simp
  have h0mem : (0 : ℝ) ∈ Icc 0 (2 * R.tstar) := ⟨le_rfl, by linarith⟩
  have hAe := P.xhat_shore_A hc h0mem (by rw [hg0, abs_one]; exact hpow)
  have ha : 0 < xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) 0) := by
    rw [hAe, hg0]; norm_num
  obtain ⟨t, ht, h0, h1, hG⟩ := door_zero hT.le
    P.smooth_A.continuous.continuousOn (fun t ht => E.avoids_A t (hsub ht)) ha E.xhat_sign.2
  refine ⟨t, ht, h0, h1, hG, ?_⟩
  by_contra hcon
  push Not at hcon
  have htI : t ∈ Icc 0 (2 * R.tstar) := hsub (Ioo_subset_Icc_self ht)
  rw [P.xhat_shore_A hc htI hcon] at h0
  have h3 : R.g t = 0 := by
    rcases div_eq_zero_iff.mp h0 with h4 | h4
    · exact absurd h4 one_ne_zero
    · exact h4
  rw [h3, abs_zero] at hcon
  linarith

/-- **t∗ での中央円**：形成後の追いつきの方程式のただ一つの解 t∗ には、二人の助変数はともに w = 0 であり、
二人は段 F_{1/2} の中央円 {F_{1/2}(0, v)} の上の異なる点にいる。 -/
theorem dyn_centre (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va) :
    dynT R w₀ F Vt R.tstar = F (1 / 2) 0 (Vt 0) ∧ dynA R w₀ F Va R.tstar = F (1 / 2) 0 (Va 0) ∧
      F (1 / 2) 0 (Vt 0) ≠ F (1 / 2) 0 (Va 0) := by
  have eT : dynT R w₀ F Vt R.tstar = F (1 / 2) 0 (Vt 0) := by
    simp only [dynT, P.centred, R.g_tstar, mul_zero]
  have eA : dynA R w₀ F Va R.tstar = F (1 / 2) 0 (Va 0) := by
    simp only [dynA, P.centred, R.g_tstar]
  refine ⟨eT, eA, ?_⟩
  rw [← eT, ← eA]
  exact P.no_collision R.tstar R.tstar_mem

end DynDoors

/-! ### 静的な面の上の走者：t∗ の前に対称面を横切る時刻がある -/

section StaticDoors

variable (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (n₁ : ℕ) (hc : w₀ ≤ R.r ^ n₁)

include h0 h1 hc in
/-- **静的な面の上の亀には、t∗ の前に対称面を横切る時刻がある**（t∗ には q₁ = −aa₀ < 0 の中央円の上に
いる）。 -/
theorem static_door_zero_T (hn : 1 ≤ n₁) :
    ∃ t ∈ Ioo 0 R.tstar,
      xhat (R.runT (Shat w₀) (VtR (R.r ^ n₁)) t) = 0 ∧
      (R.runT (Shat w₀) (VtR (R.r ^ n₁)) t).1 = 0 ∧
      ∀ w v : ℝ, G w v ≠ R.runT (Shat w₀) (VtR (R.r ^ n₁)) t := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have P := klein_passage R h0 h1 n₁ hc
  have hpow : R.r ^ n₁ ≤ R.r := pow_le_of_le_one hr0.le hr1.le (by omega)
  have hg0 : R.g 0 = 1 := by rw [R.g_eq]; simp
  have h0mem : (0 : ℝ) ∈ Icc 0 (2 * R.tstar) := ⟨le_rfl, by linarith⟩
  have ha : 0 < xhat (R.runT (Shat w₀) (VtR (R.r ^ n₁)) 0) := by
    rw [P.agree_T 0 h0mem (by rw [hg0, mul_one, abs_of_pos hr0]; exact hpow), Race.idealT, hg0,
      mul_one, xhat_G hr0.ne']
    positivity
  have hAA : 0 < AA w₀ 0 := by rw [AA_zero]; exact aa_pos (rho_pos h0.ne' 0)
  have hb : xhat (R.runT (Shat w₀) (VtR (R.r ^ n₁)) R.tstar) < 0 := by
    apply xhat_neg_of
    rw [runT_Shat_eq R h0 h1 _ R.tstar_mem, reg_Ts R h0 hc]
    show -AA w₀ 0 < 0
    linarith
  exact door_zero hT.le P.smooth_T.continuous.continuousOn (fun t _ => P.surface.avoids _ _) ha hb

include h0 h1 hc in
/-- **静的な面の上のアキレスには、t∗ の前に対称面を横切る時刻がある**。 -/
theorem static_door_zero_A :
    ∃ t ∈ Ioo 0 R.tstar,
      xhat (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) t) = 0 ∧
      (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) t).1 = 0 ∧
      ∀ w v : ℝ, G w v ≠ R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) t := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have P := klein_passage R h0 h1 n₁ hc
  have hpow : R.r ^ n₁ ≤ 1 := pow_le_one₀ hr0.le hr1.le
  have hg0 : R.g 0 = 1 := by rw [R.g_eq]; simp
  have h0mem : (0 : ℝ) ∈ Icc 0 (2 * R.tstar) := ⟨le_rfl, by linarith⟩
  have ha : 0 < xhat (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) 0) := by
    rw [P.agree_A 0 h0mem (by rw [hg0, abs_one]; exact hpow), Race.idealA, hg0,
      xhat_G one_ne_zero]
    norm_num
  have hAA : 0 < AA w₀ 0 := by rw [AA_zero]; exact aa_pos (rho_pos h0.ne' 0)
  have hb : xhat (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) R.tstar) < 0 := by
    apply xhat_neg_of
    rw [runA_Shat_eq R h0 h1 _ R.tstar_mem, reg_As R h0 hc n₁]
    show -AA w₀ 0 < 0
    linarith
  exact door_zero hT.le P.smooth_A.continuous.continuousOn (fun t _ => P.surface.avoids _ _) ha hb

end StaticDoors

/-! ### 自由度：中央の角度の選び方と実数解 -/

/-- **自由度と実数解（動く面）**：中央での二人の角度が 2π の整数倍だけ違えば、二人は t∗ に同じ点にいる。 -/
theorem dyn_collision_of_centre_angle (R : Race) (w₀ : ℝ) {F : ℝ → ℝ → ℝ → V3}
    (hper : ∀ s w v : ℝ, F s w (v + 2 * π) = F s w v) {Vt Va : ℝ → ℝ} {m : ℤ}
    (h : Va 0 = Vt 0 + m * (2 * π)) :
    dynT R w₀ F Vt R.tstar = dynA R w₀ F Va R.tstar := by
  have hp : Function.Periodic (fun v => F (sched R w₀ R.tstar) 0 v) (2 * π) :=
    fun v => hper _ _ v
  simp only [dynT, dynA, R.g_tstar, mul_zero, h]
  exact ((hp.int_mul m) (Vt 0)).symm

/-- **自由度と実数解（静的な面）**：中央での二人の角度が 2π の整数倍だけ違えば、二人は t∗ に同じ点にいる。 -/
theorem run_collision_of_centre_angle (R : Race) {S : ℝ → ℝ → V3}
    (hper : ∀ w v : ℝ, S w (v + 2 * π) = S w v) {Vt Va : ℝ → ℝ} {m : ℤ}
    (h : Va 0 = Vt 0 + m * (2 * π)) :
    R.runT S Vt R.tstar = R.runA S Va R.tstar := by
  have hp : Function.Periodic (fun v => S 0 v) (2 * π) := fun v => hper _ v
  simp only [Race.runT, Race.runA, R.g_tstar, mul_zero, h]
  exact ((hp.int_mul m) (Vt 0)).symm

/-- `DynamicPassage` の非衝突は、中央での二人の角度が 2π を法として異なることを含む。 -/
theorem DynamicPassage.centre_angle_ne {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3}
    {F : ℝ → ℝ → ℝ → V3} {Vt Va : ℝ → ℝ} (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va) (m : ℤ) :
    Va 0 ≠ Vt 0 + m * (2 * π) := fun h =>
  P.no_collision R.tstar R.tstar_mem (dyn_collision_of_centre_angle R w₀ P.eversion.periodic h)

/-- 主定理の導線では、中央での二人の角度の差は π + 2πn₁ である（中央円の対蹠点）。 -/
theorem centre_angle_diff (R : Race) (w₀ : ℝ) (n₁ : ℕ) :
    VaR R.r w₀ (R.r ^ n₁) n₁ 0 - VtR (R.r ^ n₁) 0 = π + n₁ * (2 * π) := by
  rw [VaR_zero (pow_pos R.r_pos n₁) n₁, VtR_zero (pow_pos R.r_pos n₁)]
  ring

/-! ### 複素表示 𝔾 との関係：対称面の点は純虚数の助変数をもつ -/

/-- 𝔾 の純虚数の助変数 z = iy の点は、対称面 q₁ = 0 の上にある。 -/
theorem GG_imaginary_fst (y v : ℝ) : (GG ⟨0, y⟩ v).1 = 0 := by
  simp [GG]

/-- 𝔾(iy, v) の成分。 -/
theorem GG_imaginary (y v : ℝ) :
    GG ⟨0, y⟩ v = (0, -(y ^ 3 / (1 + y ^ 4)) * sin v, y ^ 3 / (1 + y ^ 4) * cos v) := by
  have hpos : (0 : ℝ) < 1 + y ^ 4 := by positivity
  have e : Complex.normSq ⟨0, y⟩ = y * y := by simp [Complex.normSq_mk]
  simp only [GG, e]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp
  · show y * y * (0 * cos v - y * sin v) / (1 + (y * y) ^ 2) = -(y ^ 3 / (1 + y ^ 4)) * sin v
    have h2 : (1 : ℝ) + (y * y) ^ 2 = 1 + y ^ 4 := by ring
    rw [h2]
    field_simp
    ring
  · show y * y * (0 * sin v + y * cos v) / (1 + (y * y) ^ 2) = y ^ 3 / (1 + y ^ 4) * cos v
    have h2 : (1 : ℝ) + (y * y) ^ 2 = 1 + y ^ 4 := by ring
    rw [h2]
    field_simp
    ring

/-- **対称面の点は純虚数の助変数をもつ**：対称面 q₁ = 0 の上の ℘ でない点で、℘ からの距離が 1/2 以下の
ものは、ある y ∈ (0, 1] と v について 𝔾(iy, v) に等しい。 -/
theorem mirror_point_imaginary {q : V3} (h1 : q.1 = 0) (hne : q ≠ wp) (hsmall : nsq q ≤ 1 / 4) :
    ∃ y v : ℝ, 0 < y ∧ y ≤ 1 ∧ q = GG ⟨0, y⟩ v := by
  obtain ⟨q1, q2, q3⟩ := q
  have h1' : q1 = 0 := h1
  subst h1'
  have hsq : nsq ((0 : ℝ), q2, q3) = q2 ^ 2 + q3 ^ 2 := by
    simp only [nsq, dot]
    ring
  have hpos : 0 < q2 ^ 2 + q3 ^ 2 := by rw [← hsq]; exact nsq_pos_of_ne hne
  have hρpos : 0 < √(q2 ^ 2 + q3 ^ 2) := Real.sqrt_pos.mpr hpos
  have hρle : √(q2 ^ 2 + q3 ^ 2) ≤ 1 / 2 := by
    have h4 : q2 ^ 2 + q3 ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by rw [← hsq]; linarith
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, h4⟩
  have hcont : ContinuousOn (fun y : ℝ => y ^ 3 / (1 + y ^ 4)) (Icc 0 1) := by
    apply Continuous.continuousOn
    exact (continuous_pow 3).div (continuous_const.add (continuous_pow 4))
      (fun y => by positivity)
  have hmem : √(q2 ^ 2 + q3 ^ 2) ∈ Ioc ((0 : ℝ) ^ 3 / (1 + (0 : ℝ) ^ 4))
      ((1 : ℝ) ^ 3 / (1 + (1 : ℝ) ^ 4)) := by
    constructor
    · simpa using hρpos
    · norm_num
      linarith
  obtain ⟨y, hy, hval⟩ := intermediate_value_Ioc (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
  have hval' : y ^ 3 / (1 + y ^ 4) = √(q2 ^ 2 + q3 ^ 2) := hval
  -- 角度：(q3, −q2) = ρ (cos v, sin v)
  let z : ℂ := ⟨q3, -q2⟩
  have hz : ‖z‖ = √(q2 ^ 2 + q3 ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    congr 1
    show q3 ^ 2 + (-q2) ^ 2 = q2 ^ 2 + q3 ^ 2
    ring
  have hc : ‖z‖ * cos (Complex.arg z) = q3 := Complex.norm_mul_cos_arg z
  have hs : ‖z‖ * sin (Complex.arg z) = -q2 := Complex.norm_mul_sin_arg z
  refine ⟨y, Complex.arg z, hy.1, hy.2, ?_⟩
  rw [GG_imaginary, hval', ← hz]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · show q2 = -‖z‖ * sin (Complex.arg z)
    linarith
  · show q3 = ‖z‖ * cos (Complex.arg z)
    linarith

section DynImaginary

variable {R : Race} {w₀ ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3} {F : ℝ → ℝ → ℝ → V3}

/-- **亀が対称面を横切る点は、𝔾 の純虚数の助変数の点である**（首が ℘ の半径 1/2 の球に入るとき）。 -/
theorem door_zero_T_imaginary
    (P : DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ S X F (VtR (R.r ^ n₁))
      (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁))
    (E : DynamicEffects R (R.r ^ n₁) n₁ F) (hn : 1 ≤ n₁) (hε : 0 ≤ ε)
    (hball : R.r ^ n₁ + ε ≤ 1 / 2) :
    ∃ t ∈ Ioo R.tstar (2 * R.tstar), ∃ y v : ℝ, 0 < y ∧ y ≤ 1 ∧
      dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t = GG ⟨0, y⟩ v := by
  obtain ⟨t, ht, -, h1, -, hneck⟩ := door_zero_T P E hn
  have htI : t ∈ Icc 0 (2 * R.tstar) := ⟨by linarith [ht.1, R.tstar_pos], ht.2.le⟩
  have hb : nsq (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t) < (R.r ^ n₁ + ε) ^ 2 :=
    P.eversion.ball _ _ _ hneck.le
  have hpos : 0 ≤ R.r ^ n₁ + ε := by have := pow_pos R.r_pos n₁; linarith
  have hsmall : nsq (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t) ≤ 1 / 4 := by
    have : (R.r ^ n₁ + ε) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hpos hball 2
    linarith
  obtain ⟨y, v, hy0, hy1, he⟩ := mirror_point_imaginary h1 (E.avoids_T t htI) hsmall
  exact ⟨t, ht, y, v, hy0, hy1, he⟩

/-- **アキレスが対称面を横切る点は、𝔾 の純虚数の助変数の点である**（首が ℘ の半径 1/2 の球に入るとき）。 -/
theorem door_zero_A_imaginary
    (P : DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ S X F (VtR (R.r ^ n₁))
      (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁))
    (E : DynamicEffects R (R.r ^ n₁) n₁ F) (hε : 0 ≤ ε) (hball : R.r ^ n₁ + ε ≤ 1 / 2) :
    ∃ t ∈ Ioo 0 R.tstar, ∃ y v : ℝ, 0 < y ∧ y ≤ 1 ∧
      dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t = GG ⟨0, y⟩ v := by
  obtain ⟨t, ht, -, h1, -, hneck⟩ := door_zero_A P E
  have htI : t ∈ Icc 0 (2 * R.tstar) := ⟨ht.1.le, by linarith [ht.2, R.tstar_pos]⟩
  have hb : nsq (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) <
      (R.r ^ n₁ + ε) ^ 2 := P.eversion.ball _ _ _ hneck.le
  have hpos : 0 ≤ R.r ^ n₁ + ε := by have := pow_pos R.r_pos n₁; linarith
  have hsmall : nsq (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) ≤ 1 / 4 := by
    have : (R.r ^ n₁ + ε) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hpos hball 2
    linarith
  obtain ⟨y, v, hy0, hy1, he⟩ := mirror_point_imaginary h1 (E.avoids_A t htI) hsmall
  exact ⟨t, ht, y, v, hy0, hy1, he⟩

end DynImaginary

/-! ### 複素迂回の形との非両立：t∗ の二人の位置は、共通の複素助変数では書けない -/

/-- x̂ > 0 なら第 1 成分は正である。 -/
theorem fst_pos_of_xhat_pos {q : V3} (h : 0 < xhat q) : 0 < q.1 := by
  unfold xhat at h
  have hn : 0 ≤ nsq q := by
    simp only [nsq, dot]
    nlinarith [mul_self_nonneg q.1, mul_self_nonneg q.2.1, mul_self_nonneg q.2.2]
  rcases div_pos_iff.mp h with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h1
  · linarith

/-- 正の倍 κ·𝔾(z, v) の第 1 成分の符号は Re z の符号である。 -/
theorem smul_GG_fst (κ : ℝ) (z : ℂ) (v : ℝ) :
    (κ • GG z v).1 = κ * (z.re / (1 + Complex.normSq z ^ 2)) := rfl

section NoCommon

variable {R : Race} {w₀ : ℝ} {n₁ : ℕ} {F : ℝ → ℝ → ℝ → V3}

/-- **複素迂回の形との非両立**。第 3.1 版 定理 8.9 の (i) では、同じ時刻の二人の位置は、共通の複素助変数 z に
ついて A = κ𝔾(z, ·)、T = κ𝔾(rz, ·) の形であり、x̂(T) と x̂(A) は同じ符号（Re z の符号）をもつ。動く
クライン型の面の上では、t∗ に x̂(T) > 0 > x̂(A) なので、t∗ の二人の位置をこの形に書く z、正の倍率、角度は
存在しない。 -/
theorem no_common_complex_parameter (E : DynamicEffects R w₀ n₁ F) :
    ¬ ∃ (z : ℂ) (κ κ' v v' : ℝ), 0 < κ ∧ 0 < κ' ∧
      dynT R w₀ F (VtR (R.r ^ n₁)) R.tstar = κ • GG ((R.r : ℂ) * z) v ∧
      dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) R.tstar = κ' • GG z v' := by
  rintro ⟨z, κ, κ', v, v', hκ, hκ', hT, hA⟩
  have hr0 := R.r_pos
  have h1 := fst_pos_of_xhat_pos E.xhat_sign.1
  rw [hT, smul_GG_fst] at h1
  have hre1 : ((R.r : ℂ) * z).re = R.r * z.re := by simp
  rw [hre1] at h1
  have hden : 0 < 1 + Complex.normSq ((R.r : ℂ) * z) ^ 2 := by positivity
  have h2 : 0 < R.r * z.re / (1 + Complex.normSq ((R.r : ℂ) * z) ^ 2) :=
    (mul_pos_iff_of_pos_left hκ).mp h1
  have h3 : 0 < R.r * z.re := by
    rcases div_pos_iff.mp h2 with ⟨h4, _⟩ | ⟨_, h5⟩
    · exact h4
    · linarith
  have hre : 0 < z.re := (mul_pos_iff_of_pos_left hr0).mp h3
  have hA1 : 0 < (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) R.tstar).1 := by
    rw [hA, smul_GG_fst]
    have hden' : 0 < 1 + Complex.normSq z ^ 2 := by positivity
    exact mul_pos hκ' (div_pos hre hden')
  have := xhat_pos_of hA1
  linarith [E.xhat_sign.2]

end NoCommon

end Zeno.Smale
