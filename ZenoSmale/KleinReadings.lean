/-
# ZenoSmale.KleinReadings : D7 — 「解」の変数と値の範囲を区別した命題

構想の記録の「実数解を持たない」「非実数解で交叉」（第 3.1 版 付録 C.3、C.4）の読みを判定するために、
`KleinDoors` の定理に、変数（時刻、値、助変数）と値の範囲（ℝ、ℝ ∪ {∞}、ℂ、ℝ³）を区別した命題を加える。
`KleinDoors` と `KleinClosure` の定理の文と証明は変えない。新しい模型は作らない。

1. **形成後の方程式の時刻の解と値**。X_A(t) = X_T(t)（ℝ ∪ {∞} の中の等式）を満たす実数の時刻は t∗
   ただ一つである（`formed_time_solution_unique`、`formed_solution_set`）。そこでの共通の値は ∞ であり、
   二人の X が同じ有限の実数になる時刻はない（`formed_no_common_finite_value`。これは
   `formed_no_real_solution` と同じ文であり、名前を内容に合わせたものである）。t ≠ t∗ では二人の X は
   有限で、互いに異なる（`formed_finite_ne`）。
2. **複素数の上の解**。位置の一次方程式 d₀ + vₜτ = vₐτ の複素数の解は τ = t∗ だけである
   （`catchup_complex_iff`、`catchup_complex_root_real`）。形成後の方程式は、時刻を複素数に延長しても、
   τ ≠ t∗ では両辺が有限で互いに異なる（`formed_complex_ne`）。複素助変数の方程式 z = r z の解は z = 0
   だけである（`complex_parameter_eq_iff`）。したがって、これらの方程式は非実数の根をもたない。
3. **扉 0 の方程式の、複素表示での解**。κ ≠ 0 のとき x̂(κ𝔾(z, v)) = 0 ⟺ Re z = 0 である
   （`xhat_smul_GG_eq_zero_iff`）。実の助変数 w ≠ 0 は解にならず（`door_zero_no_real_parameter`、
   `xhat_G_ne_zero`）、z ≠ 0 の解は純虚数で 0 でない（`door_zero_solution_nonreal`）。純虚数の助変数は
   解である（`door_zero_imaginary_solution`）。z ≠ 0 なら 𝔾(z, v) ≠ ℘ である（`GG_ne_wp`）。
4. **共通の複素助変数の形（第 3.1 版 定理 8.9 の (i)）の判定条件**。T = κ𝔾(r z, v)、A = κ′𝔾(z, v′)
   ならば A₁²·|ζ(T)|² = r⁴·T₁²·|ζ(A)|² であり（`common_parameter_necessary`）、κ、κ′、r > 0 なら T₁ と A₁
   は同じ符号をもつ（`common_parameter_sign`）。したがって、第 1 成分の符号が異なる二点はこの形に書けず
   （`no_common_parameter_of_sign`）、静的な面の上の t∗ の二人の位置 (−aa₀, 0, ±bb₀) も、この形に
   書けない（`no_common_complex_parameter_static`）。逆に、ζ 成分が 0 でない二点について、この形に書ける
   ことは A₁·|ζ(T)| = r²·T₁·|ζ(A)| と同値である（`common_parameter_sufficient`、
   `common_parameter_iff`）。特に、対称面の上の二点はこの形に書ける（`common_parameter_of_mirror`）。動く
   面の上の二人は、岸にいる時刻には、実の助変数 z = g(t) でこの形をもつ（`shore_common_parameter`）。
5. **有限な領域と理想点**。℘ を通らない連続な道は ℘ から正の距離を保ち、x̂ は有界である
   （`path_away_from_wp`、`path_xhat_bounded`）。動く面の上の走者については `dyn_away_from_wp`、
   `dyn_xhat_bounded`、`dyn_xhat_bounded_of_effects` である。理想形では x̂ は有界でない
   （`ideal_xhat_unbounded`）。理想形の走者は扉 0 を通らない（`ideal_no_door_zero`）。形成後の
   方程式の解 t∗ に、理想形では二人は同じ点 ℘ にいて、動く面の上では二人は異なる点にいる
   （`formed_solution_positions`）。対称面の ℘ でない点は 𝔾(i, v) の正の倍であり（`mirror_point_scaled`）、
   動く面の上の二人が対称面を横切る点は、球の条件なしに、純虚数の助変数の点の正の倍である
   （`door_zero_T_scaled`、`door_zero_A_scaled`）。
6. **自由**。静的な面の上では、どの導線についても、二人は t ≠ t∗ には衝突せず、t∗ に衝突するのは
   中央の角度が 2π を法として等しいとき、そのときに限る（`static_collision_iff`）。中央の角度が 2π を
   法として等しい導線は `DynamicPassage` を満たさない（`not_dynamicPassage_of_centre_angle`）。
7. **岸の上の導線：角度と位置の区別**。右岸では導線の角度の差は θ(w) であり（`twist_diff_right`）、
   左岸では 2π + 4πn₁ − θ(w) である（`twist_diff_left`）。面に写した位置は、どちらの岸でも理想形の点
   G(w, 0)、G(w, θ(w)) である（`guide_position_shore`）。
-/
import ZenoSmale.KleinClosure

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open Zeno.Model

/-! ### 形成後の方程式：時刻の解と、解での値 -/

/-- **形成後の方程式の実数の時刻の解はただ一つである**：X_A(t) = X_T(t)（ℝ ∪ {∞} の中の等式）を満たす
実数 t は t∗ ただ一つである。 -/
theorem formed_time_solution_unique (R : Race) :
    ∃! t : ℝ, invOP (R.g t) = invOP (R.r * R.g t) :=
  ⟨R.tstar, (formed_meeting_iff R R.tstar).mpr rfl, fun t ht => (formed_meeting_iff R t).mp ht⟩

/-- 形成後の方程式の解の集合は {t∗} である。 -/
theorem formed_solution_set (R : Race) :
    {t : ℝ | invOP (R.g t) = invOP (R.r * R.g t)} = {R.tstar} := by
  ext t
  exact formed_meeting_iff R t

/-- **共通の有限の実数値はない**：二人の射影座標 X が同じ実数 x になる時刻 t はない。時刻の解 t∗ は
実数であり（`formed_time_solution_unique`）、そこでの共通の値が ∞ である（`formed_meeting_value`）。
`formed_no_real_solution` と同じ文であり、名前を内容に合わせたものである。 -/
theorem formed_no_common_finite_value (R : Race) :
    ¬ ∃ t x : ℝ, invOP (R.g t) = (x : OnePoint ℝ) ∧ invOP (R.r * R.g t) = (x : OnePoint ℝ) :=
  formed_no_real_solution R

/-- t ≠ t∗ では、二人の X はどちらも有限の実数であり、互いに異なる。 -/
theorem formed_finite_ne (R : Race) {t : ℝ} (ht : t ≠ R.tstar) :
    invOP (R.g t) = (((R.g t)⁻¹ : ℝ) : OnePoint ℝ) ∧
      invOP (R.r * R.g t) = (((R.r * R.g t)⁻¹ : ℝ) : OnePoint ℝ) ∧
      (R.g t)⁻¹ ≠ (R.r * R.g t)⁻¹ := by
  have hg : R.g t ≠ 0 := fun h0 => ht ((R.g_eq_zero_iff t).mp h0)
  have hrg : R.r * R.g t ≠ 0 := mul_ne_zero R.r_pos.ne' hg
  refine ⟨invOP_of_ne hg, invOP_of_ne hrg, ?_⟩
  intro h
  have h3 : R.g t = R.r * R.g t := inv_injective h
  have h4 : (1 - R.r) * R.g t = 0 := by linarith
  rcases mul_eq_zero.mp h4 with h5 | h5
  · linarith [R.r_lt_one]
  · exact hg h5

/-! ### 複素数の上の解：位置の方程式、形成後の方程式、複素助変数の方程式 -/

/-- 位置の方程式の実数解：xₜ(t) = xₐ(t) ⟺ t = t∗。 -/
theorem catchup_real_iff (R : Race) (t : ℝ) : R.T t = R.A t ↔ t = R.tstar := by
  rw [← R.g_eq_zero_iff t]
  unfold Race.g
  constructor
  · intro h
    rw [h, sub_self, zero_div]
  · intro h
    rcases div_eq_zero_iff.mp h with h1 | h1
    · linarith
    · exact absurd h1 R.hd.ne'

/-- **位置の方程式は、複素数の上でも t∗ だけを解にもつ**：一次方程式 d₀ + vₜτ = vₐτ の複素数の解は
τ = t∗ だけである。 -/
theorem catchup_complex_iff (R : Race) (τ : ℂ) :
    (R.d0 : ℂ) + (R.vt : ℂ) * τ = (R.va : ℂ) * τ ↔ τ = (R.tstar : ℂ) := by
  have hgapR : R.va - R.vt ≠ 0 := R.gap_pos.ne'
  have hgap : (R.va : ℂ) - (R.vt : ℂ) ≠ 0 := by
    have h : ((R.va - R.vt : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hgapR
    simpa using h
  have ht : (R.tstar : ℂ) = (R.d0 : ℂ) / ((R.va : ℂ) - (R.vt : ℂ)) := by
    simp [Race.tstar]
  constructor
  · intro h
    rw [ht, eq_div_iff hgap]
    linear_combination -h
  · intro h
    rw [h, ht]
    field_simp
    ring

/-- 位置の方程式の複素数の解は実数である（非実数の根はない）。 -/
theorem catchup_complex_root_real (R : Race) {τ : ℂ}
    (h : (R.d0 : ℂ) + (R.vt : ℂ) * τ = (R.va : ℂ) * τ) : τ.im = 0 := by
  rw [(catchup_complex_iff R τ).mp h]
  exact Complex.ofReal_im _

/-- g の複素数への延長 τ ↦ 1 − τ/t∗ は、実数の上で g に一致する。 -/
theorem g_complex_ofReal (R : Race) (t : ℝ) :
    (1 : ℂ) - (t : ℂ) / (R.tstar : ℂ) = ((R.g t : ℝ) : ℂ) := by
  rw [R.g_eq]
  push_cast
  ring

/-- 1 − τ/t∗ = 0 ⟺ τ = t∗。 -/
theorem g_complex_eq_zero_iff (R : Race) (τ : ℂ) :
    (1 : ℂ) - τ / (R.tstar : ℂ) = 0 ↔ τ = (R.tstar : ℂ) := by
  have hT : (R.tstar : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr R.tstar_pos.ne'
  constructor
  · intro h
    have h2 : τ / (R.tstar : ℂ) = 1 := by linear_combination -h
    exact (div_eq_one_iff_eq hT).mp h2
  · intro h
    rw [h, div_self hT, sub_self]

/-- **形成後の方程式は、時刻を複素数に延長しても、t∗ 以外に解をもたない**：τ ≠ t∗ の複素数 τ について、
g(τ) = 1 − τ/t∗ は 0 でなく、1/g(τ) と 1/(r g(τ)) は有限の複素数で、互いに異なる。したがって、形成後の
方程式は非実数の根をもたない。t∗ での値 ∞ は、ℝ ∪ {∞} に加えた一点であり、複素数ではない。 -/
theorem formed_complex_ne (R : Race) {τ : ℂ} (h : τ ≠ (R.tstar : ℂ)) :
    (1 : ℂ) - τ / (R.tstar : ℂ) ≠ 0 ∧
      ((1 : ℂ) - τ / (R.tstar : ℂ))⁻¹ ≠ ((R.r : ℂ) * ((1 : ℂ) - τ / (R.tstar : ℂ)))⁻¹ := by
  have hg : (1 : ℂ) - τ / (R.tstar : ℂ) ≠ 0 := fun h0 => h ((g_complex_eq_zero_iff R τ).mp h0)
  refine ⟨hg, ?_⟩
  intro h2
  have h3 : (1 : ℂ) - τ / (R.tstar : ℂ) = (R.r : ℂ) * ((1 : ℂ) - τ / (R.tstar : ℂ)) :=
    inv_injective h2
  have h4 : ((1 : ℂ) - (R.r : ℂ)) * ((1 : ℂ) - τ / (R.tstar : ℂ)) = 0 := by
    linear_combination h3
  rcases mul_eq_zero.mp h4 with h5 | h5
  · have h6 : ((1 - R.r : ℝ) : ℂ) = 0 := by
      push_cast
      exact h5
    have h7 : (1 - R.r : ℝ) = 0 := Complex.ofReal_eq_zero.mp h6
    linarith [R.r_lt_one]
  · exact hg h5

/-- **複素助変数の方程式の解は z = 0 だけである**：zₐ = zₜ（zₜ = r zₐ）の複素数の解は z = 0（実数）
だけであり、非実数の根はない。 -/
theorem complex_parameter_eq_iff (R : Race) (z : ℂ) : z = (R.r : ℂ) * z ↔ z = 0 := by
  constructor
  · intro h
    have h4 : ((1 : ℂ) - (R.r : ℂ)) * z = 0 := by linear_combination h
    rcases mul_eq_zero.mp h4 with h5 | h5
    · have h6 : ((1 - R.r : ℝ) : ℂ) = 0 := by
        push_cast
        exact h5
      have h7 : (1 - R.r : ℝ) = 0 := Complex.ofReal_eq_zero.mp h6
      linarith [R.r_lt_one]
    · exact h5
  · intro h
    rw [h, mul_zero]

/-! ### 扉 0 の方程式 x̂ = 0 の、複素表示 𝔾 での解 -/

/-- x̂(q) = 0 ⟺ q₁ = 0（℘ では、Lean の除算の規約により x̂ = 0 である）。 -/
theorem xhat_eq_zero_iff (q : V3) : xhat q = 0 ↔ q.1 = 0 := by
  unfold xhat
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with h1 | h1
    · exact h1
    · have h2 : q.1 * q.1 ≤ nsq q := by
        simp only [nsq, dot]
        nlinarith [mul_self_nonneg q.2.1, mul_self_nonneg q.2.2]
      have h3 : q.1 * q.1 ≤ 0 := by linarith
      exact mul_self_eq_zero.mp (le_antisymm h3 (mul_self_nonneg q.1))
  · intro h
    rw [h, zero_div]

/-- 𝔾 の後ろの二つの成分の恒等式：(Re z cos v − Im z sin v)² + (Re z sin v + Im z cos v)² = |z|²。 -/
theorem GG_trig (z : ℂ) (v : ℝ) :
    (z.re * cos v - z.im * sin v) ^ 2 + (z.re * sin v + z.im * cos v) ^ 2 = Complex.normSq z := by
  have hN : Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z
  have hsc := sin_sq_add_cos_sq v
  rw [hN]
  linear_combination (z.re ^ 2 + z.im ^ 2) * hsc

/-- 𝔾(z, v) の大きさの 2 乗：|𝔾(z, v)|² = ((Re z)² + |z|⁶)/(1 + |z|⁴)²。 -/
theorem nsq_GG (z : ℂ) (v : ℝ) :
    nsq (GG z v) = (z.re ^ 2 + Complex.normSq z ^ 3) / (1 + Complex.normSq z ^ 2) ^ 2 := by
  have hden : (1 : ℝ) + Complex.normSq z ^ 2 ≠ 0 := by positivity
  have e : nsq (GG z v) = (z.re ^ 2 + Complex.normSq z ^ 2 *
      ((z.re * cos v - z.im * sin v) ^ 2 + (z.re * sin v + z.im * cos v) ^ 2)) /
      (1 + Complex.normSq z ^ 2) ^ 2 := by
    simp only [nsq, dot, GG]
    field_simp
    ring
  rw [e, GG_trig]
  ring

/-- z ≠ 0 なら 𝔾(z, v) は ℘ でない。 -/
theorem GG_ne_wp {z : ℂ} (hz : z ≠ 0) (v : ℝ) : GG z v ≠ wp := by
  intro h
  have hN : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have h1 : nsq (GG z v) = 0 := by
    rw [h]
    simp [nsq, dot, wp]
  rw [nsq_GG] at h1
  have h3 : 0 < Complex.normSq z ^ 3 := pow_pos hN 3
  have hnum : 0 < z.re ^ 2 + Complex.normSq z ^ 3 := by nlinarith [sq_nonneg z.re]
  have hden : (0 : ℝ) < (1 + Complex.normSq z ^ 2) ^ 2 := by positivity
  have hpos := div_pos hnum hden
  linarith

/-- **扉 0 の方程式の、複素表示での解**：κ ≠ 0 のとき、x̂(κ𝔾(z, v)) = 0 ⟺ Re z = 0 である。 -/
theorem xhat_smul_GG_eq_zero_iff {κ : ℝ} (hκ : κ ≠ 0) (z : ℂ) (v : ℝ) :
    xhat (κ • GG z v) = 0 ↔ z.re = 0 := by
  have hden : (1 : ℝ) + Complex.normSq z ^ 2 ≠ 0 := by positivity
  rw [xhat_eq_zero_iff, smul_GG_fst]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hκ
    · rcases div_eq_zero_iff.mp h1 with h2 | h2
      · exact h2
      · exact absurd h2 hden
  · intro h
    rw [h, zero_div, mul_zero]

/-- **実の助変数は扉 0 の方程式の解にならない**：w ≠ 0 の実数 w と κ ≠ 0 について x̂(κ𝔾(w, v)) ≠ 0 で
ある。 -/
theorem door_zero_no_real_parameter {κ : ℝ} (hκ : κ ≠ 0) {w : ℝ} (hw : w ≠ 0) (v : ℝ) :
    xhat (κ • GG (w : ℂ) v) ≠ 0 := by
  intro h
  have h2 := (xhat_smul_GG_eq_zero_iff hκ (w : ℂ) v).mp h
  exact hw (by simpa using h2)

/-- ホーン対の上では x̂ は 0 にならない：w ≠ 0 なら x̂(G(w, v)) = 1/w ≠ 0。 -/
theorem xhat_G_ne_zero {w : ℝ} (hw : w ≠ 0) (v : ℝ) : xhat (G w v) ≠ 0 := by
  rw [xhat_G hw]
  exact one_div_ne_zero hw

/-- **扉 0 の方程式の解は非実数である**：z ≠ 0、κ ≠ 0 で x̂(κ𝔾(z, v)) = 0 なら、z は 0 でない純虚数で
ある（Re z = 0、Im z ≠ 0）。 -/
theorem door_zero_solution_nonreal {κ : ℝ} (hκ : κ ≠ 0) {z : ℂ} (hz : z ≠ 0) {v : ℝ}
    (h : xhat (κ • GG z v) = 0) : z.re = 0 ∧ z.im ≠ 0 := by
  have hre := (xhat_smul_GG_eq_zero_iff hκ z v).mp h
  exact ⟨hre, fun him => hz (Complex.ext hre him)⟩

/-- 純虚数の助変数は扉 0 の方程式の解である。 -/
theorem door_zero_imaginary_solution (κ y v : ℝ) : xhat (κ • GG ⟨0, y⟩ v) = 0 := by
  rw [xhat_eq_zero_iff, smul_GG_fst]
  simp

/-! ### 共通の複素助変数の形（第 3.1 版 定理 8.9 の (i)）の必要条件 -/

/-- κ𝔾(z, v) の ζ 成分の大きさの 2 乗：κ²|z|⁶/(1 + |z|⁴)²。 -/
theorem zetaSq_smul_GG (κ : ℝ) (z : ℂ) (v : ℝ) :
    zetaSq (κ • GG z v) = κ ^ 2 * Complex.normSq z ^ 3 / (1 + Complex.normSq z ^ 2) ^ 2 := by
  have hden : (1 : ℝ) + Complex.normSq z ^ 2 ≠ 0 := by positivity
  have e : zetaSq (κ • GG z v) = κ ^ 2 * Complex.normSq z ^ 2 *
      ((z.re * cos v - z.im * sin v) ^ 2 + (z.re * sin v + z.im * cos v) ^ 2) /
      (1 + Complex.normSq z ^ 2) ^ 2 := by
    simp only [zetaSq, Prod.smul_snd, Prod.smul_fst, smul_eq_mul, GG]
    field_simp
  rw [e, GG_trig]
  ring

/-- **共通の複素助変数の形の必要条件**：T = κ𝔾(r z, v)、A = κ′𝔾(z, v′) ならば、
A₁²·|ζ(T)|² = r⁴·T₁²·|ζ(A)|² である。 -/
theorem common_parameter_necessary {r κ κ' v v' : ℝ} {z : ℂ} {T A : V3}
    (hT : T = κ • GG ((r : ℂ) * z) v) (hA : A = κ' • GG z v') :
    A.1 ^ 2 * zetaSq T = r ^ 4 * T.1 ^ 2 * zetaSq A := by
  have hN : Complex.normSq ((r : ℂ) * z) = r ^ 2 * Complex.normSq z := by
    rw [Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  have hre : ((r : ℂ) * z).re = r * z.re := by simp
  have h1 : (1 : ℝ) + Complex.normSq z ^ 2 ≠ 0 := by positivity
  have h2 : (1 : ℝ) + (r ^ 2 * Complex.normSq z) ^ 2 ≠ 0 := by positivity
  rw [hT, hA, zetaSq_smul_GG, zetaSq_smul_GG, smul_GG_fst, smul_GG_fst, hN, hre]
  field_simp

/-- 正の倍率と r > 0 のもとでは、共通の複素助変数の形の二点の第 1 成分は同じ符号をもつ。 -/
theorem common_parameter_sign {r κ κ' v v' : ℝ} (hr : 0 < r) (hκ : 0 < κ) (hκ' : 0 < κ') {z : ℂ}
    {T A : V3} (hT : T = κ • GG ((r : ℂ) * z) v) (hA : A = κ' • GG z v') :
    (0 < T.1 ↔ 0 < A.1) ∧ (T.1 < 0 ↔ A.1 < 0) ∧ (T.1 = 0 ↔ A.1 = 0) := by
  have hre : ((r : ℂ) * z).re = r * z.re := by simp
  have dT : (0 : ℝ) < 1 + Complex.normSq ((r : ℂ) * z) ^ 2 := by positivity
  have dA : (0 : ℝ) < 1 + Complex.normSq z ^ 2 := by positivity
  have eT : T.1 = κ * r / (1 + Complex.normSq ((r : ℂ) * z) ^ 2) * z.re := by
    rw [hT, smul_GG_fst, hre]
    ring
  have eA : A.1 = κ' / (1 + Complex.normSq z ^ 2) * z.re := by
    rw [hA, smul_GG_fst]
    ring
  have cT : 0 < κ * r / (1 + Complex.normSq ((r : ℂ) * z) ^ 2) := div_pos (mul_pos hκ hr) dT
  have cA : 0 < κ' / (1 + Complex.normSq z ^ 2) := div_pos hκ' dA
  rw [eT, eA]
  refine ⟨?_, ?_, ?_⟩
  · rw [mul_pos_iff_of_pos_left cT, mul_pos_iff_of_pos_left cA]
  · constructor
    · intro h
      have hz : z.re < 0 := by
        by_contra hcon
        push Not at hcon
        have := mul_nonneg cT.le hcon
        linarith
      exact mul_neg_of_pos_of_neg cA hz
    · intro h
      have hz : z.re < 0 := by
        by_contra hcon
        push Not at hcon
        have := mul_nonneg cA.le hcon
        linarith
      exact mul_neg_of_pos_of_neg cT hz
  · constructor
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 cT.ne'
      · rw [h1, mul_zero]
    · intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact absurd h1 cA.ne'
      · rw [h1, mul_zero]

/-- **複素迂回の形との非両立（一般形）**：r > 0 とし、二点 T、A の第 1 成分の符号が異なる（T₁ > 0 > A₁、
または T₁ < 0 < A₁）とする。このとき、T = κ𝔾(r z, v)、A = κ′𝔾(z, v′)（κ、κ′ > 0）と書く z、κ、κ′、v、v′
は存在しない。 -/
theorem no_common_parameter_of_sign {r : ℝ} (hr : 0 < r) {T A : V3}
    (h : (0 < T.1 ∧ A.1 < 0) ∨ (T.1 < 0 ∧ 0 < A.1)) :
    ¬ ∃ (z : ℂ) (κ κ' v v' : ℝ), 0 < κ ∧ 0 < κ' ∧
      T = κ • GG ((r : ℂ) * z) v ∧ A = κ' • GG z v' := by
  rintro ⟨z, κ, κ', v, v', hκ, hκ', hT, hA⟩
  obtain ⟨h1, h2, -⟩ := common_parameter_sign hr hκ hκ' hT hA
  rcases h with ⟨a, b⟩ | ⟨a, b⟩
  · linarith [h1.mp a]
  · linarith [h2.mp a]

/-- **静的な面の上の t∗ の位置も、共通の複素助変数の形に書けない**。t∗ の二人の位置は (−aa₀, 0, ±bb₀)
であり、第 1 成分と ζ 成分の大きさが等しいので、必要条件 A₁²·|ζ(T)|² = r⁴·T₁²·|ζ(A)|² は r⁴ = 1 を
要求する。倍率の符号は仮定しない。 -/
theorem no_common_complex_parameter_static (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)
    (n₁ : ℕ) (hc : w₀ ≤ R.r ^ n₁) :
    ¬ ∃ (z : ℂ) (κ κ' v v' : ℝ),
      R.runT (Shat w₀) (VtR (R.r ^ n₁)) R.tstar = κ • GG ((R.r : ℂ) * z) v ∧
      R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) R.tstar = κ' • GG z v' := by
  rintro ⟨z, κ, κ', v, v', hT, hA⟩
  have hnec := common_parameter_necessary hT hA
  rw [runT_Shat_eq R h0 h1 _ R.tstar_mem, reg_Ts R h0 hc,
    runA_Shat_eq R h0 h1 _ R.tstar_mem, reg_As R h0 hc n₁] at hnec
  simp only [zetaSq] at hnec
  have hAA : 0 < AA w₀ 0 := by
    rw [AA_zero]
    exact aa_pos (rho_pos h0.ne' 0)
  have hBB : 0 < BB w₀ 0 := by
    rw [BB_zero]
    exact bb_pos (rho_pos h0.ne' 0)
  have hprod : 0 < AA w₀ 0 ^ 2 * BB w₀ 0 ^ 2 := by positivity
  have h4 : R.r ^ 4 < 1 := pow_lt_one₀ R.r_pos.le R.r_lt_one (by norm_num)
  have h5 : (1 - R.r ^ 4) * (AA w₀ 0 ^ 2 * BB w₀ 0 ^ 2) = 0 := by
    linear_combination hnec
  rcases mul_eq_zero.mp h5 with h6 | h6
  · linarith
  · linarith

/-! ### 共通の複素助変数の形の十分条件と、判定条件 -/

/-- (r : ℂ)·(ρ e^{iφ}) = (rρ) e^{iφ}。 -/
theorem ofReal_mul_zOf (r ρ φ : ℝ) : (r : ℂ) * zOf ρ φ = zOf (r * ρ) φ := by
  apply Complex.ext
  · simp only [zOf, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp only [zOf, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring

/-- 𝔾(ρ e^{iφ}, v) の成分：(ρ cos φ, ρ³ cos(φ + v), ρ³ sin(φ + v))/(1 + ρ⁴)。 -/
theorem GG_zOf (ρ φ v : ℝ) :
    GG (zOf ρ φ) v = (ρ * cos φ / (1 + ρ ^ 4), ρ ^ 3 * cos (φ + v) / (1 + ρ ^ 4),
      ρ ^ 3 * sin (φ + v) / (1 + ρ ^ 4)) := by
  have e : (1 : ℝ) + (ρ ^ 2) ^ 2 = 1 + ρ ^ 4 := by ring
  have hre : (zOf ρ φ).re = ρ * cos φ := rfl
  have him : (zOf ρ φ).im = ρ * sin φ := rfl
  simp only [GG, normSq_zOf, hre, him, e, cos_add, sin_add]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- ζ 成分が 0 でない点 q は、q₁ρ² = |ζ(q)| cos φ を満たす ρ > 0 と φ について、κ𝔾(ρ e^{iφ}, v)（κ > 0）と
書ける。 -/
theorem point_as_smul_GG {q : V3} (hq : zetaSq q ≠ 0) {ρ φ : ℝ} (hρ : 0 < ρ)
    (h : q.1 * ρ ^ 2 = √(zetaSq q) * cos φ) :
    ∃ κ v : ℝ, 0 < κ ∧ q = κ • GG (zOf ρ φ) v := by
  obtain ⟨q1, q2, q3⟩ := q
  have hζ : zetaSq ((q1, q2, q3) : V3) = q2 ^ 2 + q3 ^ 2 := rfl
  rw [hζ] at hq h
  have hpos : 0 < q2 ^ 2 + q3 ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm hq)
  have hs : 0 < √(q2 ^ 2 + q3 ^ 2) := Real.sqrt_pos.mpr hpos
  let ζ : ℂ := ⟨q2, q3⟩
  have hn : ‖ζ‖ = √(q2 ^ 2 + q3 ^ 2) := Complex.norm_eq_sqrt_sq_add_sq ζ
  have hc : ‖ζ‖ * cos (Complex.arg ζ) = q2 := Complex.norm_mul_cos_arg ζ
  have hsn : ‖ζ‖ * sin (Complex.arg ζ) = q3 := Complex.norm_mul_sin_arg ζ
  rw [hn] at hc hsn
  have hρ3 : 0 < ρ ^ 3 := pow_pos hρ 3
  have hd : (0 : ℝ) < 1 + ρ ^ 4 := by positivity
  refine ⟨√(q2 ^ 2 + q3 ^ 2) * (1 + ρ ^ 4) / ρ ^ 3, Complex.arg ζ - φ, by positivity, ?_⟩
  rw [GG_zOf]
  have e : φ + (Complex.arg ζ - φ) = Complex.arg ζ := by ring
  rw [e]
  have e1 : √(q2 ^ 2 + q3 ^ 2) * (1 + ρ ^ 4) / ρ ^ 3 * (ρ * cos φ / (1 + ρ ^ 4)) = q1 := by
    have h' : √(q2 ^ 2 + q3 ^ 2) * cos φ = q1 * ρ ^ 2 := h.symm
    field_simp
    linear_combination h'
  have e2 : √(q2 ^ 2 + q3 ^ 2) * (1 + ρ ^ 4) / ρ ^ 3 *
      (ρ ^ 3 * cos (Complex.arg ζ) / (1 + ρ ^ 4)) = q2 := by
    have h2 : √(q2 ^ 2 + q3 ^ 2) * (1 + ρ ^ 4) / ρ ^ 3 *
        (ρ ^ 3 * cos (Complex.arg ζ) / (1 + ρ ^ 4)) =
        √(q2 ^ 2 + q3 ^ 2) * cos (Complex.arg ζ) := by
      field_simp
    rw [h2, hc]
  have e3 : √(q2 ^ 2 + q3 ^ 2) * (1 + ρ ^ 4) / ρ ^ 3 *
      (ρ ^ 3 * sin (Complex.arg ζ) / (1 + ρ ^ 4)) = q3 := by
    have h3 : √(q2 ^ 2 + q3 ^ 2) * (1 + ρ ^ 4) / ρ ^ 3 *
        (ρ ^ 3 * sin (Complex.arg ζ) / (1 + ρ ^ 4)) =
        √(q2 ^ 2 + q3 ^ 2) * sin (Complex.arg ζ) := by
      field_simp
    rw [h3, hsn]
  exact Prod.ext e1.symm (Prod.ext e2.symm e3.symm)

/-- **共通の複素助変数の形の十分条件**：r > 0、T と A の ζ 成分が 0 でなく、
A₁·|ζ(T)| = r²·T₁·|ζ(A)| ならば、T = κ𝔾(r z, v)、A = κ′𝔾(z, v′)（z ≠ 0、κ、κ′ > 0）と書ける。 -/
theorem common_parameter_sufficient {r : ℝ} (hr : 0 < r) {T A : V3}
    (hT : zetaSq T ≠ 0) (hA : zetaSq A ≠ 0)
    (h : A.1 * √(zetaSq T) = r ^ 2 * T.1 * √(zetaSq A)) :
    ∃ (z : ℂ) (κ κ' v v' : ℝ), z ≠ 0 ∧ 0 < κ ∧ 0 < κ' ∧
      T = κ • GG ((r : ℂ) * z) v ∧ A = κ' • GG z v' := by
  have hTp : 0 < zetaSq T := lt_of_le_of_ne (by unfold zetaSq; positivity) (Ne.symm hT)
  have hAp : 0 < zetaSq A := lt_of_le_of_ne (by unfold zetaSq; positivity) (Ne.symm hA)
  have sT : 0 < √(zetaSq T) := Real.sqrt_pos.mpr hTp
  have sA : 0 < √(zetaSq A) := Real.sqrt_pos.mpr hAp
  have hden : 0 < 1 + |A.1 / √(zetaSq A)| := by positivity
  have hρ : 0 < 1 / √(1 + |A.1 / √(zetaSq A)|) := by positivity
  have hρ2 : (1 / √(1 + |A.1 / √(zetaSq A)|)) ^ 2 = 1 / (1 + |A.1 / √(zetaSq A)|) := by
    rw [div_pow, one_pow, Real.sq_sqrt hden.le]
  have hcb : |A.1 / √(zetaSq A) * (1 / √(1 + |A.1 / √(zetaSq A)|)) ^ 2| ≤ 1 := by
    rw [hρ2, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (1 + |A.1 / √(zetaSq A)|)),
      mul_one_div, div_le_one hden]
    linarith [abs_nonneg (A.1 / √(zetaSq A))]
  have hcos := Real.cos_arccos (by linarith [(abs_le.mp hcb).1]) (abs_le.mp hcb).2
  have hAeq : A.1 * (1 / √(1 + |A.1 / √(zetaSq A)|)) ^ 2 =
      √(zetaSq A) * cos (arccos (A.1 / √(zetaSq A) * (1 / √(1 + |A.1 / √(zetaSq A)|)) ^ 2)) := by
    rw [hcos]
    field_simp
  have hTeq : T.1 * (r * (1 / √(1 + |A.1 / √(zetaSq A)|))) ^ 2 =
      √(zetaSq T) * cos (arccos (A.1 / √(zetaSq A) * (1 / √(1 + |A.1 / √(zetaSq A)|)) ^ 2)) := by
    rw [hcos, mul_pow]
    have h2 : T.1 * r ^ 2 = √(zetaSq T) * (A.1 / √(zetaSq A)) := by
      field_simp
      linear_combination -h
    linear_combination (1 / √(1 + |A.1 / √(zetaSq A)|)) ^ 2 * h2
  obtain ⟨κ', v', hκ', eA⟩ := point_as_smul_GG hA hρ hAeq
  obtain ⟨κ, v, hκ, eT⟩ := point_as_smul_GG hT (mul_pos hr hρ) hTeq
  refine ⟨zOf (1 / √(1 + |A.1 / √(zetaSq A)|))
    (arccos (A.1 / √(zetaSq A) * (1 / √(1 + |A.1 / √(zetaSq A)|)) ^ 2)), κ, κ', v, v', ?_, hκ,
    hκ', ?_, eA⟩
  · intro hz
    have h0 : Complex.normSq (zOf (1 / √(1 + |A.1 / √(zetaSq A)|))
        (arccos (A.1 / √(zetaSq A) * (1 / √(1 + |A.1 / √(zetaSq A)|)) ^ 2))) = 0 := by
      rw [hz]
      simp
    rw [normSq_zOf] at h0
    exact (pow_pos hρ 2).ne' h0
  · rw [ofReal_mul_zOf]
    exact eT

/-- **共通の複素助変数の形の判定条件**：r > 0 とし、二点 T、A の ζ 成分が 0 でないとする。T = κ𝔾(r z, v)、
A = κ′𝔾(z, v′)（z ≠ 0、κ、κ′ > 0）と書けることは、A₁·|ζ(T)| = r²·T₁·|ζ(A)| と同値である。 -/
theorem common_parameter_iff {r : ℝ} (hr : 0 < r) {T A : V3} (hT : zetaSq T ≠ 0)
    (hA : zetaSq A ≠ 0) :
    (∃ (z : ℂ) (κ κ' v v' : ℝ), z ≠ 0 ∧ 0 < κ ∧ 0 < κ' ∧
        T = κ • GG ((r : ℂ) * z) v ∧ A = κ' • GG z v') ↔
      A.1 * √(zetaSq T) = r ^ 2 * T.1 * √(zetaSq A) := by
  have hTp : 0 < zetaSq T := lt_of_le_of_ne (by unfold zetaSq; positivity) (Ne.symm hT)
  have hAp : 0 < zetaSq A := lt_of_le_of_ne (by unfold zetaSq; positivity) (Ne.symm hA)
  have sT : 0 < √(zetaSq T) := Real.sqrt_pos.mpr hTp
  have sA : 0 < √(zetaSq A) := Real.sqrt_pos.mpr hAp
  constructor
  · rintro ⟨z, κ, κ', v, v', -, hκ, hκ', eT, eA⟩
    have hnec := common_parameter_necessary eT eA
    obtain ⟨hpos, hneg, hzero⟩ := common_parameter_sign hr hκ hκ' eT eA
    have hsq : (A.1 * √(zetaSq T)) ^ 2 = (r ^ 2 * T.1 * √(zetaSq A)) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hTp.le, Real.sq_sqrt hAp.le]
      linear_combination hnec
    have hr2 : 0 < r ^ 2 := pow_pos hr 2
    rcases lt_trichotomy T.1 0 with h | h | h
    · have hA1 : A.1 < 0 := hneg.mp h
      have h1 : 0 ≤ -(A.1 * √(zetaSq T)) := by
        have := mul_neg_of_neg_of_pos hA1 sT
        linarith
      have h2 : 0 ≤ -(r ^ 2 * T.1 * √(zetaSq A)) := by
        have := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hr2 h) sA
        linarith
      have h3 : (-(A.1 * √(zetaSq T))) ^ 2 = (-(r ^ 2 * T.1 * √(zetaSq A))) ^ 2 := by
        rw [neg_sq, neg_sq]
        exact hsq
      have h4 := (sq_eq_sq₀ h1 h2).mp h3
      linarith
    · have hA1 : A.1 = 0 := hzero.mp h
      rw [h, hA1]
      ring
    · have hA1 : 0 < A.1 := hpos.mp h
      have h1 : 0 ≤ A.1 * √(zetaSq T) := (mul_pos hA1 sT).le
      have h2 : 0 ≤ r ^ 2 * T.1 * √(zetaSq A) := (mul_pos (mul_pos hr2 h) sA).le
      exact (sq_eq_sq₀ h1 h2).mp hsq
  · exact common_parameter_sufficient hr hT hA

/-- 対称面の上にあって ζ 成分が 0 でない二点（T₁ = A₁ = 0）は、共通の複素助変数の形に書ける。 -/
theorem common_parameter_of_mirror {r : ℝ} (hr : 0 < r) {T A : V3} (hT1 : T.1 = 0) (hA1 : A.1 = 0)
    (hT : zetaSq T ≠ 0) (hA : zetaSq A ≠ 0) :
    ∃ (z : ℂ) (κ κ' v v' : ℝ), z ≠ 0 ∧ 0 < κ ∧ 0 < κ' ∧
      T = κ • GG ((r : ℂ) * z) v ∧ A = κ' • GG z v' :=
  common_parameter_sufficient hr hT hA (by rw [hT1, hA1]; ring)

/-- **岸では、二人の位置は共通の複素助変数の形をもつ**：亀が岸にいる時刻（そのときアキレスも岸にいる）
には、T_F(t) = 𝔾(r g(t), 0)、A_F(t) = 𝔾(g(t), θ(g(t))) であり、共通の助変数は実数 z = g(t)、倍率は 1 で
ある。 -/
theorem shore_common_parameter {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3}
    {F : ℝ → ℝ → ℝ → V3} {Vt Va : ℝ → ℝ} (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar)) (hT : c ≤ |R.r * R.g t|) :
    dynT R w₀ F Vt t = (1 : ℝ) • GG ((R.r : ℂ) * (R.g t : ℂ)) 0 ∧
      dynA R w₀ F Va t = (1 : ℝ) • GG (R.g t : ℂ) (theta R.r (R.g t)) := by
  have hA : c ≤ |R.g t| := hT.trans (R.abs_r_g_le t)
  have e : (R.r : ℂ) * (R.g t : ℂ) = ((R.r * R.g t : ℝ) : ℂ) := by push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [P.agree_T t ht hT, e, GG_real, one_smul, Race.idealT]
  · rw [P.agree_A t ht hA, GG_real, one_smul, Race.idealA]

/-! ### 有限な領域と理想点 -/

/-- **℘ を通らない連続な道は、℘ から正の距離を保つ**：閉区間の上で連続で ℘ を通らない道について、℘ から
の距離の 2 乗は、ある正の数 δ 以上である。反転 ι で見ると、道は半径 1/√δ の球の中にとどまる。 -/
theorem path_away_from_wp {f : ℝ → V3} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hne : ∀ t ∈ Icc a b, f t ≠ wp) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc a b, δ ≤ nsq (f t) := by
  have hcont : ContinuousOn (fun t => nsq (f t)) (Icc a b) := continuous_nsq.comp_continuousOn hf
  obtain ⟨m, hm, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab) hcont
  exact ⟨nsq (f m), nsq_pos_of_ne (hne m hm), fun t ht => isMinOn_iff.mp hmin t ht⟩

/-- **℘ を通らない連続な道の x̂ は有界である**。 -/
theorem path_xhat_bounded {f : ℝ → V3} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hne : ∀ t ∈ Icc a b, f t ≠ wp) : ∃ B : ℝ, ∀ t ∈ Icc a b, |xhat (f t)| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_xhat hf hne)
  exact ⟨B, fun t ht => by simpa using hB t ht⟩

section Bounded

variable {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3} {F : ℝ → ℝ → ℝ → V3}
  {Vt Va : ℝ → ℝ}

/-- **走者は ℘ から正の距離を保つ**：動く面の上の二人が競走の時間に ℘ を通らないなら、℘ からの距離の
2 乗は、ある正の数 δ 以上である。 -/
theorem dyn_away_from_wp (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va)
    (hT : ∀ t ∈ Icc 0 (2 * R.tstar), dynT R w₀ F Vt t ≠ wp)
    (hA : ∀ t ∈ Icc 0 (2 * R.tstar), dynA R w₀ F Va t ≠ wp) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc 0 (2 * R.tstar),
      δ ≤ nsq (dynT R w₀ F Vt t) ∧ δ ≤ nsq (dynA R w₀ F Va t) := by
  have hab : (0 : ℝ) ≤ 2 * R.tstar := by linarith [R.tstar_pos]
  obtain ⟨δ1, h1, hδ1⟩ := path_away_from_wp hab P.smooth_T.continuous.continuousOn hT
  obtain ⟨δ2, h2, hδ2⟩ := path_away_from_wp hab P.smooth_A.continuous.continuousOn hA
  exact ⟨min δ1 δ2, lt_min h1 h2, fun t ht =>
    ⟨(min_le_left _ _).trans (hδ1 t ht), (min_le_right _ _).trans (hδ2 t ht)⟩⟩

/-- **有限な領域**：動く面の上の二人が ℘ を通らないなら、射影座標 x̂ は競走の時間の上で有界である。 -/
theorem dyn_xhat_bounded (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va)
    (hT : ∀ t ∈ Icc 0 (2 * R.tstar), dynT R w₀ F Vt t ≠ wp)
    (hA : ∀ t ∈ Icc 0 (2 * R.tstar), dynA R w₀ F Va t ≠ wp) :
    ∃ B : ℝ, ∀ t ∈ Icc 0 (2 * R.tstar),
      |xhat (dynT R w₀ F Vt t)| ≤ B ∧ |xhat (dynA R w₀ F Va t)| ≤ B := by
  obtain ⟨B1, hB1⟩ := path_xhat_bounded P.smooth_T.continuous.continuousOn hT
  obtain ⟨B2, hB2⟩ := path_xhat_bounded P.smooth_A.continuous.continuousOn hA
  exact ⟨max B1 B2, fun t ht =>
    ⟨(hB1 t ht).trans (le_max_left _ _), (hB2 t ht).trans (le_max_right _ _)⟩⟩

/-- 形成後の方程式の解 t∗ での位置：理想形では二人は同じ点 ℘ にいる。動く面の上では二人は異なる点に
いる。形成後の方程式そのもの（`formed_meeting_iff`）は、どちらの模型でも同じ文であり、この区別を
表さない。 -/
theorem formed_solution_positions (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va) :
    (R.idealT R.tstar = wp ∧ R.idealA R.tstar = wp) ∧
      dynT R w₀ F Vt R.tstar ≠ dynA R w₀ F Va R.tstar :=
  ⟨⟨(ideal_door_infty R).1, (ideal_door_infty R).2.1⟩, P.no_collision R.tstar R.tstar_mem⟩

end Bounded

section BoundedMain

variable {R : Race} {w₀ ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3} {F : ℝ → ℝ → ℝ → V3}

/-- 主定理の F（`DynamicEffects` を満たす F）の上では、x̂ は競走の時間の上で有界であり、二人は ℘ から
正の距離を保つ。 -/
theorem dyn_xhat_bounded_of_effects
    (P : DynamicPassage R w₀ (R.r ^ n₁) ε n₁ S X F (VtR (R.r ^ n₁)) (VaR R.r w₀ (R.r ^ n₁) n₁))
    (E : DynamicEffects R w₀ n₁ F) :
    (∃ B : ℝ, ∀ t ∈ Icc 0 (2 * R.tstar),
      |xhat (dynT R w₀ F (VtR (R.r ^ n₁)) t)| ≤ B ∧
      |xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)| ≤ B) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc 0 (2 * R.tstar),
      δ ≤ nsq (dynT R w₀ F (VtR (R.r ^ n₁)) t) ∧
      δ ≤ nsq (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) :=
  ⟨dyn_xhat_bounded P E.avoids_T E.avoids_A, dyn_away_from_wp P E.avoids_T E.avoids_A⟩

end BoundedMain

/-- **理想形では x̂ は有界でない**：どの B についても、t∗ の前に x̂(A_id(t)) > B となる時刻がある。 -/
theorem ideal_xhat_unbounded (R : Race) (B : ℝ) :
    ∃ t ∈ Ioo 0 R.tstar, B < xhat (R.idealA t) := by
  have hT := R.tstar_pos
  have hden : 0 < |B| + 2 := by positivity
  have hu0 : 0 < 1 / (|B| + 2) := by positivity
  have hu1 : 1 / (|B| + 2) < 1 := by
    rw [div_lt_one hden]
    linarith [abs_nonneg B]
  refine ⟨R.tstar * (1 - 1 / (|B| + 2)), ⟨by nlinarith, by nlinarith⟩, ?_⟩
  have hg : R.g (R.tstar * (1 - 1 / (|B| + 2))) = 1 / (|B| + 2) := by
    rw [R.g_eq]
    field_simp
    ring
  rw [Race.idealA, hg, xhat_G hu0.ne', one_div_one_div]
  linarith [le_abs_self B]

/-- **理想形の走者は扉 0 を通らない**：t ≠ t∗ では x̂(T_id(t)) ≠ 0、x̂(A_id(t)) ≠ 0 である。理想形の
走者はホーン対の上にとどまり、x̂ の符号は t∗ に ℘ を通って変わる（`ideal_door_infty`）。 -/
theorem ideal_no_door_zero (R : Race) {t : ℝ} (ht : t ≠ R.tstar) :
    xhat (R.idealT t) ≠ 0 ∧ xhat (R.idealA t) ≠ 0 := by
  have hg : R.g t ≠ 0 := fun h0 => ht ((R.g_eq_zero_iff t).mp h0)
  have hrg : R.r * R.g t ≠ 0 := mul_ne_zero R.r_pos.ne' hg
  exact ⟨xhat_G_ne_zero hrg 0, xhat_G_ne_zero hg _⟩

/-! ### 対称面の点は、純虚数の助変数の点の正の倍である（球の条件なし） -/

/-- **対称面の ℘ でない点は、𝔾(i, v) の正の倍である**：q₁ = 0、q ≠ ℘ なら、ある κ > 0 と v について
q = κ𝔾(i, v) である。したがって q は、扉 0 の方程式の複素表示での解（純虚数の助変数）の点である。 -/
theorem mirror_point_scaled {q : V3} (h1 : q.1 = 0) (hne : q ≠ wp) :
    ∃ κ v : ℝ, 0 < κ ∧ q = κ • GG ⟨0, 1⟩ v := by
  obtain ⟨q1, q2, q3⟩ := q
  have h1' : q1 = 0 := h1
  subst h1'
  have hsq : nsq ((0 : ℝ), q2, q3) = q2 ^ 2 + q3 ^ 2 := by
    simp only [nsq, dot]
    ring
  have hpos : 0 < q2 ^ 2 + q3 ^ 2 := by rw [← hsq]; exact nsq_pos_of_ne hne
  have hρpos : 0 < √(q2 ^ 2 + q3 ^ 2) := Real.sqrt_pos.mpr hpos
  let z : ℂ := ⟨q3, -q2⟩
  have hz : ‖z‖ = √(q2 ^ 2 + q3 ^ 2) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    congr 1
    show q3 ^ 2 + (-q2) ^ 2 = q2 ^ 2 + q3 ^ 2
    ring
  have hc : ‖z‖ * cos (Complex.arg z) = q3 := Complex.norm_mul_cos_arg z
  have hs : ‖z‖ * sin (Complex.arg z) = -q2 := Complex.norm_mul_sin_arg z
  refine ⟨2 * ‖z‖, Complex.arg z, by rw [hz]; positivity, ?_⟩
  rw [GG_imaginary]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (0 : ℝ) = 2 * ‖z‖ * 0
    ring
  · show q2 = 2 * ‖z‖ * (-((1 : ℝ) ^ 3 / (1 + (1 : ℝ) ^ 4)) * sin (Complex.arg z))
    norm_num
    linarith
  · show q3 = 2 * ‖z‖ * ((1 : ℝ) ^ 3 / (1 + (1 : ℝ) ^ 4) * cos (Complex.arg z))
    norm_num
    linarith

section DynScaled

variable {R : Race} {w₀ ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3} {F : ℝ → ℝ → ℝ → V3}

/-- **亀が対称面を横切る点は、純虚数の助変数の点の正の倍である**（球の条件なし）。 -/
theorem door_zero_T_scaled
    (P : DynamicPassage R w₀ (R.r ^ n₁) ε n₁ S X F (VtR (R.r ^ n₁)) (VaR R.r w₀ (R.r ^ n₁) n₁))
    (E : DynamicEffects R w₀ n₁ F) (hn : 1 ≤ n₁) :
    ∃ t ∈ Ioo R.tstar (2 * R.tstar), ∃ κ v : ℝ, 0 < κ ∧
      dynT R w₀ F (VtR (R.r ^ n₁)) t = κ • GG ⟨0, 1⟩ v := by
  obtain ⟨t, ht, -, h1, -, -⟩ := door_zero_T P E hn
  have htI : t ∈ Icc 0 (2 * R.tstar) := ⟨by linarith [ht.1, R.tstar_pos], ht.2.le⟩
  obtain ⟨κ, v, hκ, he⟩ := mirror_point_scaled h1 (E.avoids_T t htI)
  exact ⟨t, ht, κ, v, hκ, he⟩

/-- **アキレスが対称面を横切る点は、純虚数の助変数の点の正の倍である**（球の条件なし）。 -/
theorem door_zero_A_scaled
    (P : DynamicPassage R w₀ (R.r ^ n₁) ε n₁ S X F (VtR (R.r ^ n₁)) (VaR R.r w₀ (R.r ^ n₁) n₁))
    (E : DynamicEffects R w₀ n₁ F) :
    ∃ t ∈ Ioo 0 R.tstar, ∃ κ v : ℝ, 0 < κ ∧
      dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t = κ • GG ⟨0, 1⟩ v := by
  obtain ⟨t, ht, -, h1, -, -⟩ := door_zero_A P E
  have htI : t ∈ Icc 0 (2 * R.tstar) := ⟨ht.1.le, by linarith [ht.2, R.tstar_pos]⟩
  obtain ⟨κ, v, hκ, he⟩ := mirror_point_scaled h1 (E.avoids_A t htI)
  exact ⟨t, ht, κ, v, hκ, he⟩

end DynScaled

/-! ### 自由：衝突の方程式が実数解をもつ導線ともたない導線 -/

/-- cos と sin が等しい二つの角度は、2π の整数倍だけ違う。 -/
theorem angle_eq_of_cos_sin {a b : ℝ} (hc : cos a = cos b) (hs : sin a = sin b) :
    ∃ m : ℤ, b = a + m * (2 * π) := by
  rcases Real.cos_eq_cos_iff.mp hc with ⟨k, h | h⟩
  · exact ⟨k, by rw [h]; ring⟩
  · have e : b = (k : ℝ) * (2 * π) - a := by rw [h]; ring
    have h2 : sin b = -sin a := by rw [e, Real.sin_int_mul_two_pi_sub]
    have h3 : sin a = 0 := by linarith
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h3
    refine ⟨k - n, ?_⟩
    rw [e, ← hn]
    push_cast
    ring

/-- **静的な面の上の衝突の方程式と自由**：どの導線 V_T、V_A についても、静的な面の上の二人は、競走の
時間の t ≠ t∗ には衝突しない。t∗ に衝突するのは、中央での二人の角度が 2π を法として等しいとき、その
ときに限る。すなわち、衝突の方程式が競走の時間に実数解をもつことと、中央の角度が 2π を法として等しい
ことは同値であり、そのときの解は t∗ だけである。 -/
theorem static_collision_iff (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (Vt Va : ℝ → ℝ) :
    (∀ t ∈ Icc 0 (2 * R.tstar), t ≠ R.tstar →
        R.runT (Shat w₀) Vt t ≠ R.runA (Shat w₀) Va t) ∧
      (R.runT (Shat w₀) Vt R.tstar = R.runA (Shat w₀) Va R.tstar ↔
        ∃ m : ℤ, Va 0 = Vt 0 + m * (2 * π)) := by
  refine ⟨?_, ?_⟩
  · intro t ht htne he
    rw [runT_Shat_eq R h0 h1 _ ht, runA_Shat_eq R h0 h1 _ ht] at he
    have hlt := nsq_Sig_lt h0.ne' (by nlinarith) (R.abs_r_g_lt htne) (R.abs_g_le ht.1 ht.2)
      (Vt (R.r * R.g t)) (Va (R.g t))
    simp only [Race.runT, Race.runA] at he
    rw [he] at hlt
    exact lt_irrefl _ hlt
  · have hBB : 0 < BB w₀ 0 := by
      rw [BB_zero]
      exact bb_pos (rho_pos h0.ne' 0)
    constructor
    · intro he
      rw [runT_Shat_eq R h0 h1 _ R.tstar_mem, runA_Shat_eq R h0 h1 _ R.tstar_mem] at he
      simp only [Race.runT, Race.runA, R.g_tstar, mul_zero, Sig_zero h0] at he
      have h2 : BB w₀ 0 * cos (Vt 0) = BB w₀ 0 * cos (Va 0) := congrArg (fun q : V3 => q.2.1) he
      have h3 : -(BB w₀ 0 * sin (Vt 0)) = -(BB w₀ 0 * sin (Va 0)) :=
        congrArg (fun q : V3 => q.2.2) he
      have hc : cos (Vt 0) = cos (Va 0) := mul_left_cancel₀ hBB.ne' h2
      have hs : sin (Vt 0) = sin (Va 0) := mul_left_cancel₀ hBB.ne' (neg_injective h3)
      exact angle_eq_of_cos_sin hc hs
    · rintro ⟨m, hm⟩
      exact run_collision_of_centre_angle R (Shat_periodic w₀) hm

/-- 中央での二人の角度が 2π を法として等しい導線は、`DynamicPassage` を満たさない（`DynamicPassage` は
全時刻の非衝突を含む）。 -/
theorem not_dynamicPassage_of_centre_angle {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3}
    {F : ℝ → ℝ → ℝ → V3} {Vt Va : ℝ → ℝ} {m : ℤ} (h : Va 0 = Vt 0 + m * (2 * π)) :
    ¬ DynamicPassage R w₀ c ε n₁ S X F Vt Va := fun P => P.centre_angle_ne m h

/-! ### 岸の上の導線：角度の関数と、面に写した位置の区別 -/

/-- **岸の上の導線の位置**：c ≤ |w| ≤ 1 の岸の上では、面に写した導線の点は理想形の点である。亀は
G(w, 0)、アキレスは G(w, θ(w)) にいる（右岸でも左岸でも）。 -/
theorem guide_position_shore {r w₀ c w : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (hc : w₀ ≤ c)
    (hw : c ≤ |w|) (hw1 : |w| ≤ 1) (n₁ : ℕ) :
    Shat w₀ w (VtR c w) = G w 0 ∧ Shat w₀ w (VaR r w₀ c n₁ w) = G w (theta r w) := by
  rw [Shat_neck h0 h1 hw1, Shat_neck h0 h1 hw1]
  rcases le_abs.mp hw with h | h
  · exact ⟨T_right h0 hc h, A_right h0 hc h n₁⟩
  · exact ⟨T_left h0 hc (by linarith), A_left h0 hc (by linarith) n₁⟩

/-- 右岸（w ≥ c）では、二つの導線の角度の差は θ(w) である。 -/
theorem twist_diff_right {r w₀ c w : ℝ} (h0 : 0 < w₀) (hc : w₀ ≤ c) (hw : c ≤ w) (n₁ : ℕ) :
    VaR r w₀ c n₁ w - VtR c w = theta r w := by
  obtain ⟨hT, hA⟩ := twist_shore_right (r := r) h0 hc hw n₁
  rw [hT, hA, sub_zero]

/-- 左岸（w ≤ −c）では、二つの導線の角度の差は 2π + 4πn₁ − θ(w) であり、θ(w) そのものではない。左岸
では面が G(w, π − v) なので、面に写した位置は右岸と同じ形 G(w, 0)、G(w, θ(w)) である
（`guide_position_shore`）。 -/
theorem twist_diff_left {r w₀ c w : ℝ} (h0 : 0 < w₀) (hc : w₀ ≤ c) (hw : w ≤ -c) (n₁ : ℕ) :
    VaR r w₀ c n₁ w - VtR c w = 2 * π + 4 * π * n₁ - theta r w := by
  obtain ⟨hT, hA⟩ := twist_shore_left (r := r) h0 hc hw n₁
  rw [hT, hA]
  ring

end Zeno.Smale
