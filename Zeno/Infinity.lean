/-
# Zeno.Infinity : 【仮定】1 の三つの内容

(a) 数え上げ：亀（v = 0）とアキレス（v = θ）のすれ違いは無限個で、℘ にしか集積しない。
(b) 捻り：θ は `Real.Angle` に極限をもたず、法線も極限をもたない。導線の極限は点 ℘ にだけある。
(c) 座標：x = 1/w は ℘ を `OnePoint ℝ` の ∞ に送り、両岸は同じ ∞ に向かう。

これらは定理であり、「℘ を無限遠点と見做す」こと自体はこの上に置く見做しである。
-/
import Zeno.Geometry
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Algebra.Order.Field

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology OnePoint

variable {r : ℝ}

/-! ### 無限の捻り -/

/-- 捻り θ(w) = 2π ln|w| / ln r。w = rⁿ でちょうど n 周する。 -/
def theta (r w : ℝ) : ℝ := 2 * π * (log |w| / log r)

theorem log_r_ne (hr0 : 0 < r) (hr1 : r < 1) : log r ≠ 0 :=
  (Real.log_neg hr0 hr1).ne

theorem theta_pow (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) : theta r (r ^ n) = n * (2 * π) := by
  have h := log_r_ne hr0 hr1
  simp only [theta, abs_of_pos (pow_pos hr0 n), Real.log_pow]
  field_simp

theorem theta_half (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    theta r (r ^ n * √r) = π + n * (2 * π) := by
  have h := log_r_ne hr0 hr1
  have hs : 0 < √r := Real.sqrt_pos.mpr hr0
  have hp : 0 < r ^ n * √r := mul_pos (pow_pos hr0 n) hs
  simp only [theta, abs_of_pos hp]
  rw [Real.log_mul (pow_pos hr0 n).ne' hs.ne', Real.log_pow, Real.log_sqrt hr0.le]
  field_simp
  ring

theorem tendsto_pow_right (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1,
     Eventually.of_forall fun n => pow_pos hr0 n⟩

theorem tendsto_pow_half_right (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => r ^ n * √r) atTop (𝓝[>] 0) := by
  have hs : 0 < √r := Real.sqrt_pos.mpr hr0
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => mul_pos (pow_pos hr0 n) hs⟩
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).mul_const √r

/-- 捻りの角は極限をもたない。円（無限遠端）の上には導線の極限がない。 -/
theorem no_angle_limit (hr0 : 0 < r) (hr1 : r < 1) :
    ¬ ∃ a : Real.Angle, Tendsto (fun w => ((theta r w : ℝ) : Real.Angle)) (𝓝[>] 0) (𝓝 a) := by
  rintro ⟨a, ha⟩
  have l1 := ha.comp (tendsto_pow_right hr0 hr1)
  have l2 := ha.comp (tendsto_pow_half_right hr0 hr1)
  have e1 : ∀ n : ℕ, ((theta r (r ^ n) : ℝ) : Real.Angle) = 0 := by
    intro n
    rw [theta_pow hr0 hr1, Real.Angle.natCast_mul_eq_nsmul]
    simp
  have e2 : ∀ n : ℕ, ((theta r (r ^ n * √r) : ℝ) : Real.Angle) = (π : Real.Angle) := by
    intro n
    rw [theta_half hr0 hr1, Real.Angle.coe_add, Real.Angle.natCast_mul_eq_nsmul]
    simp
  have h1 : a = 0 := by
    refine tendsto_nhds_unique l1 ?_
    simp [Function.comp_def, e1]
  have h2 : a = (π : Real.Angle) := by
    refine tendsto_nhds_unique l2 ?_
    simp [Function.comp_def, e2]
  exact Real.Angle.pi_ne_zero (h2.symm.trans h1)

/-- どんな導線も ℘ に収束する（v の連続性は要らない）。円は点に潰れている。 -/
theorem tendsto_G_wp (v : ℝ → ℝ) : Tendsto (fun w => G w (v w)) (𝓝 0) (𝓝 wp) := by
  have hD : ∀ w : ℝ, 1 ≤ D w := fun w => by
    unfold D
    have : 0 ≤ w ^ 4 := by positivity
    linarith
  have h3 : Tendsto (fun w : ℝ => |w| ^ 3) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun w : ℝ => |w| ^ 3) := continuous_abs.pow 3
    simpa using this.tendsto 0
  have h0 : Tendsto (fun w : ℝ => w / D w) (𝓝 0) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun w : ℝ => |w|) ?_ ?_
    · intro w
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (D_pos w)]
      exact div_le_self (abs_nonneg _) (hD w)
    · simpa using (continuous_abs (G := ℝ)).tendsto 0
  have h1 : Tendsto (fun w : ℝ => w ^ 3 * cos (v w) / D w) (𝓝 0) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun w : ℝ => |w| ^ 3) ?_ h3
    intro w
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (D_pos w), abs_mul, abs_pow]
    refine (div_le_self (by positivity) (hD w)).trans ?_
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  have h2 : Tendsto (fun w : ℝ => w ^ 3 * sin (v w) / D w) (𝓝 0) (𝓝 0) := by
    refine squeeze_zero_norm (a := fun w : ℝ => |w| ^ 3) ?_ h3
    intro w
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (D_pos w), abs_mul, abs_pow]
    refine (div_le_self (by positivity) (hD w)).trans ?_
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  exact h0.prodMk_nhds (h1.prodMk_nhds h2)

/-- N は v を固定すれば w について連続である。 -/
theorem continuous_N_w (v : ℝ) : Continuous fun w => N w v := by
  unfold N
  fun_prop

theorem N_zero (v : ℝ) : N 0 v = (0, cos v, sin v) := by
  simp [N]

/-- 無限に捻った導線では法線に極限がない。
連続性は通過則を決めない。ここが仮定2 の「自由」（L988）の居場所である。 -/
theorem normal_no_limit (hr0 : 0 < r) (hr1 : r < 1) :
    ¬ ∃ n₀ : V3, Tendsto (fun w => N w (theta r w)) (𝓝[>] 0) (𝓝 n₀) := by
  rintro ⟨n₀, h⟩
  have l1 := h.comp (tendsto_pow_right hr0 hr1)
  have l2 := h.comp (tendsto_pow_half_right hr0 hr1)
  have e1 : ∀ n : ℕ, N (r ^ n) (theta r (r ^ n)) = N (r ^ n) 0 := by
    intro n
    rw [theta_pow hr0 hr1]
    have hs : sin ((n : ℝ) * (2 * π)) = 0 := by
      rw [Real.sin_periodic.nat_mul_eq n]; simp
    simp [N, Real.cos_nat_mul_two_pi, hs]
  have e2 : ∀ n : ℕ, N (r ^ n * √r) (theta r (r ^ n * √r)) = N (r ^ n * √r) π := by
    intro n
    rw [theta_half hr0 hr1]
    simp [N, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]
  have t1 : Tendsto (fun n : ℕ => N (r ^ n) 0) atTop (𝓝 (N 0 0)) :=
    (continuous_N_w 0).continuousAt.tendsto.comp
      ((tendsto_pow_right hr0 hr1).mono_right nhdsWithin_le_nhds)
  have t2 : Tendsto (fun n : ℕ => N (r ^ n * √r) π) atTop (𝓝 (N 0 π)) :=
    (continuous_N_w π).continuousAt.tendsto.comp
      ((tendsto_pow_half_right hr0 hr1).mono_right nhdsWithin_le_nhds)
  have u1 : n₀ = N 0 0 := by
    refine tendsto_nhds_unique l1 ?_
    simpa [Function.comp_def, e1] using t1
  have u2 : n₀ = N 0 π := by
    refine tendsto_nhds_unique l2 ?_
    simpa [Function.comp_def, e2] using t2
  have h3 : N 0 0 = N 0 π := u1.symm.trans u2
  rw [N_zero, N_zero] at h3
  have h4 := congrArg (fun p : V3 => p.2.1) h3
  simp at h4
  norm_num at h4

/-! ### すれ違いの数え上げ -/

/-- w ≠ 0 で G が v について同じ点になるのは v が 2π の整数倍のときだけ。 -/
theorem G_eq_G_zero_iff {w : ℝ} (hw : w ≠ 0) (v : ℝ) : G w v = G w 0 ↔ cos v = 1 := by
  have hD := D_ne w
  have h3 : w ^ 3 ≠ 0 := pow_ne_zero 3 hw
  constructor
  · intro h
    have h2 := congrArg (fun p : V3 => p.2.1) h
    simp only [G, cos_zero, mul_one] at h2
    field_simp at h2
    linarith
  · intro h
    have hs : sin v = 0 := by
      have := sin_sq_add_cos_sq v
      rw [h] at this
      have h' : sin v ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff (by norm_num) |>.1 h'
    simp [G, h, hs]

/-- 亀（v = 0）とアキレス（v = θ）が同じ点に来るのは |w| = rⁿ（n ∈ ℤ）のときだけである。 -/
theorem meeting_iff (hr0 : 0 < r) (hr1 : r < 1) {w : ℝ} (hw : w ≠ 0) :
    G w (theta r w) = G w 0 ↔ ∃ n : ℤ, |w| = r ^ n := by
  have hlog := log_r_ne hr0 hr1
  have habs : 0 < |w| := abs_pos.mpr hw
  rw [G_eq_G_zero_iff hw, Real.cos_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h1 : log |w| / log r = n := by
      simp only [theta] at hn
      have hpi : (2 * π) ≠ 0 := by positivity
      field_simp at hn ⊢
      linarith
    have h2 : log |w| = n * log r := by
      field_simp at h1
      linarith
    have h3 : log |w| = log (r ^ n) := by
      rw [Real.log_zpow, h2]
    exact Real.log_injOn_pos (mem_Ioi.mpr habs) (mem_Ioi.mpr (zpow_pos hr0 n)) h3
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simp only [theta]
    rw [hn, Real.log_zpow]
    field_simp

/-- すれ違いの集合（右岸、腰 w = 1 まで）。 -/
def meetings (r : ℝ) : Set ℝ := {w | 0 < w ∧ w ≤ 1 ∧ G w (theta r w) = G w 0}

/-- すれ違いはちょうど Zeno のステップ rⁿ（n ∈ ℕ）である。 -/
theorem meetings_eq (hr0 : 0 < r) (hr1 : r < 1) :
    meetings r = range (fun n : ℕ => r ^ n) := by
  ext w
  constructor
  · rintro ⟨h0, h1, hm⟩
    obtain ⟨n, hn⟩ := (meeting_iff hr0 hr1 h0.ne').1 hm
    rw [abs_of_pos h0] at hn
    have hn0 : 0 ≤ n := by
      by_contra hneg
      have hlt : n < 0 := not_le.mp hneg
      have : 1 < r ^ n := one_lt_zpow_of_neg₀ hr0 hr1 hlt
      linarith
    refine ⟨n.toNat, ?_⟩
    simp only
    rw [hn, ← zpow_natCast, Int.toNat_of_nonneg hn0]
  · rintro ⟨n, rfl⟩
    simp only
    have hp := pow_pos hr0 n
    refine ⟨hp, pow_le_one₀ hr0.le hr1.le, ?_⟩
    refine (meeting_iff hr0 hr1 hp.ne').2 ⟨n, ?_⟩
    rw [abs_of_pos hp, zpow_natCast]

/-- すれ違いは無限個ある。 -/
theorem meetings_infinite (hr0 : 0 < r) (hr1 : r < 1) : (meetings r).Infinite := by
  rw [meetings_eq hr0 hr1]
  exact infinite_range_of_injective (pow_right_injective₀ hr0 hr1.ne)

/-- ℘ から離れた所ではすれ違いは有限個。集積点は ℘ だけである。 -/
theorem meetings_finite_off_wp (hr0 : 0 < r) (hr1 : r < 1) {w₀ : ℝ} (hw₀ : 0 < w₀) :
    (meetings r ∩ Ici w₀).Finite := by
  rw [meetings_eq hr0 hr1]
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  obtain ⟨N₀, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hw₀))
  refine ((finite_lt_nat N₀).image (fun n : ℕ => r ^ n)).subset ?_
  rintro w ⟨⟨n, rfl⟩, hw⟩
  refine ⟨n, ?_, rfl⟩
  by_contra hn
  have := hN n (not_lt.mp hn)
  exact absurd (mem_Ici.mp hw) (not_le.mpr this)

/-! ### Zeno のステップの一点コンパクト化 -/

/-- ステップの番号から w へ：n ↦ rⁿ、∞ ↦ 0。 -/
def stepPoint (r : ℝ) (o : OnePoint ℕ) : ℝ := OnePoint.elim o 0 (fun n => r ^ n)

@[simp] theorem stepPoint_infty (r : ℝ) : stepPoint r ∞ = 0 := rfl
@[simp] theorem stepPoint_coe (r : ℝ) (n : ℕ) : stepPoint r n = r ^ n := rfl

/-- ∞ が ℘ に当たる対応は連続である。 -/
theorem continuous_stepPoint (hr0 : 0 < r) (hr1 : r < 1) : Continuous (stepPoint r) := by
  rw [continuous_iff_from_nat]
  simpa using tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1

/-- この対応は単射である。導線の上で ℘ は番号の無限遠に当たる。 -/
theorem injective_stepPoint (hr0 : 0 < r) (hr1 : r < 1) : Function.Injective (stepPoint r) := by
  intro x y
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => simp
    | coe y =>
      intro h
      simp only [stepPoint_infty, stepPoint_coe] at h
      exact absurd h.symm (pow_pos hr0 y).ne'
  | coe x =>
    induction y using OnePoint.rec with
    | infty =>
      intro h
      simp only [stepPoint_infty, stepPoint_coe] at h
      exact absurd h (pow_pos hr0 x).ne'
    | coe y =>
      intro h
      simp only [stepPoint_coe] at h
      rw [pow_right_injective₀ hr0 hr1.ne h]

/-! ### x = 1/w と一点コンパクト化 -/

/-- x = 1/w を `OnePoint ℝ` の値とする写像。℘（w = 0）は ∞ に行く。 -/
def invOP (w : ℝ) : OnePoint ℝ := if w = 0 then ∞ else ((w⁻¹ : ℝ) : OnePoint ℝ)

theorem invOP_zero : invOP 0 = ∞ := by simp [invOP]

theorem invOP_of_ne {w : ℝ} (hw : w ≠ 0) : invOP w = ((w⁻¹ : ℝ) : OnePoint ℝ) := by
  simp [invOP, hw]

theorem invOP_eq_infty_iff {w : ℝ} : invOP w = ∞ ↔ w = 0 := by
  by_cases hw : w = 0
  · simp [hw, invOP_zero]
  · simp [invOP_of_ne hw, hw]

theorem invOP_ne_zero (w : ℝ) : invOP w ≠ ((0 : ℝ) : OnePoint ℝ) := by
  by_cases hw : w = 0
  · simp [hw, invOP_zero]
  · rw [invOP_of_ne hw]
    intro h
    have := OnePoint.coe_injective h
    exact (inv_ne_zero hw) this

/-- x = 1/w は `OnePoint ℝ` の値として連続である。両岸は同じ ∞ に向かう。 -/
theorem continuous_invOP : Continuous invOP := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · subst hw
    rw [continuousAt_iff_punctured_nhds, invOP_zero]
    have h1 : Tendsto (fun w : ℝ => ((w⁻¹ : ℝ) : OnePoint ℝ)) (𝓝[≠] 0) (𝓝 ∞) := by
      have h2 : Tendsto (Inv.inv : ℝ → ℝ) (𝓝[≠] 0) (Bornology.cobounded ℝ) :=
        tendsto_inv₀_nhdsNE_zero
      rw [Metric.cobounded_eq_cocompact, ← coclosedCompact_eq_cocompact] at h2
      exact OnePoint.tendsto_coe_infty.comp h2
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    rw [invOP_of_ne hw]
  · have h1 : ContinuousAt (fun w : ℝ => ((w⁻¹ : ℝ) : OnePoint ℝ)) w :=
      OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hw)
    refine h1.congr ?_
    filter_upwards [isOpen_ne.mem_nhds hw] with y hy
    rw [invOP_of_ne hy]

/-- 実数値のままでは両岸の行き先が違う（右は +∞、左は −∞）。 -/
theorem inv_right_left :
    Tendsto (fun w : ℝ => w⁻¹) (𝓝[>] 0) atTop ∧ Tendsto (fun w : ℝ => w⁻¹) (𝓝[<] 0) atBot :=
  ⟨tendsto_inv_nhdsGT_zero, tendsto_inv_nhdsLT_zero⟩

/-- 「二つの扉」。`OnePoint ℝ` の連続な径路が正から負へ移るなら 0 か ∞ を通る。 -/
theorem two_doors {a b : ℝ} (hab : a ≤ b) {γ : ℝ → OnePoint ℝ} (hγ : ContinuousOn γ (Icc a b))
    {xa xb : ℝ} (h0 : γ a = (xa : OnePoint ℝ)) (hxa : 0 < xa)
    (h1 : γ b = (xb : OnePoint ℝ)) (hxb : xb < 0) :
    ∃ t ∈ Icc a b, γ t = ((0 : ℝ) : OnePoint ℝ) ∨ γ t = ∞ := by
  by_contra hcon
  push Not at hcon
  let U : Set (OnePoint ℝ) := (↑) '' Ioi (0 : ℝ)
  let V : Set (OnePoint ℝ) := (↑) '' Iio (0 : ℝ)
  have hU : IsOpen U := OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_Ioi
  have hV : IsOpen V := OnePoint.isOpenEmbedding_coe.isOpenMap _ isOpen_Iio
  have hconn : IsPreconnected (γ '' Icc a b) := isPreconnected_Icc.image γ hγ
  have hcover : γ '' Icc a b ⊆ U ∪ V := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨hne0, hneinf⟩ := hcon t ht
    induction hy : γ t using OnePoint.rec with
    | infty => exact absurd hy hneinf
    | coe x =>
      rw [hy] at hne0
      have hx0 : x ≠ 0 := fun h => hne0 (by rw [h])
      rcases lt_or_gt_of_ne hx0 with h | h
      · exact Or.inr ⟨x, h, rfl⟩
      · exact Or.inl ⟨x, h, rfl⟩
  have hmemU : (γ '' Icc a b ∩ U).Nonempty :=
    ⟨γ a, ⟨a, left_mem_Icc.mpr hab, rfl⟩, by rw [h0]; exact ⟨xa, hxa, rfl⟩⟩
  have hmemV : (γ '' Icc a b ∩ V).Nonempty :=
    ⟨γ b, ⟨b, right_mem_Icc.mpr hab, rfl⟩, by rw [h1]; exact ⟨xb, hxb, rfl⟩⟩
  obtain ⟨y, -, ⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hx₂e⟩⟩ := hconn U V hU hV hcover hmemU hmemV
  have : x₂ = x₁ := OnePoint.coe_injective hx₂e
  subst this
  exact lt_asymm (mem_Ioi.mp hx₁) (mem_Iio.mp hx₂)

end Zeno.Model
