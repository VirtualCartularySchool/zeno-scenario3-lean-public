/-
# Zeno.KleinProfile : クラインの壺型閉包の管の輪郭（定数、角 θ、半径 R）

管の子午線は、子午半平面 (q₁, ρ) の極座標 (r, θ) で r = R(θ)、θ ∈ [π/4, 3π/4] のグラフである。
R² = σ/2 で、σ は口の近く（|θ − π/2| ≥ u₂）でホーンの子午線 sin 2|θ − π/2| に一致し、
中央（|θ − π/2| ≤ u₁）で 1 になる。角 θ(w) は w ≤ wₐ で arctan(w²) に一致し、
[w₁, 4 − w₁] で一次式、θ(4 − w) = π − θ(w)、(0, 4) で θ′ > 0 である。

ここの定理は恒等式と不等式であり、見做しは一つも含まない。
-/
import Zeno.Neck
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### 定数 -/

/-- θ₀ = arctan(w₀²)。 -/
def th0 (w₀ : ℝ) : ℝ := arctan (w₀ ^ 2)

/-- u₁ = (π/4 + θ₀)/2。 -/
def u1 (w₀ : ℝ) : ℝ := (π / 4 + th0 w₀) / 2

/-- u₂ = (π/4 + u₁)/2。 -/
def u2 (w₀ : ℝ) : ℝ := (π / 4 + u1 w₀) / 2

/-- w₁ = √(cot u₂)。arctan(w₁²) = π/2 − u₂。 -/
def w1 (w₀ : ℝ) : ℝ := √((tan (u2 w₀))⁻¹)

/-- wₐ = (1 + w₁)/2。[1, wₐ] で管は G に正確に等しい。 -/
def wa (w₀ : ℝ) : ℝ := (1 + w1 w₀) / 2

/-- 管の角の傾き κ_T = u₂/(2 − wₐ)。 -/
def kT (w₀ : ℝ) : ℝ := u2 w₀ / (2 - wa w₀)

section Constants

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 in
theorem th0_pos : 0 < th0 w₀ := arctan_pos.mpr (by positivity)

include h0 h1 in
theorem th0_lt : th0 w₀ < π / 4 := by
  rw [th0, ← arctan_one]
  exact arctan_strictMono (by nlinarith)

include h0 h1 in
theorem u1_lt : u1 w₀ < π / 4 := by
  have := th0_lt h0 h1
  simp only [u1]; linarith

include h0 h1 in
theorem th0_lt_u1 : th0 w₀ < u1 w₀ := by
  have := th0_lt h0 h1
  simp only [u1]; linarith

include h0 in
theorem u1_pos : 0 < u1 w₀ := by
  have := th0_pos h0
  have := pi_pos
  simp only [u1]; linarith

include h0 h1 in
theorem u1_lt_u2 : u1 w₀ < u2 w₀ := by
  have := u1_lt h0 h1
  simp only [u2]; linarith

include h0 h1 in
theorem u2_lt : u2 w₀ < π / 4 := by
  have := u1_lt h0 h1
  simp only [u2]; linarith

include h0 in
theorem u2_pos : 0 < u2 w₀ := by
  have := u1_pos h0
  have := pi_pos
  simp only [u2]; linarith

include h0 in
theorem u2_ge : 3 * π / 16 ≤ u2 w₀ := by
  have := th0_pos h0
  simp only [u2, u1]; linarith

include h0 h1 in
theorem tan_u2_pos : 0 < tan (u2 w₀) :=
  tan_pos_of_pos_of_lt_pi_div_two (u2_pos h0) (by linarith [u2_lt h0 h1, pi_pos])

include h0 h1 in
theorem tan_u2_lt_one : tan (u2 w₀) < 1 := by
  rw [← tan_pi_div_four]
  exact tan_lt_tan_of_lt_of_lt_pi_div_two (by linarith [u2_pos h0, pi_pos])
    (by linarith [pi_pos]) (u2_lt h0 h1)

include h0 h1 in
theorem tan_u2_gt : 1 / 4 < tan (u2 w₀) := by
  have h := lt_tan (u2_pos h0) (by linarith [u2_lt h0 h1, pi_pos])
  have := u2_ge h0
  have := two_le_pi
  linarith

include h0 h1 in
theorem w1_sq : w1 w₀ ^ 2 = (tan (u2 w₀))⁻¹ := by
  simp only [w1]
  exact sq_sqrt (inv_nonneg.mpr (tan_u2_pos h0 h1).le)

include h0 h1 in
theorem w1_gt_one : 1 < w1 w₀ := by
  simp only [w1]
  rw [lt_sqrt zero_le_one, one_pow]
  exact one_lt_inv_iff₀.mpr ⟨tan_u2_pos h0 h1, tan_u2_lt_one h0 h1⟩

include h0 h1 in
theorem w1_lt_two : w1 w₀ < 2 := by
  simp only [w1]
  rw [sqrt_lt' (by norm_num)]
  have h := tan_u2_gt h0 h1
  have h2 := tan_u2_pos h0 h1
  rw [inv_lt_comm₀ h2 (by norm_num)]
  linarith

include h0 h1 in
theorem arctan_w1_sq : arctan (w1 w₀ ^ 2) = π / 2 - u2 w₀ := by
  rw [w1_sq h0 h1, arctan_inv_of_pos (tan_u2_pos h0 h1),
    arctan_tan (by linarith [u2_pos h0, pi_pos]) (by linarith [u2_lt h0 h1, pi_pos])]

include h0 h1 in
theorem wa_gt_one : 1 < wa w₀ := by
  have := w1_gt_one h0 h1
  simp only [wa]; linarith

include h0 h1 in
theorem wa_lt_w1 : wa w₀ < w1 w₀ := by
  have := w1_gt_one h0 h1
  simp only [wa]; linarith

include h0 h1 in
theorem wa_lt_two : wa w₀ < 2 := by
  have := w1_lt_two h0 h1
  simp only [wa]; linarith

include h0 h1 in
theorem kT_pos : 0 < kT w₀ := by
  have := wa_lt_two h0 h1
  have := u2_pos h0
  simp only [kT]
  exact div_pos this (by linarith)

include h0 h1 in
theorem kT_mul : kT w₀ * (wa w₀ - 2) = -u2 w₀ := by
  have := wa_lt_two h0 h1
  simp only [kT]
  field_simp
  ring

end Constants

/-! ### 遷移関数 χ₁ と角 θ -/

/-- χ₁ : w ≤ wₐ で 0、w ≥ w₁ で 1、単調。 -/
def chi1 (w₀ w : ℝ) : ℝ := s₀ ((w - wa w₀) / (w1 w₀ - wa w₀))

/-- 口の角 f(w) = arctan(w²)。 -/
def fl (w : ℝ) : ℝ := arctan (w ^ 2)

/-- 管の中央の一次式 g(w) = π/2 + κ_T(w − 2)。 -/
def gl (w₀ w : ℝ) : ℝ := π / 2 + kT w₀ * (w - 2)

/-- 口での差 Dθ(w) = (1 − χ₁(w))(f(w) − g(w))。w ≥ w₁ で 0。 -/
def Dth (w₀ w : ℝ) : ℝ := (1 - chi1 w₀ w) * (fl w - gl w₀ w)

/-- 管の角 θ(w) = g(w) + Dθ(w) − Dθ(4 − w)。 -/
def thT (w₀ w : ℝ) : ℝ := gl w₀ w + Dth w₀ w - Dth w₀ (4 - w)

section Angle

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
theorem chi1_of_le {w : ℝ} (hw : w ≤ wa w₀) : chi1 w₀ w = 0 := by
  have hd : 0 < w1 w₀ - wa w₀ := by linarith [wa_lt_w1 h0 h1]
  have : (w - wa w₀) / (w1 w₀ - wa w₀) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp [chi1, smoothTransition.zero_of_nonpos this]

include h0 h1 in
theorem chi1_of_ge {w : ℝ} (hw : w1 w₀ ≤ w) : chi1 w₀ w = 1 := by
  have hd : 0 < w1 w₀ - wa w₀ := by linarith [wa_lt_w1 h0 h1]
  have : 1 ≤ (w - wa w₀) / (w1 w₀ - wa w₀) := by
    rw [le_div_iff₀ hd]; linarith
  simp [chi1, smoothTransition.one_of_one_le this]

theorem chi1_nonneg (w₀ w : ℝ) : 0 ≤ chi1 w₀ w := smoothTransition.nonneg _

theorem chi1_le_one (w₀ w : ℝ) : chi1 w₀ w ≤ 1 := smoothTransition.le_one _

theorem contDiff_chi1 (w₀ : ℝ) : ContDiff ℝ ∞ (chi1 w₀) := by
  unfold chi1
  refine Real.smoothTransition.contDiff.comp ?_
  fun_prop

include h0 h1 in
theorem chi1_monotone : Monotone (chi1 w₀) := by
  have hd : 0 < w1 w₀ - wa w₀ := by linarith [wa_lt_w1 h0 h1]
  intro x y hxy
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (by linarith) hd.le

include h0 h1 in
theorem deriv_chi1_nonneg (w : ℝ) : 0 ≤ deriv (chi1 w₀) w :=
  (chi1_monotone h0 h1).deriv_nonneg

include h0 h1 in
theorem deriv_chi1_eq_zero {w : ℝ} (hw : w < wa w₀ ∨ w1 w₀ < w) : deriv (chi1 w₀) w = 0 := by
  rcases hw with hw | hw
  · have e : chi1 w₀ =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hw] with y hy using chi1_of_le h0 h1 (le_of_lt hy)
    rw [e.deriv_eq]; simp
  · have e : chi1 w₀ =ᶠ[𝓝 w] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds hw] with y hy using chi1_of_ge h0 h1 (le_of_lt hy)
    rw [e.deriv_eq]; simp

theorem hasDerivAt_chi1 (w₀ w : ℝ) : HasDerivAt (chi1 w₀) (deriv (chi1 w₀) w) w :=
  ((contDiff_chi1 w₀).differentiable (by simp) w).hasDerivAt

theorem contDiff_fl : ContDiff ℝ ∞ fl := by
  unfold fl
  exact contDiff_arctan.comp (contDiff_id.pow 2)

theorem hasDerivAt_fl (w : ℝ) : HasDerivAt fl (2 * w / (1 + w ^ 4)) w := by
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  have h := (hasDerivAt_arctan (w ^ 2)).comp w h2
  refine h.congr_deriv ?_
  have e : (w ^ 2) ^ 2 = w ^ 4 := by ring
  rw [e]
  field_simp

theorem fl_strictMonoOn : StrictMonoOn fl (Ici 0) := by
  intro x hx y hy hxy
  simp only [fl]
  exact arctan_strictMono (pow_lt_pow_left₀ hxy hx (by norm_num))

theorem fl_one : fl 1 = π / 4 := by simp [fl, arctan_one]

theorem fl_nonneg (w : ℝ) : 0 ≤ fl w := arctan_nonneg.mpr (sq_nonneg _)

theorem fl_lt_pi_div_two (w : ℝ) : fl w < π / 2 := arctan_lt_pi_div_two _

theorem contDiff_gl (w₀ : ℝ) : ContDiff ℝ ∞ (gl w₀) := by
  unfold gl; fun_prop

theorem hasDerivAt_gl (w₀ w : ℝ) : HasDerivAt (gl w₀) (kT w₀) w := by
  have h := ((hasDerivAt_id w).sub_const 2).const_mul (kT w₀) |>.const_add (π / 2)
  show HasDerivAt (fun x => π / 2 + kT w₀ * (x - 2)) (kT w₀) w
  simpa using h

theorem contDiff_Dth (w₀ : ℝ) : ContDiff ℝ ∞ (Dth w₀) := by
  unfold Dth
  exact (contDiff_const.sub (contDiff_chi1 w₀)).mul (contDiff_fl.sub (contDiff_gl w₀))

theorem hasDerivAt_Dth (w₀ w : ℝ) :
    HasDerivAt (Dth w₀)
      (-(deriv (chi1 w₀) w) * (fl w - gl w₀ w) +
        (1 - chi1 w₀ w) * (2 * w / (1 + w ^ 4) - kT w₀)) w := by
  have h := ((hasDerivAt_chi1 w₀ w).const_sub 1).mul ((hasDerivAt_fl w).sub (hasDerivAt_gl w₀ w))
  have e : Dth w₀ = (fun x => 1 - chi1 w₀ x) * (fl - gl w₀) := by
    funext x; simp [Dth]
  rw [e]
  refine h.congr_deriv ?_
  simp only [Pi.sub_apply]

theorem contDiff_thT (w₀ : ℝ) : ContDiff ℝ ∞ (thT w₀) := by
  unfold thT
  refine ((contDiff_gl w₀).add (contDiff_Dth w₀)).sub ((contDiff_Dth w₀).comp ?_)
  fun_prop

theorem hasDerivAt_thT (w₀ w : ℝ) :
    HasDerivAt (thT w₀) (kT w₀ + deriv (Dth w₀) w + deriv (Dth w₀) (4 - w)) w := by
  have h1 := hasDerivAt_gl w₀ w
  have h2 : HasDerivAt (Dth w₀) (deriv (Dth w₀) w) w :=
    ((contDiff_Dth w₀).differentiable (by simp) w).hasDerivAt
  have h3 : HasDerivAt (fun w : ℝ => 4 - w) (-1) w := by
    simpa using (hasDerivAt_id w).const_sub 4
  have h4 : HasDerivAt (Dth w₀) (deriv (Dth w₀) (4 - w)) (4 - w) :=
    ((contDiff_Dth w₀).differentiable (by simp) (4 - w)).hasDerivAt
  have h5 := h4.comp w h3
  have e : thT w₀ = (gl w₀ + Dth w₀) - (Dth w₀ ∘ fun w => 4 - w) := by
    funext x; simp [thT]
  rw [e]
  refine ((h1.add h2).sub h5).congr_deriv ?_
  ring

include h0 h1 in
theorem Dth_of_ge {w : ℝ} (hw : w1 w₀ ≤ w) : Dth w₀ w = 0 := by
  simp [Dth, chi1_of_ge h0 h1 hw]

include h0 h1 in
theorem Dth_of_le {w : ℝ} (hw : w ≤ wa w₀) : Dth w₀ w = fl w - gl w₀ w := by
  simp [Dth, chi1_of_le h0 h1 hw]

include h0 h1 in
theorem deriv_Dth_of_gt {w : ℝ} (hw : w1 w₀ < w) : deriv (Dth w₀) w = 0 := by
  have e : Dth w₀ =ᶠ[𝓝 w] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hw] with y hy using Dth_of_ge h0 h1 (le_of_lt hy)
  rw [e.deriv_eq]; simp

/-- 対称性 θ(4 − w) = π − θ(w)。 -/
theorem thT_symm (w₀ w : ℝ) : thT w₀ (4 - w) = π - thT w₀ w := by
  have e : (4 : ℝ) - (4 - w) = w := by ring
  simp only [thT, gl, e]
  ring

include h0 h1 in
theorem thT_of_le {w : ℝ} (hw : w ≤ wa w₀) : thT w₀ w = fl w := by
  have h2 : w1 w₀ ≤ 4 - w := by linarith [wa_lt_w1 h0 h1, w1_lt_two h0 h1]
  simp only [thT, Dth_of_le h0 h1 hw, Dth_of_ge h0 h1 h2]
  ring

include h0 h1 in
theorem thT_of_mid {w : ℝ} (hw1 : w1 w₀ ≤ w) (hw2 : w ≤ 4 - w1 w₀) : thT w₀ w = gl w₀ w := by
  have h2 : w1 w₀ ≤ 4 - w := by linarith
  simp only [thT, Dth_of_ge h0 h1 hw1, Dth_of_ge h0 h1 h2]
  ring

include h0 h1 in
theorem thT_of_ge {w : ℝ} (hw : 4 - wa w₀ ≤ w) : thT w₀ w = π - fl (4 - w) := by
  have e : w = 4 - (4 - w) := by ring
  rw [e, thT_symm, thT_of_le h0 h1 (by linarith)]
  ring_nf

include h0 h1 in
theorem thT_one : thT w₀ 1 = π / 4 := by
  rw [thT_of_le h0 h1 (wa_gt_one h0 h1).le, fl_one]

include h0 h1 in
theorem thT_two : thT w₀ 2 = π / 2 := by
  have := w1_lt_two h0 h1
  rw [thT_of_mid h0 h1 this.le (by linarith)]
  simp [gl]

include h0 h1 in
theorem thT_three : thT w₀ 3 = 3 * π / 4 := by
  have e : (3 : ℝ) = 4 - 1 := by norm_num
  rw [e, thT_symm, thT_one h0 h1]
  ring

include h0 h1 in
/-- 遷移区間 [wₐ, w₁] で g ≥ f。 -/
theorem fl_le_gl {w : ℝ} (hw1 : wa w₀ ≤ w) (hw2 : w ≤ w1 w₀) : fl w ≤ gl w₀ w := by
  have hk := kT_pos h0 h1
  have h2 : gl w₀ (wa w₀) = π / 2 - u2 w₀ := by
    simp only [gl]
    rw [kT_mul h0 h1]; ring
  have h3 : gl w₀ (wa w₀) ≤ gl w₀ w := by
    simp only [gl]
    nlinarith
  have h4 : fl w ≤ fl (w1 w₀) :=
    fl_strictMonoOn.monotoneOn (by linarith [wa_gt_one h0 h1] : (0 : ℝ) ≤ w)
      (by linarith [w1_gt_one h0 h1] : (0 : ℝ) ≤ w1 w₀) hw2
  have h5 : fl (w1 w₀) = π / 2 - u2 w₀ := arctan_w1_sq h0 h1
  linarith

include h0 h1 in
/-- 核の不等式：x > 0 で κ_T + Dθ′(x) > 0。 -/
theorem core_pos {x : ℝ} (hx0 : 0 < x) : 0 < kT w₀ + deriv (Dth w₀) x := by
  rw [(hasDerivAt_Dth w₀ x).deriv]
  have hk := kT_pos h0 h1
  have hf : 0 < 2 * x / (1 + x ^ 4) := by positivity
  have hc0 := chi1_nonneg w₀ x
  have hc1 := chi1_le_one w₀ x
  have hd0 := deriv_chi1_nonneg h0 h1 x
  -- 第三項は 0 以上
  have h3 : 0 ≤ -(deriv (chi1 w₀) x) * (fl x - gl w₀ x) := by
    by_cases hd : deriv (chi1 w₀) x = 0
    · rw [hd]; simp
    · have hin : wa w₀ ≤ x ∧ x ≤ w1 w₀ := by
        by_contra hc
        apply hd
        apply deriv_chi1_eq_zero h0 h1
        by_cases h : wa w₀ ≤ x
        · right
          by_contra h'
          exact hc ⟨h, le_of_not_gt h'⟩
        · left; exact lt_of_not_ge h
      have := fl_le_gl h0 h1 hin.1 hin.2
      nlinarith
  -- 第一・第二項は正の凸結合
  have h12 : 0 < (1 - chi1 w₀ x) * (2 * x / (1 + x ^ 4)) + chi1 w₀ x * kT w₀ := by
    rcases lt_or_eq_of_le hc1 with hlt | heq
    · have : 0 < (1 - chi1 w₀ x) * (2 * x / (1 + x ^ 4)) :=
        mul_pos (by linarith) hf
      nlinarith
    · rw [heq]; simpa using hk
  nlinarith

include h0 h1 in
theorem deriv_thT_pos {w : ℝ} (hw0 : 0 < w) (hw4 : w < 4) : 0 < deriv (thT w₀) w := by
  rw [(hasDerivAt_thT w₀ w).deriv]
  have hw1 := w1_lt_two h0 h1
  by_cases hw : w ≤ 2
  · have e : deriv (Dth w₀) (4 - w) = 0 := deriv_Dth_of_gt h0 h1 (by linarith)
    rw [e, add_zero]
    exact core_pos h0 h1 hw0
  · push Not at hw
    have e : deriv (Dth w₀) w = 0 := deriv_Dth_of_gt h0 h1 (by linarith)
    rw [e, add_zero]
    exact core_pos h0 h1 (by linarith)

include h0 h1 in
theorem thT_strictMonoOn : StrictMonoOn (thT w₀) (Icc 0 4) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 4) (contDiff_thT w₀).continuous.continuousOn
    fun x hx => ?_
  rw [interior_Icc] at hx
  exact deriv_thT_pos h0 h1 hx.1 hx.2

include h0 h1 in
theorem thT_mem {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) : π / 4 ≤ thT w₀ w ∧ thT w₀ w ≤ 3 * π / 4 := by
  have hm := (thT_strictMonoOn h0 h1).monotoneOn
  constructor
  · rw [← thT_one h0 h1]
    exact hm ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩ hw1
  · rw [← thT_three h0 h1]
    exact hm ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ hw3

include h0 h1 in
theorem thT_mem_open {w : ℝ} (hw1 : 1 < w) (hw3 : w < 3) :
    π / 4 < thT w₀ w ∧ thT w₀ w < 3 * π / 4 := by
  have hm := thT_strictMonoOn h0 h1
  constructor
  · rw [← thT_one h0 h1]
    exact hm ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩ hw1
  · rw [← thT_three h0 h1]
    exact hm ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ hw3

end Angle

/-! ### 輪郭 σ と半径 R -/

/-- χ₂ : u ≤ u₁ で 1、u ≥ u₂ で 0。 -/
def chi2 (w₀ u : ℝ) : ℝ := 1 - s₀ ((u - u1 w₀) / (u2 w₀ - u1 w₀))

/-- u の関数としての輪郭 (1 − χ₂(u)) sin 2u + χ₂(u)。 -/
def sigAux (w₀ u : ℝ) : ℝ := (1 - chi2 w₀ u) * sin (2 * u) + chi2 w₀ u

/-- σ(θ) = (1 − χ₂(u)) sin 2u + χ₂(u)、u = |θ − π/2|。 -/
def sigP (w₀ θ : ℝ) : ℝ := sigAux w₀ |θ - π / 2|

/-- 半径 R(θ) = √(σ(θ)/2)。 -/
def RP (w₀ θ : ℝ) : ℝ := √(sigP w₀ θ / 2)

section Profile

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
theorem chi2_of_le {u : ℝ} (hu : u ≤ u1 w₀) : chi2 w₀ u = 1 := by
  have hd : 0 < u2 w₀ - u1 w₀ := by linarith [u1_lt_u2 h0 h1]
  have : (u - u1 w₀) / (u2 w₀ - u1 w₀) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp [chi2, smoothTransition.zero_of_nonpos this]

include h0 h1 in
theorem chi2_of_ge {u : ℝ} (hu : u2 w₀ ≤ u) : chi2 w₀ u = 0 := by
  have hd : 0 < u2 w₀ - u1 w₀ := by linarith [u1_lt_u2 h0 h1]
  have : 1 ≤ (u - u1 w₀) / (u2 w₀ - u1 w₀) := by
    rw [le_div_iff₀ hd]; linarith
  simp [chi2, smoothTransition.one_of_one_le this]

theorem chi2_nonneg (w₀ u : ℝ) : 0 ≤ chi2 w₀ u := by
  have := smoothTransition.le_one ((u - u1 w₀) / (u2 w₀ - u1 w₀))
  simp only [chi2]; linarith

theorem chi2_le_one (w₀ u : ℝ) : chi2 w₀ u ≤ 1 := by
  have := smoothTransition.nonneg ((u - u1 w₀) / (u2 w₀ - u1 w₀))
  simp only [chi2]; linarith

theorem contDiff_chi2 (w₀ : ℝ) : ContDiff ℝ ∞ (chi2 w₀) := by
  unfold chi2
  refine contDiff_const.sub (Real.smoothTransition.contDiff.comp ?_)
  fun_prop

/-- σ(π − θ) = σ(θ)。 -/
theorem sigP_symm (w₀ θ : ℝ) : sigP w₀ (π - θ) = sigP w₀ θ := by
  have e : |π - θ - π / 2| = |θ - π / 2| := by
    rw [← abs_neg]; congr 1; ring
  simp only [sigP, e]

theorem contDiff_sigAux (w₀ : ℝ) : ContDiff ℝ ∞ (sigAux w₀) := by
  unfold sigAux
  have h := contDiff_chi2 w₀
  fun_prop

theorem sigP_le_one (w₀ θ : ℝ) : sigP w₀ θ ≤ 1 := by
  have h1 := sin_le_one (2 * |θ - π / 2|)
  have h2 := chi2_nonneg w₀ |θ - π / 2|
  have h3 := chi2_le_one w₀ |θ - π / 2|
  simp only [sigP, sigAux]
  nlinarith

include h0 h1 in
theorem sigP_of_far {θ : ℝ} (hθ : u2 w₀ ≤ |θ - π / 2|) : sigP w₀ θ = sin (2 * |θ - π / 2|) := by
  simp [sigP, sigAux, chi2_of_ge h0 h1 hθ]

include h0 h1 in
theorem sigP_of_near {θ : ℝ} (hθ : |θ - π / 2| ≤ u1 w₀) : sigP w₀ θ = 1 := by
  simp [sigP, sigAux, chi2_of_le h0 h1 hθ]

include h0 h1 in
/-- 下界：|θ − π/2| ≤ π/4 で σ ≥ sin 2u₁。 -/
theorem sigP_ge {θ : ℝ} (hθ : |θ - π / 2| ≤ π / 4) : sin (2 * u1 w₀) ≤ sigP w₀ θ := by
  set u := |θ - π / 2| with hu
  have hu0 : 0 ≤ u := abs_nonneg _
  have hs1 : sin (2 * u1 w₀) ≤ 1 := sin_le_one _
  by_cases hle : u ≤ u1 w₀
  · rw [sigP_of_near h0 h1 hle]; exact hs1
  · push Not at hle
    have hsin : sin (2 * u1 w₀) ≤ sin (2 * u) := by
      apply sin_le_sin_of_le_of_le_pi_div_two
      · linarith [u1_pos h0, pi_pos]
      · linarith
      · linarith
    have hs2 : sin (2 * u) ≤ 1 := sin_le_one _
    have hc0 := chi2_nonneg w₀ u
    have hc1 := chi2_le_one w₀ u
    simp only [sigP, sigAux, ← hu]
    nlinarith

include h0 h1 in
theorem sin_two_u1_pos : 0 < sin (2 * u1 w₀) :=
  sin_pos_of_pos_of_lt_pi (by linarith [u1_pos h0]) (by linarith [u1_lt h0 h1, pi_pos])

include h0 h1 in
theorem sigP_pos {θ : ℝ} (hθ : |θ - π / 2| ≤ π / 4) : 0 < sigP w₀ θ :=
  (sin_two_u1_pos h0 h1).trans_le (sigP_ge h0 h1 hθ)

include h0 h1 in
/-- σ は滑らかである（θ = π/2 の近傍では定数 1）。 -/
theorem contDiffAt_sigP (θ : ℝ) : ContDiffAt ℝ ∞ (sigP w₀) θ := by
  by_cases hθ : θ = π / 2
  · subst hθ
    have hopen : IsOpen {x : ℝ | |x - π / 2| < u1 w₀} :=
      isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
    have hmem : {x : ℝ | |x - π / 2| < u1 w₀} ∈ 𝓝 (π / 2) := by
      refine hopen.mem_nhds ?_
      simp [u1_pos h0]
    have e : sigP w₀ =ᶠ[𝓝 (π / 2)] fun _ => 1 := by
      filter_upwards [hmem] with x hx using sigP_of_near h0 h1 (le_of_lt hx)
    exact contDiffAt_const.congr_of_eventuallyEq e
  · rcases lt_or_gt_of_ne hθ with hlt | hgt
    · have e : sigP w₀ =ᶠ[𝓝 θ] fun x => sigAux w₀ (π / 2 - x) := by
        filter_upwards [Iio_mem_nhds hlt] with x hx
        simp only [sigP]
        rw [abs_sub_comm, abs_of_pos (by simpa using hx)]
      refine ContDiffAt.congr_of_eventuallyEq ?_ e
      exact (contDiff_sigAux w₀).contDiffAt.comp θ (contDiffAt_const.sub contDiffAt_id)
    · have e : sigP w₀ =ᶠ[𝓝 θ] fun x => sigAux w₀ (x - π / 2) := by
        filter_upwards [Ioi_mem_nhds hgt] with x hx
        simp only [sigP]
        rw [abs_of_pos (by simpa using hx)]
      refine ContDiffAt.congr_of_eventuallyEq ?_ e
      exact (contDiff_sigAux w₀).contDiffAt.comp θ (contDiffAt_id.sub contDiffAt_const)

include h0 h1 in
theorem RP_pos {θ : ℝ} (hθ : |θ - π / 2| ≤ π / 4) : 0 < RP w₀ θ :=
  Real.sqrt_pos.mpr (by have := sigP_pos h0 h1 hθ; positivity)

include h0 h1 in
theorem RP_sq {θ : ℝ} (hθ : |θ - π / 2| ≤ π / 4) : RP w₀ θ ^ 2 = sigP w₀ θ / 2 :=
  Real.sq_sqrt (by have := sigP_pos h0 h1 hθ; positivity)

theorem RP_symm (w₀ θ : ℝ) : RP w₀ (π - θ) = RP w₀ θ := by
  simp [RP, sigP_symm]

include h0 h1 in
theorem contDiffAt_RP {θ : ℝ} (hθ : |θ - π / 2| ≤ π / 4) : ContDiffAt ℝ ∞ (RP w₀) θ := by
  unfold RP
  refine ContDiffAt.sqrt ((contDiffAt_sigP h0 h1 θ).div_const 2) ?_
  have := sigP_pos h0 h1 hθ
  positivity

/-! ### 口での一致：θ = arctan(w²)、σ = sin 2θ のとき R cos θ = aa(w)、R sin θ = bb(w) -/

/-- ホーンの子午線の極座標の半径 r(w) = w/√(1 + w⁴)。 -/
def rG (w : ℝ) : ℝ := w / √(1 + w ^ 4)

theorem sqrt_one_add_pow_four_pos (w : ℝ) : 0 < √(1 + w ^ 4) :=
  Real.sqrt_pos.mpr (by positivity)

theorem rG_mul_cos (w : ℝ) : rG w * cos (fl w) = aa w := by
  have hm : √(1 + w ^ 4) * √(1 + w ^ 4) = 1 + w ^ 4 := Real.mul_self_sqrt (by positivity)
  have e : (w ^ 2) ^ 2 = w ^ 4 := by ring
  simp only [rG, fl, cos_arctan, aa, D, e]
  rw [div_mul_div_comm, hm, mul_one]

theorem rG_mul_sin (w : ℝ) : rG w * sin (fl w) = bb w := by
  have hm : √(1 + w ^ 4) * √(1 + w ^ 4) = 1 + w ^ 4 := Real.mul_self_sqrt (by positivity)
  have e : (w ^ 2) ^ 2 = w ^ 4 := by ring
  simp only [rG, fl, sin_arctan, bb, D, e]
  rw [div_mul_div_comm, hm]
  ring

theorem rG_sq (w : ℝ) : rG w ^ 2 = Rad (w ^ 2) := by
  have hs := sqrt_one_add_pow_four_pos w
  have hm : √(1 + w ^ 4) ^ 2 = 1 + w ^ 4 := Real.sq_sqrt (by positivity)
  simp only [rG, Rad]
  rw [div_pow, hm]
  congr 1
  ring

theorem rG_pos {w : ℝ} (hw : 0 < w) : 0 < rG w := div_pos hw (sqrt_one_add_pow_four_pos w)

theorem rG_eq_sqrt {w : ℝ} (hw : 0 ≤ w) : rG w = √(Rad (w ^ 2)) := by
  rw [← rG_sq, Real.sqrt_sq]
  exact div_nonneg hw (sqrt_one_add_pow_four_pos w).le

include h0 h1 in
/-- 口の角では σ = sin 2θ = 2 sin θ cos θ、したがって R = r。 -/
theorem RP_fl_eq_rG {w : ℝ} (hw1 : 1 ≤ w) (hwa : w ≤ wa w₀) : RP w₀ (fl w) = rG w := by
  have hw0 : 0 < w := by linarith
  have hlt : fl w < π / 2 - u2 w₀ := by
    rw [← arctan_w1_sq h0 h1]
    exact fl_strictMonoOn hw0.le (by linarith [wa_lt_w1 h0 h1] : (0 : ℝ) ≤ w1 w₀)
      (by linarith [wa_lt_w1 h0 h1])
  have habs : |fl w - π / 2| = π / 2 - fl w := by
    rw [abs_sub_comm, abs_of_pos (by linarith [fl_lt_pi_div_two w])]
  have hfar : u2 w₀ ≤ |fl w - π / 2| := by rw [habs]; linarith
  have hsig : sigP w₀ (fl w) = 2 * sin (fl w) * cos (fl w) := by
    rw [sigP_of_far h0 h1 hfar, habs]
    have e : 2 * (π / 2 - fl w) = π - 2 * fl w := by ring
    rw [e, sin_pi_sub, sin_two_mul]
  have hprod : sin (fl w) * cos (fl w) = w ^ 2 / (1 + w ^ 4) := by
    have hm : √(1 + w ^ 4) * √(1 + w ^ 4) = 1 + w ^ 4 := Real.mul_self_sqrt (by positivity)
    have e : (w ^ 2) ^ 2 = w ^ 4 := by ring
    simp only [fl, sin_arctan, cos_arctan, e]
    rw [div_mul_div_comm, hm, mul_one]
  simp only [RP]
  rw [hsig]
  have e2 : 2 * sin (fl w) * cos (fl w) / 2 = w ^ 2 / (1 + w ^ 4) := by
    rw [mul_assoc, hprod]; ring
  rw [e2, rG_eq_sqrt hw0.le]
  congr 1
  simp only [Rad]
  congr 1
  ring

end Profile

end Zeno.Model
