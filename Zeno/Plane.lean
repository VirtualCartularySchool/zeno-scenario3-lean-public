/-
# Zeno.Plane : 定理 C の平面と傘（Smale–Hirsch を使う手前まで）

g(y) = (χ(τ) τ√τ/(1 + τ²), y/(1 + τ²))、τ = |y|²。τ ≥ ½ で g(y) = G(1/|y|, arg y)。
y → ∞ で g(y) → ℘ である。

傘 U(φ) = Λ(φ)∘g は U(0) = g、U(π) = −g を結ぶ素朴な裏返しで、
φ = π/2、τ² = ⅓ の円の上にだけ折り目を持つ（C1）。℘ の近くでは正則である。

形式解の単射性（`frame_inj`）は、Smale–Hirsch を適用するための入力である。
-/
import Zeno.Regular
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### 平面 -/

/-- τ(y) = |y|² -/
def tau (y : ℝ × ℝ) : ℝ := y.1 ^ 2 + y.2 ^ 2

/-- h(τ) = 1/(1 + τ²) -/
def hC (τ : ℝ) : ℝ := 1 / (1 + τ ^ 2)

/-- h′(τ) -/
def hP (τ : ℝ) : ℝ := -(2 * τ) / (1 + τ ^ 2) ^ 2

/-- 中央を平らにする階段：τ ≤ ¼ で 0、τ ≥ ½ で 1。 -/
def chiC (τ : ℝ) : ℝ := s₀ (4 * τ - 1)

/-- 第 1 成分 q(τ) -/
def qC (τ : ℝ) : ℝ := chiC τ * (τ * √τ) / (1 + τ ^ 2)

/-- **キャップつき平面 g**。 -/
def planeG (y : ℝ × ℝ) : V3 := (qC (tau y), hC (tau y) * y.1, hC (tau y) * y.2)

theorem den_pos' (τ : ℝ) : 0 < 1 + τ ^ 2 := by positivity

theorem tau_nonneg (y : ℝ × ℝ) : 0 ≤ tau y := by
  unfold tau; positivity

theorem hC_pos (τ : ℝ) : 0 < hC τ := by
  unfold hC; positivity

theorem contDiff_tau : ContDiff ℝ ∞ tau := by
  unfold tau; fun_prop

theorem contDiff_hC : ContDiff ℝ ∞ hC :=
  contDiff_const.div (contDiff_const.add (contDiff_id.pow 2)) fun τ => (den_pos' τ).ne'

theorem contDiff_hP : ContDiff ℝ ∞ hP :=
  (contDiff_const.mul contDiff_id).neg.div ((contDiff_const.add (contDiff_id.pow 2)).pow 2)
    fun τ => (pow_pos (den_pos' τ) 2).ne'

theorem hasDerivAt_hC (τ : ℝ) : HasDerivAt hC (hP τ) τ := by
  have h1 : HasDerivAt (fun τ : ℝ => 1 + τ ^ 2) (2 * τ) τ := by
    simpa using (hasDerivAt_pow 2 τ).const_add 1
  have h2 := (hasDerivAt_const τ (1 : ℝ)).div h1 (den_pos' τ).ne'
  refine h2.congr_deriv ?_
  simp only [hP]
  ring

theorem chiC_of_le {τ : ℝ} (h : τ ≤ 1 / 4) : chiC τ = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

theorem chiC_of_ge {τ : ℝ} (h : 1 / 2 ≤ τ) : chiC τ = 1 :=
  smoothTransition.one_of_one_le (by linarith)

theorem contDiff_chiC : ContDiff ℝ ∞ chiC := by
  unfold chiC
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem contDiff_qC : ContDiff ℝ ∞ qC := by
  rw [contDiff_iff_contDiffAt]
  intro τ₀
  by_cases h : τ₀ < 1 / 4
  · have e : qC =ᶠ[𝓝 τ₀] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with y hy
      simp [qC, chiC_of_le (le_of_lt hy)]
    exact contDiffAt_const.congr_of_eventuallyEq e
  · have hpos : τ₀ ≠ 0 := by
      push Not at h
      intro h0
      linarith
    unfold qC
    refine ContDiffAt.div ?_ (contDiffAt_const.add (contDiffAt_id.pow 2)) (den_pos' τ₀).ne'
    exact contDiff_chiC.contDiffAt.mul (contDiffAt_id.mul (contDiffAt_id.sqrt hpos))

/-- q′ -/
def dq (τ : ℝ) : ℝ := deriv qC τ

theorem contDiff_dq : ContDiff ℝ ∞ dq :=
  (contDiff_infty_iff_deriv.mp contDiff_qC).2

theorem hasDerivAt_qC (τ : ℝ) : HasDerivAt qC (dq τ) τ :=
  (contDiff_qC.differentiable (by simp) τ).hasDerivAt

/-- τ > ½ で q′ の式。 -/
theorem dq_of {τ : ℝ} (h : 1 / 2 < τ) : dq τ = √τ * (3 - τ ^ 2) / (2 * (1 + τ ^ 2) ^ 2) := by
  have hτ : 0 < τ := by linarith
  have hr : 0 < √τ := Real.sqrt_pos.mpr hτ
  have hrs : √τ ^ 2 = τ := Real.sq_sqrt hτ.le
  have h1 : HasDerivAt (fun τ : ℝ => 1 + τ ^ 2) (2 * τ) τ := by
    simpa using (hasDerivAt_pow 2 τ).const_add 1
  have h2 : HasDerivAt (fun τ : ℝ => τ * √τ) (1 * √τ + τ * (1 / (2 * √τ))) τ :=
    (hasDerivAt_id' τ).mul (Real.hasDerivAt_sqrt hτ.ne')
  have h3 := h2.div h1 (den_pos' τ).ne'
  have e : qC =ᶠ[𝓝 τ] fun τ => τ * √τ / (1 + τ ^ 2) := by
    filter_upwards [Ioi_mem_nhds h] with y hy
    have : chiC y = 1 := chiC_of_ge (le_of_lt hy)
    simp [qC, this]
  have h4 := (h3.congr_of_eventuallyEq e).deriv
  have hd : dq τ = _ := h4
  rw [hd]
  have hτ' : τ = √τ ^ 2 := hrs.symm
  generalize √τ = x at *
  subst hτ'
  have hD := den_pos' (x ^ 2)
  field_simp
  ring

/-- S(τ) = h + 2τh′ = (1 − 3τ²)/(1 + τ²)² -/
def SS (τ : ℝ) : ℝ := hC τ + 2 * τ * hP τ

theorem SS_eq (τ : ℝ) : SS τ = (1 - 3 * τ ^ 2) / (1 + τ ^ 2) ^ 2 := by
  have := den_pos' τ
  simp only [SS, hC, hP]
  field_simp
  ring

theorem contDiff_SS : ContDiff ℝ ∞ SS :=
  contDiff_hC.add ((contDiff_const.mul contDiff_id).mul contDiff_hP)

/-! ### 平面の微分 -/

/-- ∂g/∂y₁ -/
def D1 (y : ℝ × ℝ) : V3 :=
  (2 * dq (tau y) * y.1, hC (tau y) + 2 * hP (tau y) * y.1 * y.1, 2 * hP (tau y) * y.1 * y.2)

/-- ∂g/∂y₂ -/
def D2 (y : ℝ × ℝ) : V3 :=
  (2 * dq (tau y) * y.2, 2 * hP (tau y) * y.2 * y.1, hC (tau y) + 2 * hP (tau y) * y.2 * y.2)

/-- 半径方向の内積 a = ⟨y, ξ⟩ -/
def ra (y ξ : ℝ × ℝ) : ℝ := y.1 * ξ.1 + y.2 * ξ.2

/-- 接線方向の内積 b = ⟨iy, ξ⟩ -/
def rb (y ξ : ℝ × ℝ) : ℝ := -(y.2 * ξ.1) + y.1 * ξ.2

/-- dg_y(ξ) -/
def planeD (y ξ : ℝ × ℝ) : V3 :=
  (2 * dq (tau y) * ra y ξ,
   hC (tau y) * ξ.1 + 2 * hP (tau y) * ra y ξ * y.1,
   hC (tau y) * ξ.2 + 2 * hP (tau y) * ra y ξ * y.2)

theorem contDiff_planeG : ContDiff ℝ ∞ planeG := by
  have h1 : ContDiff ℝ ∞ (fun y => qC (tau y)) := contDiff_qC.comp contDiff_tau
  have h2 : ContDiff ℝ ∞ (fun y => hC (tau y)) := contDiff_hC.comp contDiff_tau
  unfold planeG
  fun_prop

theorem hasDerivAt_tau_1 (y₁ y₂ : ℝ) : HasDerivAt (fun x => tau (x, y₂)) (2 * y₁) y₁ := by
  have := (hasDerivAt_pow 2 y₁).add_const (y₂ ^ 2)
  simpa [tau] using this

theorem hasDerivAt_tau_2 (y₁ y₂ : ℝ) : HasDerivAt (fun x => tau (y₁, x)) (2 * y₂) y₂ := by
  have := (hasDerivAt_pow 2 y₂).const_add (y₁ ^ 2)
  simpa [tau] using this

theorem hasDerivAt_planeG_1 (y₁ y₂ : ℝ) :
    HasDerivAt (fun x => planeG (x, y₂)) (D1 (y₁, y₂)) y₁ := by
  have ht := hasDerivAt_tau_1 y₁ y₂
  have hq := HasDerivAt.comp (h₂ := qC) (h := fun x => tau (x, y₂)) y₁
    (hasDerivAt_qC (tau (y₁, y₂))) ht
  have hh := HasDerivAt.comp (h₂ := hC) (h := fun x => tau (x, y₂)) y₁
    (hasDerivAt_hC (tau (y₁, y₂))) ht
  have h2 := hh.mul (hasDerivAt_id' y₁)
  have h3 := hh.mul_const y₂
  refine (hq.prodMk (h2.prodMk h3)).congr_deriv ?_
  simp only [D1, Function.comp]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem hasDerivAt_planeG_2 (y₁ y₂ : ℝ) :
    HasDerivAt (fun x => planeG (y₁, x)) (D2 (y₁, y₂)) y₂ := by
  have ht := hasDerivAt_tau_2 y₁ y₂
  have hq := HasDerivAt.comp (h₂ := qC) (h := fun x => tau (y₁, x)) y₂
    (hasDerivAt_qC (tau (y₁, y₂))) ht
  have hh := HasDerivAt.comp (h₂ := hC) (h := fun x => tau (y₁, x)) y₂
    (hasDerivAt_hC (tau (y₁, y₂))) ht
  have h2 := hh.mul_const y₁
  have h3 := hh.mul (hasDerivAt_id' y₂)
  refine (hq.prodMk (h2.prodMk h3)).congr_deriv ?_
  simp only [D2, Function.comp]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem planeD_eq (y ξ : ℝ × ℝ) : ξ.1 • D1 y + ξ.2 • D2 y = planeD y ξ := by
  simp only [D1, D2, planeD, ra]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] <;> ring

theorem fderiv_planeG (y ξ : ℝ × ℝ) : fderiv ℝ planeG y ξ = planeD y ξ := by
  obtain ⟨y₁, y₂⟩ := y
  have hd : DifferentiableAt ℝ planeG (y₁, y₂) :=
    contDiff_planeG.differentiable (by simp) _
  rw [fderiv_apply_of_partials hd (hasDerivAt_planeG_1 y₁ y₂) (hasDerivAt_planeG_2 y₁ y₂),
    planeD_eq]

/-- 法線の式 n₀ -/
def n0 (y : ℝ × ℝ) : V3 :=
  (SS (tau y), -(2 * dq (tau y) * y.1), -(2 * dq (tau y) * y.2))

/-- ∂₁g × ∂₂g = h n₀ -/
theorem cross_D1_D2 (y : ℝ × ℝ) : cross (D1 y) (D2 y) = hC (tau y) • n0 y := by
  simp only [cross, D1, D2, n0, SS]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.smul_mk, smul_eq_mul, tau]; ring
  · simp only [Prod.smul_mk, smul_eq_mul]; ring
  · simp only [Prod.smul_mk, smul_eq_mul]; ring

/-- |n₀|² -/
def WW (y : ℝ × ℝ) : ℝ := SS (tau y) ^ 2 + 4 * dq (tau y) ^ 2 * tau y

theorem dot_n0_n0 (y : ℝ × ℝ) : dot (n0 y) (n0 y) = WW y := by
  simp only [dot, n0, WW, tau]; ring

theorem dot_n0_planeD (y ξ : ℝ × ℝ) : dot (n0 y) (planeD y ξ) = 0 := by
  simp only [dot, n0, planeD, SS, ra, tau]; ring

/-- S = 0 なら τ² = ⅓ で、q′ ≠ 0。 -/
theorem tau_sq_of_SS {τ : ℝ} (h : SS τ = 0) : τ ^ 2 = 1 / 3 := by
  rw [SS_eq] at h
  rcases div_eq_zero_iff.mp h with h1 | h1
  · linarith
  · exact absurd h1 (pow_pos (den_pos' τ) 2).ne'

theorem half_lt_of_sq {τ : ℝ} (h0 : 0 ≤ τ) (h : 1 / 3 ≤ τ ^ 2) : 1 / 2 < τ := by
  nlinarith

theorem dq_pos_of_crease {τ : ℝ} (h0 : 0 ≤ τ) (h : τ ^ 2 = 1 / 3) : 0 < dq τ := by
  have hh := half_lt_of_sq h0 h.ge
  rw [dq_of hh]
  have hr : 0 < √τ := Real.sqrt_pos.mpr (by linarith)
  have h3 : 0 < 3 - τ ^ 2 := by rw [h]; norm_num
  have := den_pos' τ
  positivity

theorem WW_pos (y : ℝ × ℝ) : 0 < WW y := by
  have ht := tau_nonneg y
  by_cases hS : SS (tau y) = 0
  · have h1 := tau_sq_of_SS hS
    have h2 := dq_pos_of_crease ht h1
    have h3 := half_lt_of_sq ht h1.ge
    simp only [WW, hS]
    have : 0 < tau y := by linarith
    positivity
  · have h1 : 0 < SS (tau y) ^ 2 := by positivity
    have h2 : 0 ≤ 4 * dq (tau y) ^ 2 * tau y := by positivity
    simp only [WW]
    linarith

/-- 単位法線 -/
def nh (y : ℝ × ℝ) : V3 := (1 / √(WW y)) • n0 y

theorem sqrt_WW_pos (y : ℝ × ℝ) : 0 < √(WW y) := Real.sqrt_pos.mpr (WW_pos y)

theorem contDiff_WW : ContDiff ℝ ∞ WW := by
  have h1 : ContDiff ℝ ∞ (fun y => SS (tau y)) := contDiff_SS.comp contDiff_tau
  have h2 : ContDiff ℝ ∞ (fun y => dq (tau y)) := contDiff_dq.comp contDiff_tau
  have h3 := contDiff_tau
  unfold WW
  fun_prop

theorem contDiff_n0 : ContDiff ℝ ∞ n0 := by
  have h1 : ContDiff ℝ ∞ (fun y => SS (tau y)) := contDiff_SS.comp contDiff_tau
  have h2 : ContDiff ℝ ∞ (fun y => dq (tau y)) := contDiff_dq.comp contDiff_tau
  unfold n0
  fun_prop

theorem contDiff_nh : ContDiff ℝ ∞ nh := by
  have h1 : ContDiff ℝ ∞ (fun y => √(WW y)) :=
    contDiff_WW.sqrt fun y => (WW_pos y).ne'
  have h2 : ContDiff ℝ ∞ (fun y => 1 / √(WW y)) :=
    contDiff_const.div h1 fun y => (sqrt_WW_pos y).ne'
  unfold nh
  exact h2.smul contDiff_n0

theorem dot_nh_nh (y : ℝ × ℝ) : dot (nh y) (nh y) = 1 := by
  have h := dot_n0_n0 y
  have hs := sqrt_WW_pos y
  have hsq : √(WW y) ^ 2 = WW y := Real.sq_sqrt (WW_pos y).le
  simp only [nh, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
  field_simp
  rw [hsq, ← h]
  ring

theorem dot_nh_planeD (y ξ : ℝ × ℝ) : dot (nh y) (planeD y ξ) = 0 := by
  have h := dot_n0_planeD y ξ
  simp only [nh, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h ⊢
  linear_combination (1 / √(WW y)) * h

/-! ### 半径方向と接線方向の分解 -/

/-- ⟨ȳ, ζ⟩ の実部 -/
def rr (y : ℝ × ℝ) (u : V3) : ℝ := y.1 * u.2.1 + y.2 * u.2.2

/-- ⟨ȳ, ζ⟩ の虚部 -/
def ii (y : ℝ × ℝ) (u : V3) : ℝ := -(y.2 * u.2.1) + y.1 * u.2.2

theorem rr_planeD (y ξ : ℝ × ℝ) : rr y (planeD y ξ) = ra y ξ * SS (tau y) := by
  simp only [rr, planeD, SS, ra, tau]; ring

theorem ii_planeD (y ξ : ℝ × ℝ) : ii y (planeD y ξ) = hC (tau y) * rb y ξ := by
  simp only [ii, planeD, ra, rb]; ring

theorem fst_planeD (y ξ : ℝ × ℝ) : (planeD y ξ).1 = 2 * dq (tau y) * ra y ξ := rfl

theorem xi_of_ra {y ξ : ℝ × ℝ} (ha : ra y ξ = 0) (h2 : (planeD y ξ).2.1 = 0)
    (h3 : (planeD y ξ).2.2 = 0) : ξ = 0 := by
  simp only [planeD, ha, mul_zero, zero_mul, add_zero] at h2 h3
  have h := (hC_pos (tau y)).ne'
  exact Prod.ext ((mul_eq_zero.mp h2).resolve_left h) ((mul_eq_zero.mp h3).resolve_left h)

/-- u₁ = 0 かつ ζ の分解が 0 なら ξ = 0。S = 0 でも q′ ≠ 0 なので。 -/
theorem ra_eq_zero {y ξ : ℝ × ℝ} (h1 : dq (tau y) * ra y ξ = 0) (hS : ra y ξ * SS (tau y) = 0) :
    ra y ξ = 0 := by
  by_contra hne
  have hS0 : SS (tau y) = 0 := (mul_eq_zero.mp hS).resolve_left hne
  have hq := dq_pos_of_crease (tau_nonneg y) (tau_sq_of_SS hS0)
  exact (mul_ne_zero hq.ne' hne) h1

/-- **g ははめ込みである**（座標の形）。 -/
theorem planeD_inj {y ξ : ℝ × ℝ} (h : planeD y ξ = 0) : ξ = 0 := by
  have h1 : (planeD y ξ).1 = 0 := congrArg Prod.fst h
  have h2 : (planeD y ξ).2.1 = 0 := congrArg (fun z : V3 => z.2.1) h
  have h3 : (planeD y ξ).2.2 = 0 := congrArg (fun z : V3 => z.2.2) h
  have e1 : rr y (planeD y ξ) = 0 := by simp only [rr, h2, h3, mul_zero, add_zero]
  rw [rr_planeD] at e1
  have ha : ra y ξ = 0 := by
    refine ra_eq_zero ?_ e1
    rw [fst_planeD] at h1
    linarith
  exact xi_of_ra ha h2 h3

theorem planeG_immersion (y : ℝ × ℝ) : Function.Injective (fderiv ℝ planeG y) := by
  refine (injective_iff_map_eq_zero _).mpr fun ξ hξ => ?_
  rw [fderiv_planeG] at hξ
  exact planeD_inj hξ

/-! ### 傘 Λ と回転 -/

/-- Λ(φ)(q₁, ζ) = (cos φ · q₁, e^{iφ} ζ) -/
def Lam (φ : ℝ) (q : V3) : V3 :=
  (cos φ * q.1, cos φ * q.2.1 - sin φ * q.2.2, sin φ * q.2.1 + cos φ * q.2.2)

theorem Lam_zero (q : V3) : Lam 0 q = q := by
  simp [Lam]

theorem Lam_pi (q : V3) : Lam π q = -q := by
  simp only [Lam, cos_pi, sin_pi]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

theorem rr_Lam (φ : ℝ) (y : ℝ × ℝ) (u : V3) :
    rr y (Lam φ u) = cos φ * rr y u - sin φ * ii y u := by
  simp only [rr, ii, Lam]; ring

theorem ii_Lam (φ : ℝ) (y : ℝ × ℝ) (u : V3) :
    ii y (Lam φ u) = sin φ * rr y u + cos φ * ii y u := by
  simp only [rr, ii, Lam]; ring

theorem nsq_Lam_le (φ : ℝ) (q : V3) : nsq (Lam φ q) ≤ nsq q := by
  have h := sin_sq_add_cos_sq φ
  have e : nsq (Lam φ q) = cos φ ^ 2 * q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 := by
    simp only [nsq, dot, Lam]
    linear_combination (q.2.1 ^ 2 + q.2.2 ^ 2) * h
  have e2 : nsq q = q.1 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 := by
    simp only [nsq, dot]; ring
  rw [e, e2]
  have : cos φ ^ 2 ≤ 1 := by nlinarith [sq_nonneg (sin φ)]
  nlinarith [sq_nonneg q.1]

/-- Rodrigues の回転（n のまわりに −φ）。 -/
def Rod (φ : ℝ) (n u : V3) : V3 :=
  cos φ • u - sin φ • cross n u + ((1 - cos φ) * dot n u) • n

theorem Rod_zero (n u : V3) : Rod 0 n u = u := by
  simp [Rod]

theorem Rod_pi {n u : V3} (h : dot n u = 0) : Rod π n u = -u := by
  simp [Rod, h]

theorem Rod_of_perp (φ : ℝ) {n u : V3} (h : dot n u = 0) :
    Rod φ n u = cos φ • u - sin φ • cross n u := by
  simp [Rod, h]

/-- 接平面の上で Rod は等長である。 -/
theorem dot_Rod_self (φ : ℝ) {n u : V3} (hn : dot n n = 1) (hu : dot n u = 0) :
    dot (Rod φ n u) (Rod φ n u) = dot u u := by
  rw [Rod_of_perp φ hu]
  have h3 := sin_sq_add_cos_sq φ
  simp only [dot, cross, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    at hn hu ⊢
  linear_combination (u.1 * u.1 + u.2.1 * u.2.1 + u.2.2 * u.2.2) * h3 +
    (sin φ) ^ 2 * (u.1 * u.1 + u.2.1 * u.2.1 + u.2.2 * u.2.2) * hn -
    (sin φ) ^ 2 * (n.1 * u.1 + n.2.1 * u.2.1 + n.2.2 * u.2.2) * hu

theorem rr_cross (y : ℝ × ℝ) (u : V3) :
    rr y (cross (nh y) u) = -((SS (tau y) / √(WW y)) * ii y u) := by
  have hs := (sqrt_WW_pos y).ne'
  simp only [rr, ii, cross, nh, n0, Prod.smul_mk, smul_eq_mul]
  field_simp
  ring

theorem ii_cross (y : ℝ × ℝ) (u : V3) :
    ii y (cross (nh y) u) =
      (SS (tau y) / √(WW y)) * rr y u + (2 * dq (tau y) / √(WW y)) * tau y * u.1 := by
  have hs := (sqrt_WW_pos y).ne'
  simp only [rr, ii, cross, nh, n0, Prod.smul_mk, smul_eq_mul, tau]
  field_simp
  ring

/-- 混合の核：S < 0 なら行列式は負である。 -/
theorem blend_core {R Rp t c s χ : ℝ} (hR : 0 < R) (hRp : Rp < 0) (ht : 0 < t)
    (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    R * (c ^ 2 * Rp - s ^ 2 * (((1 - χ) * Rp - χ * t) * (-(1 - χ) + χ * Rp / t))) < 0 := by
  have hPlt : (1 - χ) * Rp - χ * t < 0 := by
    rcases eq_or_lt_of_le hχ0 with h | h
    · rw [← h]; simpa using hRp
    · nlinarith
  have hB : -(1 - χ) + χ * Rp / t < 0 := by
    have h1 : χ * Rp / t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by nlinarith) ht.le
    rcases eq_or_lt_of_le hχ1 with h | h
    · have hχ : χ = 1 := h
      subst hχ
      have : (1 : ℝ) * Rp / t < 0 := by
        simpa using div_neg_of_neg_of_pos hRp ht
      linarith
    · linarith
  have hprod : 0 < ((1 - χ) * Rp - χ * t) * (-(1 - χ) + χ * Rp / t) := mul_pos_of_neg_of_neg hPlt hB
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have key : c ^ 2 * Rp - s ^ 2 * (((1 - χ) * Rp - χ * t) * (-(1 - χ) + χ * Rp / t)) < 0 := by
    have hm := min_le_left (-Rp) (((1 - χ) * Rp - χ * t) * (-(1 - χ) + χ * Rp / t))
    have hm2 := min_le_right (-Rp) (((1 - χ) * Rp - χ * t) * (-(1 - χ) + χ * Rp / t))
    have hmpos : 0 < min (-Rp) (((1 - χ) * Rp - χ * t) * (-(1 - χ) + χ * Rp / t)) :=
      lt_min (by linarith) hprod
    nlinarith [mul_le_mul_of_nonneg_left hm hc2, mul_le_mul_of_nonneg_left hm2 hs2]
  exact mul_neg_of_pos_of_neg hR key

/-- 形式解の微分（倍率を除く）。 -/
def blendM (χ φ : ℝ) (n u : V3) : V3 := (1 - χ) • Lam φ u + χ • Rod φ n u

theorem rr_add (y : ℝ × ℝ) (a b : V3) : rr y (a + b) = rr y a + rr y b := by
  simp only [rr, Prod.fst_add, Prod.snd_add]; ring

theorem rr_smul (y : ℝ × ℝ) (k : ℝ) (a : V3) : rr y (k • a) = k * rr y a := by
  simp only [rr, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem rr_sub (y : ℝ × ℝ) (a b : V3) : rr y (a - b) = rr y a - rr y b := by
  simp only [rr, Prod.fst_sub, Prod.snd_sub]; ring

theorem ii_add (y : ℝ × ℝ) (a b : V3) : ii y (a + b) = ii y a + ii y b := by
  simp only [ii, Prod.fst_add, Prod.snd_add]; ring

theorem ii_smul (y : ℝ × ℝ) (k : ℝ) (a : V3) : ii y (k • a) = k * ii y a := by
  simp only [ii, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem ii_sub (y : ℝ × ℝ) (a b : V3) : ii y (a - b) = ii y a - ii y b := by
  simp only [ii, Prod.fst_sub, Prod.snd_sub]; ring

/-- **形式解の単射性**：S ≥ 0 のところで χ = 1 なら、混合は dg の像の上で単射である。 -/
theorem frame_inj {y ξ : ℝ × ℝ} {χ : ℝ} (φ : ℝ) (hχ0 : 0 ≤ χ) (hχ1 : χ ≤ 1)
    (hχS : 0 ≤ SS (tau y) → χ = 1) (h : blendM χ φ (nh y) (planeD y ξ) = 0) : ξ = 0 := by
  set u := planeD y ξ with hu
  have hperp := dot_nh_planeD y ξ
  rw [← hu] at hperp
  by_cases hS : 0 ≤ SS (tau y)
  · -- 等長
    have hχ := hχS hS
    subst hχ
    have h0 : Rod φ (nh y) u = 0 := by simpa [blendM] using h
    have h1 := dot_Rod_self φ (dot_nh_nh y) hperp
    rw [h0] at h1
    have h2 : dot u u = 0 := by
      rw [← h1]
      simp [dot]
    have h3 : u = wp := by
      by_contra hne
      exact dot_self_ne hne h2
    exact planeD_inj h3
  · -- 混合の行列式
    push Not at hS
    set S := SS (tau y) with hSdef
    set q := dq (tau y) with hq
    set hh := hC (tau y) with hhdef
    set t := √(WW y) with ht
    have htp : 0 < t := sqrt_WW_pos y
    have hhp : 0 < hh := hC_pos _
    have hτ0 : tau y ≠ 0 := by
      intro h0
      have : S = 1 := by
        simp only [hSdef, h0, SS_eq]; norm_num
      linarith
    set c := cos φ with hc
    set s := sin φ with hs
    set a := ra y ξ with ha
    set b := rb y ξ with hb
    have hru : rr y u = a * S := rr_planeD y ξ
    have hiu : ii y u = hh * b := ii_planeD y ξ
    have hfu : u.1 = 2 * q * a := fst_planeD y ξ
    have hW : S ^ 2 + 4 * q ^ 2 * tau y = t ^ 2 := by
      rw [ht, Real.sq_sqrt (WW_pos y).le]
      rfl
    have e1 : rr y (blendM χ φ (nh y) u) = 0 := by rw [h]; simp [rr]
    have e2 : ii y (blendM χ φ (nh y) u) = 0 := by rw [h]; simp [ii]
    simp only [blendM, Rod_of_perp φ hperp, rr_add, rr_smul, rr_sub, rr_Lam, rr_cross,
      ii_add, ii_smul, ii_sub, ii_Lam, ii_cross] at e1 e2
    simp only [← hc, ← hs, ← hSdef, ← hq, ← ht, hru, hiu, hfu] at e1 e2
    have E1 : c * S * a + s * hh * (-(1 - χ) + χ * S / t) * b = 0 := by
      rw [← e1]
      field_simp
      ring
    have E2 : s * ((1 - χ) * S - χ * t) * a + c * hh * b = 0 := by
      have e3 : (S / t) * (a * S) + (2 * q / t) * tau y * (2 * q * a) = a * t := by
        have : (S / t) * (a * S) + (2 * q / t) * tau y * (2 * q * a) =
            a * (S ^ 2 + 4 * q ^ 2 * tau y) / t := by
          field_simp
          ring
        rw [this, hW]
        field_simp
      linear_combination e2 + (χ * s) * e3
    have hcs : c ^ 2 + s ^ 2 = 1 := by
      have := sin_sq_add_cos_sq φ
      rw [hc, hs]
      linarith
    have hdet := blend_core hhp hS htp hχ0 hχ1 hcs
    set P := (1 - χ) * S - χ * t with hP
    set B₂ := -(1 - χ) + χ * S / t with hB₂
    have hne : hh * (c ^ 2 * S - s ^ 2 * (P * B₂)) ≠ 0 := hdet.ne
    have ha0 : a = 0 := by
      have : a * (hh * (c ^ 2 * S - s ^ 2 * (P * B₂))) = 0 := by
        linear_combination (c * hh) * E1 - (s * hh * B₂) * E2
      exact (mul_eq_zero.mp this).resolve_right hne
    have hb0 : b = 0 := by
      have : b * (hh * (c ^ 2 * S - s ^ 2 * (P * B₂))) = 0 := by
        linear_combination (c * S) * E2 - (s * P) * E1
      exact (mul_eq_zero.mp this).resolve_right hne
    have e4 : tau y * ξ.1 = y.1 * a - y.2 * b := by
      simp only [ha, hb, ra, rb, tau]; ring
    have e5 : tau y * ξ.2 = y.2 * a + y.1 * b := by
      simp only [ha, hb, ra, rb, tau]; ring
    rw [ha0, hb0] at e4 e5
    refine Prod.ext ?_ ?_
    · have : tau y * ξ.1 = 0 := by rw [e4]; ring
      exact (mul_eq_zero.mp this).resolve_left hτ0
    · have : tau y * ξ.2 = 0 := by rw [e5]; ring
      exact (mul_eq_zero.mp this).resolve_left hτ0

/-! ### 傘の折り目（C1） -/

/-- Λ(φ) は φ を固定すると線形である。 -/
def LamL (φ : ℝ) : V3 →L[ℝ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := Lam φ
      map_add' := fun a b => by
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Lam, Prod.fst_add, Prod.snd_add] <;> ring
      map_smul' := fun k a => by
        refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
          simp only [Lam, RingHom.id_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring }

@[simp] theorem LamL_apply (φ : ℝ) (q : V3) : LamL φ q = Lam φ q := rfl

theorem fderiv_umbrella (φ : ℝ) (y ξ : ℝ × ℝ) :
    fderiv ℝ (fun y => Lam φ (planeG y)) y ξ = Lam φ (planeD y ξ) := by
  have hd : HasFDerivAt planeG (fderiv ℝ planeG y) y :=
    (contDiff_planeG.differentiable (by simp) y).hasFDerivAt
  have h := (LamL φ).hasFDerivAt.comp y hd
  have e : (⇑(LamL φ) ∘ planeG) = fun y => Lam φ (planeG y) := rfl
  rw [e] at h
  rw [h.fderiv]
  simp [fderiv_planeG]

/-- **C1（折り目）**：傘 U(φ) がはめ込みでないのは、cos φ = 0 かつ τ² = ⅓ の円の上だけである。 -/
theorem umbrella_crease (φ : ℝ) (y : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (fun y => Lam φ (planeG y)) y) ↔
      ¬ (cos φ = 0 ∧ tau y ^ 2 = 1 / 3) := by
  constructor
  · rintro hinj ⟨hc, ht⟩
    have hS : SS (tau y) = 0 := by
      rw [SS_eq, ht]; norm_num
    have hτ : tau y ≠ 0 := by
      intro h0
      rw [h0] at ht
      norm_num at ht
    have hy : y ≠ 0 := by
      rintro rfl
      exact hτ (by simp [tau])
    apply hy
    apply hinj
    rw [fderiv_umbrella, map_zero]
    have hS' : hC (tau y) + 2 * tau y * hP (tau y) = 0 := hS
    simp only [Lam, planeD, ra, hc]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp
    · simp only [zero_mul, Prod.fst_zero, Prod.snd_zero, zero_sub]
      have : hC (tau y) * y.1 + 2 * hP (tau y) * (y.1 * y.1 + y.2 * y.2) * y.1 = 0 := by
        have e : y.1 * y.1 + y.2 * y.2 = tau y := by simp only [tau]; ring
        rw [e]
        linear_combination y.1 * hS'
      have h2 : hC (tau y) * y.2 + 2 * hP (tau y) * (y.1 * y.1 + y.2 * y.2) * y.2 = 0 := by
        have e : y.1 * y.1 + y.2 * y.2 = tau y := by simp only [tau]; ring
        rw [e]
        linear_combination y.2 * hS'
      rw [h2]; simp
    · simp only [zero_mul, Prod.snd_zero, add_zero]
      have : hC (tau y) * y.1 + 2 * hP (tau y) * (y.1 * y.1 + y.2 * y.2) * y.1 = 0 := by
        have e : y.1 * y.1 + y.2 * y.2 = tau y := by simp only [tau]; ring
        rw [e]
        linear_combination y.1 * hS'
      rw [this]; simp
  · intro hno
    refine (injective_iff_map_eq_zero _).mpr fun ξ hξ => ?_
    rw [fderiv_umbrella] at hξ
    have h1 : (Lam φ (planeD y ξ)).1 = 0 := congrArg Prod.fst hξ
    have h2 : (Lam φ (planeD y ξ)).2.1 = 0 := congrArg (fun z : V3 => z.2.1) hξ
    have h3 : (Lam φ (planeD y ξ)).2.2 = 0 := congrArg (fun z : V3 => z.2.2) hξ
    simp only [Lam] at h1 h2 h3
    have hcs := sin_sq_add_cos_sq φ
    have z2 : (planeD y ξ).2.1 = 0 := by
      linear_combination cos φ * h2 + sin φ * h3 - (planeD y ξ).2.1 * hcs
    have z3 : (planeD y ξ).2.2 = 0 := by
      linear_combination -(sin φ) * h2 + cos φ * h3 - (planeD y ξ).2.2 * hcs
    have e1 : rr y (planeD y ξ) = 0 := by simp only [rr, z2, z3, mul_zero, add_zero]
    rw [rr_planeD] at e1
    have ha : ra y ξ = 0 := by
      by_contra hne
      have hS0 : SS (tau y) = 0 := (mul_eq_zero.mp e1).resolve_left hne
      have ht := tau_sq_of_SS hS0
      have hc0 : cos φ ≠ 0 := fun hc => hno ⟨hc, ht⟩
      have hq := dq_pos_of_crease (tau_nonneg y) ht
      rw [fst_planeD] at h1
      exact (mul_ne_zero hc0 (mul_ne_zero (mul_ne_zero two_ne_zero hq.ne') hne)) h1
    exact xi_of_ra ha z2 z3

/-! ### ホーンの部分 -/

/-- τ ≥ ½ で g は G である。 -/
theorem planeG_polar {ρ : ℝ} (hρ : 0 < ρ) (h : ρ ^ 2 ≤ 2) (v : ℝ) :
    planeG (cos v / ρ, sin v / ρ) = G ρ v := by
  have hc := sin_sq_add_cos_sq v
  have ht : tau (cos v / ρ, sin v / ρ) = 1 / ρ ^ 2 := by
    simp only [tau]
    field_simp
    linarith
  have hge : 1 / 2 ≤ 1 / ρ ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have hs : √(1 / ρ ^ 2) = 1 / ρ := by
    rw [show 1 / ρ ^ 2 = (1 / ρ) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hD := D_pos ρ
  simp only [planeG, ht, qC, chiC_of_ge hge, hs, hC, G, D]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; field_simp; ring
  · simp only; field_simp; ring
  · simp only; field_simp; ring

/-- ホーンの部分で n₀ は N の正の倍である。 -/
theorem n0_polar {ρ : ℝ} (hρ : 0 < ρ) (h : ρ ^ 2 < 2) (v : ℝ) :
    n0 (cos v / ρ, sin v / ρ) = (ρ ^ 2 / D ρ ^ 2) • N ρ v := by
  have hc := sin_sq_add_cos_sq v
  have ht : tau (cos v / ρ, sin v / ρ) = 1 / ρ ^ 2 := by
    simp only [tau]
    field_simp
    linarith
  have hgt : 1 / 2 < 1 / ρ ^ 2 := by
    rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
    linarith
  have hs : √(1 / ρ ^ 2) = 1 / ρ := by
    rw [show 1 / ρ ^ 2 = (1 / ρ) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  have hD : 1 + ρ ^ 4 ≠ 0 := by positivity
  simp only [n0, ht, SS_eq, dq_of hgt, hs, N, D, Prod.smul_mk, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; field_simp; ring
  · simp only; field_simp; ring
  · simp only; field_simp; ring

theorem tau_polar {ρ : ℝ} (hρ : 0 < ρ) (v : ℝ) : tau (cos v / ρ, sin v / ρ) = 1 / ρ ^ 2 := by
  have hc := sin_sq_add_cos_sq v
  simp only [tau]
  field_simp
  linarith

/-- |g|² ≤ 1/τ（τ ≥ ½）。y → ∞ で g(y) → ℘。 -/
theorem nsq_planeG_le {y : ℝ × ℝ} (h : 1 / 2 ≤ tau y) : nsq (planeG y) ≤ 1 / tau y := by
  have hτ : 0 < tau y := by linarith
  have hr : √(tau y) ^ 2 = tau y := Real.sq_sqrt hτ.le
  have e : nsq (planeG y) = tau y / (1 + tau y ^ 2) := by
    simp only [nsq, dot, planeG, qC, chiC_of_ge h, hC]
    have hD := (den_pos' (tau y)).ne'
    field_simp
    have e2 : y.1 ^ 2 + y.2 ^ 2 = tau y := rfl
    rw [hr]
    linear_combination e2
  rw [e, div_le_div_iff₀ (den_pos' _) hτ]
  nlinarith [sq_nonneg (tau y)]

/-- |g|² ≤ ½ -/
theorem nsq_planeG_le_half (y : ℝ × ℝ) : nsq (planeG y) ≤ 1 / 2 := by
  have hτ := tau_nonneg y
  have hχ0 := smoothTransition.nonneg (4 * tau y - 1)
  have hχ1 := smoothTransition.le_one (4 * tau y - 1)
  have hD := den_pos' (tau y)
  have e : nsq (planeG y) = (chiC (tau y) ^ 2 * tau y ^ 3 + tau y) / (1 + tau y ^ 2) ^ 2 := by
    have hr : √(tau y) ^ 2 = tau y := Real.sq_sqrt hτ
    simp only [nsq, dot, planeG, qC, hC]
    have e2 : y.1 ^ 2 + y.2 ^ 2 = tau y := rfl
    field_simp
    rw [hr]
    linear_combination e2
  rw [e, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hχ2 : chiC (tau y) ^ 2 ≤ 1 := by
    have h0 : 0 ≤ chiC (tau y) := hχ0
    have h1 : chiC (tau y) ≤ 1 := hχ1
    nlinarith
  have h3 : chiC (tau y) ^ 2 * tau y ^ 3 ≤ tau y ^ 3 :=
    mul_le_of_le_one_left (by positivity) hχ2
  nlinarith [sq_nonneg (tau y - 1), mul_nonneg hτ (sq_nonneg (tau y - 1))]

/-! ### 動く面の基底と形式解 -/

/-- 時間の階段 σ(s)：s ≤ ¼ で 0、s ≥ ¾ で 1、σ(½) = ½。 -/
def sig (s : ℝ) : ℝ := s₀ (2 * s - 1 / 2)

theorem sig_of_le {s : ℝ} (h : s ≤ 1 / 4) : sig s = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

theorem sig_of_ge {s : ℝ} (h : 3 / 4 ≤ s) : sig s = 1 :=
  smoothTransition.one_of_one_le (by linarith)

theorem sig_half : sig (1 / 2) = 1 / 2 := by
  simp only [sig]
  have e : (2 : ℝ) * (1 / 2) - 1 / 2 = 1 / 2 := by norm_num
  rw [e, s0_half]

theorem sig_nonneg (s : ℝ) : 0 ≤ sig s := smoothTransition.nonneg _

theorem sig_le_one (s : ℝ) : sig s ≤ 1 := smoothTransition.le_one _

theorem contDiff_sig : ContDiff ℝ ∞ sig := by
  unfold sig
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-- 倍率：σ = 0、1 で 1、σ = ½ で κ₀。 -/
def Kf (κ₀ σ : ℝ) : ℝ := 1 - (1 - κ₀) * (4 * σ * (1 - σ))

theorem Kf_zero (κ₀ : ℝ) : Kf κ₀ 0 = 1 := by simp [Kf]

theorem Kf_one (κ₀ : ℝ) : Kf κ₀ 1 = 1 := by simp [Kf]

theorem Kf_half (κ₀ : ℝ) : Kf κ₀ (1 / 2) = κ₀ := by
  simp only [Kf]; ring

theorem Kf_ge {κ₀ σ : ℝ} (h1 : κ₀ ≤ 1) : κ₀ ≤ Kf κ₀ σ := by
  simp only [Kf]
  nlinarith [mul_nonneg (sub_nonneg.2 h1) (sq_nonneg (2 * σ - 1))]

theorem Kf_le {κ₀ σ : ℝ} (h1 : κ₀ ≤ 1) (h2 : 0 ≤ σ) (h3 : σ ≤ 1) : Kf κ₀ σ ≤ 1 := by
  simp only [Kf]
  have : 0 ≤ 4 * σ * (1 - σ) := by
    have := sub_nonneg.2 h3
    positivity
  nlinarith [mul_nonneg (sub_nonneg.2 h1) this]

/-- 面の倍率 κ(s) -/
def kapS (κ₀ s : ℝ) : ℝ := Kf κ₀ (sig s)

/-- 傘の角度 φ(s) = π σ(s) -/
def phiS (s : ℝ) : ℝ := π * sig s

theorem contDiff_kapS (κ₀ : ℝ) : ContDiff ℝ ∞ (kapS κ₀) := by
  have h := contDiff_sig
  unfold kapS Kf
  fun_prop

theorem contDiff_phiS : ContDiff ℝ ∞ phiS :=
  contDiff_const.mul contDiff_sig

theorem kapS_pos {κ₀ : ℝ} (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1) (s : ℝ) : 0 < kapS κ₀ s :=
  lt_of_lt_of_le h0 (Kf_ge h1)

theorem kapS_le {κ₀ : ℝ} (h1 : κ₀ ≤ 1) (s : ℝ) : kapS κ₀ s ≤ 1 :=
  Kf_le h1 (sig_nonneg s) (sig_le_one s)

/-- 混合の切り替え：τ ≤ 0.8 で 1、τ ≥ 0.9 で 0。 -/
def chiT (y : ℝ × ℝ) : ℝ := 1 - s₀ (10 * tau y - 8)

theorem chiT_of_le {y : ℝ × ℝ} (h : tau y ≤ 8 / 10) : chiT y = 1 := by
  have : 10 * tau y - 8 ≤ 0 := by linarith
  simp [chiT, smoothTransition.zero_of_nonpos this]

theorem chiT_of_ge {y : ℝ × ℝ} (h : 9 / 10 ≤ tau y) : chiT y = 0 := by
  have : 1 ≤ 10 * tau y - 8 := by linarith
  simp [chiT, smoothTransition.one_of_one_le this]

theorem chiT_nonneg (y : ℝ × ℝ) : 0 ≤ chiT y := by
  have := smoothTransition.le_one (10 * tau y - 8)
  simp only [chiT]; linarith

theorem chiT_le_one (y : ℝ × ℝ) : chiT y ≤ 1 := by
  have := smoothTransition.nonneg (10 * tau y - 8)
  simp only [chiT]; linarith

theorem contDiff_chiT : ContDiff ℝ ∞ chiT := by
  have h : ContDiff ℝ ∞ (fun y => s₀ (10 * tau y - 8)) :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_tau).sub contDiff_const)
  exact contDiff_const.sub h

theorem contDiff_Lam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ} {g : E → V3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun x => Lam (f x) (g x)) := by
  have hc : ContDiff ℝ ∞ (fun x => cos (f x)) := Real.contDiff_cos.comp hf
  have hs : ContDiff ℝ ∞ (fun x => sin (f x)) := Real.contDiff_sin.comp hf
  have g1 : ContDiff ℝ ∞ (fun x => (g x).1) := contDiff_fst.comp hg
  have g2 : ContDiff ℝ ∞ (fun x => (g x).2.1) := contDiff_fst.comp (contDiff_snd.comp hg)
  have g3 : ContDiff ℝ ∞ (fun x => (g x).2.2) := contDiff_snd.comp (contDiff_snd.comp hg)
  exact (hc.mul g1).prodMk (((hc.mul g2).sub (hs.mul g3)).prodMk ((hs.mul g2).add (hc.mul g3)))

/-- 基底の族 κ(s) U(φ(s))。 -/
def bsP (κ₀ s : ℝ) (y : ℝ × ℝ) : V3 := kapS κ₀ s • Lam (phiS s) (planeG y)

theorem contDiff_bsP (κ₀ : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => bsP κ₀ p.1 p.2) := by
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => kapS κ₀ p.1) :=
    (contDiff_kapS κ₀).comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => phiS p.1) := contDiff_phiS.comp contDiff_fst
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => planeG p.2) := contDiff_planeG.comp contDiff_snd
  exact h1.smul (contDiff_Lam h2 h3)

theorem bsP_of_le {κ₀ s : ℝ} (h : s ≤ 1 / 4) (y : ℝ × ℝ) : bsP κ₀ s y = planeG y := by
  simp [bsP, kapS, phiS, sig_of_le h, Kf_zero, Lam_zero]

theorem bsP_of_ge {κ₀ s : ℝ} (h : 3 / 4 ≤ s) (y : ℝ × ℝ) : bsP κ₀ s y = -planeG y := by
  simp [bsP, kapS, phiS, sig_of_ge h, Kf_one, Lam_pi]

/-- 形式解の線形写像の値。 -/
def LLfun (κ₀ : ℝ) (p : ℝ × (ℝ × ℝ)) (u : V3) : V3 :=
  kapS κ₀ p.1 • blendM (chiT p.2) (phiS p.1) (nh p.2) u

theorem blendM_add (χ φ : ℝ) (n a b : V3) :
    blendM χ φ n (a + b) = blendM χ φ n a + blendM χ φ n b := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [blendM, Rod, Lam, cross, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> ring

theorem blendM_smul (χ φ : ℝ) (n : V3) (k : ℝ) (a : V3) :
    blendM χ φ n (k • a) = k • blendM χ φ n a := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [blendM, Rod, Lam, cross, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, Prod.fst_sub, Prod.snd_sub, smul_eq_mul] <;> ring

/-- 形式解の線形写像の族 L(s, y)。 -/
def LL (κ₀ : ℝ) (p : ℝ × (ℝ × ℝ)) : V3 →L[ℝ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := LLfun κ₀ p
      map_add' := fun a b => by
        simp only [LLfun, blendM_add, smul_add]
      map_smul' := fun k a => by
        simp only [LLfun, blendM_smul, RingHom.id_apply, smul_comm (kapS κ₀ p.1) k] }

@[simp] theorem LL_apply (κ₀ : ℝ) (p : ℝ × (ℝ × ℝ)) (u : V3) : LL κ₀ p u = LLfun κ₀ p u := rfl

theorem contDiff_LL (κ₀ : ℝ) : ContDiff ℝ ∞ (LL κ₀) := by
  rw [contDiff_clm_apply_iff]
  intro u
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => kapS κ₀ p.1) :=
    (contDiff_kapS κ₀).comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => phiS p.1) := contDiff_phiS.comp contDiff_fst
  have h3 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => chiT p.2) := contDiff_chiT.comp contDiff_snd
  have h4 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => nh p.2) := contDiff_nh.comp contDiff_snd
  have hL : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Lam (phiS p.1) u) :=
    contDiff_Lam h2 contDiff_const
  have n1 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (nh p.2).1) := contDiff_fst.comp h4
  have n2 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (nh p.2).2.1) :=
    contDiff_fst.comp (contDiff_snd.comp h4)
  have n3 : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (nh p.2).2.2) :=
    contDiff_snd.comp (contDiff_snd.comp h4)
  have hc : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => cross (nh p.2) u) :=
    ((n2.mul contDiff_const).sub (n3.mul contDiff_const)).prodMk
      (((n3.mul contDiff_const).sub (n1.mul contDiff_const)).prodMk
        ((n1.mul contDiff_const).sub (n2.mul contDiff_const)))
  have hd : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => dot (nh p.2) u) :=
    ((n1.mul contDiff_const).add (n2.mul contDiff_const)).add (n3.mul contDiff_const)
  have hcos : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => cos (phiS p.1)) := Real.contDiff_cos.comp h2
  have hsin : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => sin (phiS p.1)) := Real.contDiff_sin.comp h2
  have hR : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => Rod (phiS p.1) (nh p.2) u) := by
    unfold Rod
    exact ((hcos.smul contDiff_const).sub (hsin.smul hc)).add
      (((contDiff_const.sub hcos).mul hd).smul h4)
  have hB : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => blendM (chiT p.2) (phiS p.1) (nh p.2) u) := by
    unfold blendM
    exact ((contDiff_const.sub h3).smul hL).add (h3.smul hR)
  exact h1.smul hB

/-- dbs の式。 -/
theorem fderiv_bsP (κ₀ s : ℝ) (y ξ : ℝ × ℝ) :
    fderiv ℝ (bsP κ₀ s) y ξ = kapS κ₀ s • Lam (phiS s) (planeD y ξ) := by
  have hd : HasFDerivAt planeG (fderiv ℝ planeG y) y :=
    (contDiff_planeG.differentiable (by simp) y).hasFDerivAt
  have h := (kapS κ₀ s • LamL (phiS s)).hasFDerivAt.comp y hd
  have e : (⇑(kapS κ₀ s • LamL (phiS s)) ∘ planeG) = bsP κ₀ s := rfl
  rw [e] at h
  rw [h.fderiv]
  simp [fderiv_planeG]

theorem LL_comp_apply (κ₀ : ℝ) (p : ℝ × (ℝ × ℝ)) (ξ : ℝ × ℝ) :
    (LL κ₀ p).comp (fderiv ℝ planeG p.2) ξ =
      kapS κ₀ p.1 • blendM (chiT p.2) (phiS p.1) (nh p.2) (planeD p.2 ξ) := by
  simp [fderiv_planeG, LLfun]

/-- **形式解は単射である**。 -/
theorem LL_inj {κ₀ : ℝ} (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1) (p : ℝ × (ℝ × ℝ)) :
    Function.Injective ((LL κ₀ p).comp (fderiv ℝ planeG p.2)) := by
  refine (injective_iff_map_eq_zero _).mpr fun ξ hξ => ?_
  rw [LL_comp_apply] at hξ
  have hk := (kapS_pos h0 h1 p.1).ne'
  have hb := (smul_eq_zero.mp hξ).resolve_left hk
  refine frame_inj (phiS p.1) (chiT_nonneg p.2) (chiT_le_one p.2) ?_ hb
  intro hS
  apply chiT_of_le
  rw [SS_eq] at hS
  have hn : 0 ≤ 1 - 3 * tau p.2 ^ 2 := by
    by_contra hneg
    push Not at hneg
    have := div_neg_of_neg_of_pos hneg (pow_pos (den_pos' (tau p.2)) 2)
    linarith
  have ht := tau_nonneg p.2
  nlinarith

/-- 基底は、端の時刻とホーンの近くで形式解に一致する（ホロノミック）。 -/
theorem hol_identity (κ₀ : ℝ) {p : ℝ × (ℝ × ℝ)}
    (hp : p.1 < 1 / 4 ∨ 3 / 4 < p.1 ∨ 9 / 10 < tau p.2) :
    fderiv ℝ (bsP κ₀ p.1) p.2 = (LL κ₀ p).comp (fderiv ℝ planeG p.2) := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [LL_comp_apply, fderiv_bsP]
  have hperp := dot_nh_planeD p.2 ξ
  rcases hp with h | h | h
  · have e : phiS p.1 = 0 := by simp [phiS, sig_of_le h.le]
    simp [blendM, e, Rod_zero, Lam_zero, ← add_smul]
  · have e : phiS p.1 = π := by simp [phiS, sig_of_ge h.le]
    simp only [blendM, e, Rod_pi hperp, Lam_pi]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_neg,
        Prod.snd_neg, smul_eq_mul] <;> ring
  · simp [blendM, chiT_of_ge h.le]

end Zeno.Model
