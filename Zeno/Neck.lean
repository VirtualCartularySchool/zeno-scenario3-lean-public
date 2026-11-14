/-
# Zeno.Neck : 定理 B の面 Σ（静止した正則な接続）

Σ(w, v) = Rot₂(ψ(w))·(A(w), B(w)eⁱᵛ)。A + iB = exp(iκ)·C(ρ)、C(p) = a(p) + ib(p) は子午線。
ρ は偶で滑らか、|w| が大きいところで ρ = |w|、ρ(0) > 0。
円は内向きの途中で q₂ 軸まわりに半回転し、最小半径で折り返して外へ出る。

Smale の定理は使わない。正則性は首の補題 `neck_lemma` から出る。
-/
import Zeno.NeckLemma
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### 滑らかな階段の導関数の上界 -/

theorem deriv_s0_eq_zero {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) : deriv s₀ x = 0 := by
  rcases not_and_or.mp hx with h | h
  · have h' : x < 0 := not_le.mp h
    have e : s₀ =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h'] with y hy
      exact smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [e.deriv_eq]; simp
  · have h' : 1 < x := not_le.mp h
    have e : s₀ =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h'] with y hy
      exact smoothTransition.one_of_one_le (le_of_lt hy)
    rw [e.deriv_eq]; simp

theorem exists_deriv_bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |deriv s₀ x| ≤ K := by
  have hc : Continuous (deriv s₀) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨K, hK⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · have h := hK x hx
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · rw [deriv_s0_eq_zero hx, abs_zero]
    exact le_max_right K 0

/-- s₀′ の上界。 -/
def Ks : ℝ := Classical.choose exists_deriv_bound

theorem Ks_nonneg : 0 ≤ Ks := (Classical.choose_spec exists_deriv_bound).1

theorem abs_deriv_s0_le (x : ℝ) : |deriv s₀ x| ≤ Ks :=
  (Classical.choose_spec exists_deriv_bound).2 x

theorem hasDerivAt_s0 (x : ℝ) : HasDerivAt s₀ (deriv s₀ x) x :=
  ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt

/-! ### 切り落とし -/

/-- x ≤ c/4 で 1、x ≥ c/2 で 0。 -/
def cut (c x : ℝ) : ℝ := 1 - s₀ (4 * x / c - 1)

theorem cut_of_le {c x : ℝ} (hc : 0 < c) (h : x ≤ c / 4) : cut c x = 1 := by
  have : 4 * x / c - 1 ≤ 0 := by
    have : 4 * x / c ≤ 1 := by
      rw [div_le_one hc]; linarith
    linarith
  simp [cut, smoothTransition.zero_of_nonpos this]

theorem cut_of_ge {c x : ℝ} (hc : 0 < c) (h : c / 2 ≤ x) : cut c x = 0 := by
  have : 1 ≤ 4 * x / c - 1 := by
    have : 2 ≤ 4 * x / c := by
      rw [le_div_iff₀ hc]; linarith
    linarith
  simp [cut, smoothTransition.one_of_one_le this]

theorem cut_nonneg (c x : ℝ) : 0 ≤ cut c x := by
  have := smoothTransition.le_one (4 * x / c - 1)
  simp only [cut]; linarith

theorem cut_le_one (c x : ℝ) : cut c x ≤ 1 := by
  have := smoothTransition.nonneg (4 * x / c - 1)
  simp only [cut]; linarith

theorem contDiff_cut (c : ℝ) : ContDiff ℝ ∞ (cut c) := by
  unfold cut
  refine contDiff_const.sub (Real.smoothTransition.contDiff.comp ?_)
  fun_prop

theorem hasDerivAt_cut (c x : ℝ) :
    HasDerivAt (cut c) (-(deriv s₀ (4 * x / c - 1) * (4 / c))) x := by
  have h1 : HasDerivAt (fun x : ℝ => 4 * x / c - 1) (4 / c) x := by
    have := (((hasDerivAt_id x).const_mul 4).div_const c).sub_const 1
    simpa using this
  have h2 := (hasDerivAt_s0 (4 * x / c - 1)).comp x h1
  exact h2.const_sub 1

/-! ### ρ² の修正 hh -/

/-- ρ₀² -/
def rsq (w₀ : ℝ) : ℝ := w₀ ^ 2 / (8 * Ks + 8)

/-- ρ² = hh(w²)。τ ≥ τ₀/2 で hh(τ) = τ、hh(0) = ρ₀² > 0、hh′ ≥ ½。 -/
def hh (w₀ τ : ℝ) : ℝ := τ + rsq w₀ * cut (w₀ ^ 2) τ

theorem den_pos : 0 < 8 * Ks + 8 := by
  have := Ks_nonneg; linarith

theorem rsq_pos {w₀ : ℝ} (h : w₀ ≠ 0) : 0 < rsq w₀ :=
  div_pos (by positivity) den_pos

theorem rsq_le {w₀ : ℝ} : rsq w₀ ≤ w₀ ^ 2 / 8 := by
  have := Ks_nonneg
  unfold rsq
  exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)

theorem contDiff_hh (w₀ : ℝ) : ContDiff ℝ ∞ (hh w₀) := by
  unfold hh
  exact contDiff_id.add (contDiff_const.mul (contDiff_cut _))

/-- hh′ -/
def dh (w₀ τ : ℝ) : ℝ := 1 + rsq w₀ * -(deriv s₀ (4 * τ / w₀ ^ 2 - 1) * (4 / w₀ ^ 2))

theorem hasDerivAt_hh (w₀ τ : ℝ) : HasDerivAt (hh w₀) (dh w₀ τ) τ := by
  exact (hasDerivAt_id' τ).add ((hasDerivAt_cut (w₀ ^ 2) τ).const_mul (rsq w₀))

theorem dh_ge {w₀ : ℝ} (h : w₀ ≠ 0) (τ : ℝ) : 1 / 2 ≤ dh w₀ τ := by
  have hK := Ks_nonneg
  have hw : 0 < w₀ ^ 2 := by positivity
  have hb := abs_le.mp (abs_deriv_s0_le (4 * τ / w₀ ^ 2 - 1))
  set d := deriv s₀ (4 * τ / w₀ ^ 2 - 1) with hd
  have e : rsq w₀ * -(d * (4 / w₀ ^ 2)) = -(4 * d / (8 * Ks + 8)) := by
    have := den_pos.ne'
    simp only [rsq]
    field_simp
  have h2 : 4 * d / (8 * Ks + 8) ≤ 1 / 2 := by
    rw [div_le_iff₀ den_pos]; linarith [hb.2]
  simp only [dh, ← hd, e]
  linarith

theorem dh_pos {w₀ : ℝ} (h : w₀ ≠ 0) (τ : ℝ) : 0 < dh w₀ τ := by
  have := dh_ge h τ; linarith

theorem hh_strictMono {w₀ : ℝ} (h : w₀ ≠ 0) : StrictMono (hh w₀) := by
  refine strictMono_of_deriv_pos fun x => ?_
  rw [(hasDerivAt_hh w₀ x).deriv]
  exact dh_pos h x

theorem hh_zero {w₀ : ℝ} (h : w₀ ≠ 0) : hh w₀ 0 = rsq w₀ := by
  have hw : 0 < w₀ ^ 2 := by positivity
  simp only [hh, cut_of_le hw (by positivity : (0 : ℝ) ≤ w₀ ^ 2 / 4)]
  ring

theorem hh_of_ge {w₀ τ : ℝ} (h : w₀ ≠ 0) (hτ : w₀ ^ 2 / 2 ≤ τ) : hh w₀ τ = τ := by
  have hw : 0 < w₀ ^ 2 := by positivity
  simp [hh, cut_of_ge hw hτ]

theorem hh_pos {w₀ τ : ℝ} (h : w₀ ≠ 0) (hτ : 0 ≤ τ) : 0 < hh w₀ τ := by
  rcases eq_or_lt_of_le hτ with h0 | h0
  · rw [← h0, hh_zero h]; exact rsq_pos h
  · have h1 := cut_nonneg (w₀ ^ 2) τ
    have h2 := rsq_pos h
    simp only [hh]; positivity

theorem hh_ge_rsq {w₀ τ : ℝ} (h : w₀ ≠ 0) (hτ : 0 ≤ τ) : rsq w₀ ≤ hh w₀ τ := by
  rw [← hh_zero h]
  exact (hh_strictMono h).monotone hτ

theorem hh_one {w₀ : ℝ} (h : w₀ ≠ 0) (h1 : w₀ ^ 2 ≤ 1) : hh w₀ 1 = 1 :=
  hh_of_ge h (by linarith)

/-! ### ρ -/

/-- 半径の助変数 ρ(w) = √hh(w²)。 -/
def rho (w₀ w : ℝ) : ℝ := √(hh w₀ (w ^ 2))

theorem rho_pos {w₀ : ℝ} (h : w₀ ≠ 0) (w : ℝ) : 0 < rho w₀ w :=
  Real.sqrt_pos.mpr (hh_pos h (sq_nonneg w))

theorem rho_sq {w₀ : ℝ} (h : w₀ ≠ 0) (w : ℝ) : rho w₀ w ^ 2 = hh w₀ (w ^ 2) :=
  Real.sq_sqrt (hh_pos h (sq_nonneg w)).le

theorem rho_of {w₀ w : ℝ} (h : w₀ ≠ 0) (hw : w₀ ^ 2 / 2 ≤ w ^ 2) : rho w₀ w = |w| := by
  simp only [rho, hh_of_ge h hw, Real.sqrt_sq_eq_abs]

theorem contDiff_rho {w₀ : ℝ} (h : w₀ ≠ 0) : ContDiff ℝ ∞ (rho w₀) := by
  unfold rho
  refine ContDiff.sqrt ((contDiff_hh w₀).comp (contDiff_id.pow 2)) fun x => ?_
  exact (hh_pos h (sq_nonneg x)).ne'

theorem hasDerivAt_hh_sq (w₀ w : ℝ) :
    HasDerivAt (fun w => hh w₀ (w ^ 2)) (dh w₀ (w ^ 2) * (2 * w)) w := by
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * w) w := by
    simpa using hasDerivAt_pow 2 w
  exact (hasDerivAt_hh w₀ (w ^ 2)).comp w h2

theorem hasDerivAt_rho {w₀ : ℝ} (h : w₀ ≠ 0) (w : ℝ) :
    HasDerivAt (rho w₀) (dh w₀ (w ^ 2) * w / rho w₀ w) w := by
  have h1 := (hasDerivAt_hh_sq w₀ w).sqrt (hh_pos h (sq_nonneg w)).ne'
  refine h1.congr_deriv ?_
  have := rho_pos h w
  change dh w₀ (w ^ 2) * (2 * w) / (2 * rho w₀ w) = _
  field_simp

/-! ### κ と ψ -/

/-- 折り返しの回転 κ。 -/
def kap (w₀ w : ℝ) : ℝ := rsq w₀ / (4 * w₀) * w * cut (w₀ ^ 2) (w ^ 2)

theorem contDiff_kap (w₀ : ℝ) : ContDiff ℝ ∞ (kap w₀) := by
  unfold kap
  exact (contDiff_const.mul contDiff_id).mul ((contDiff_cut _).comp (contDiff_id.pow 2))

theorem kap_of {w₀ w : ℝ} (h : w₀ ≠ 0) (hw : w₀ ^ 2 / 2 ≤ w ^ 2) : kap w₀ w = 0 := by
  have h2 : 0 < w₀ ^ 2 := by positivity
  simp [kap, cut_of_ge h2 hw]

theorem abs_kap_le {w₀ : ℝ} (h : 0 < w₀) (w : ℝ) : |kap w₀ w| ≤ rsq w₀ / 4 := by
  have hr := rsq_pos h.ne'
  have hw2 : 0 < w₀ ^ 2 := by positivity
  by_cases hw : w₀ ^ 2 / 2 ≤ w ^ 2
  · rw [kap_of h.ne' hw, abs_zero]; positivity
  · have hlt : w ^ 2 < w₀ ^ 2 := by push Not at hw; linarith
    have habs : |w| < w₀ := by
      rw [← abs_of_pos h]; exact sq_lt_sq.mp hlt
    have hc0 := cut_nonneg (w₀ ^ 2) (w ^ 2)
    have hc1 := cut_le_one (w₀ ^ 2) (w ^ 2)
    have hk : 0 < rsq w₀ / (4 * w₀) := by positivity
    simp only [kap, abs_mul, abs_of_pos hk, abs_of_nonneg hc0]
    calc rsq w₀ / (4 * w₀) * |w| * cut (w₀ ^ 2) (w ^ 2)
        ≤ rsq w₀ / (4 * w₀) * w₀ * 1 := by
          apply mul_le_mul _ hc1 hc0 (by positivity)
          exact mul_le_mul_of_nonneg_left habs.le hk.le
      _ = rsq w₀ / 4 := by field_simp

/-- ψ : w ≤ w₀/4 で π、w ≥ w₀/2 で 0。 -/
def psi (w₀ w : ℝ) : ℝ := π * (1 - s₀ ((4 * w - w₀) / w₀))

theorem contDiff_psi (w₀ : ℝ) : ContDiff ℝ ∞ (psi w₀) := by
  unfold psi
  refine contDiff_const.mul (contDiff_const.sub (Real.smoothTransition.contDiff.comp ?_))
  fun_prop

theorem psi_of_le {w₀ w : ℝ} (h : 0 < w₀) (hw : w ≤ w₀ / 4) : psi w₀ w = π := by
  have : (4 * w - w₀) / w₀ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) h.le
  simp [psi, smoothTransition.zero_of_nonpos this]

theorem psi_of_ge {w₀ w : ℝ} (h : 0 < w₀) (hw : w₀ / 2 ≤ w) : psi w₀ w = 0 := by
  have : 1 ≤ (4 * w - w₀) / w₀ := by
    rw [le_div_iff₀ h]; linarith
  simp [psi, smoothTransition.one_of_one_le this]

/-- ψ が動くのは w₀/4 ≤ w ≤ w₀/2 だけである。 -/
theorem deriv_psi_ne {w₀ w : ℝ} (h : 0 < w₀) (hd : deriv (psi w₀) w ≠ 0) :
    w₀ / 4 ≤ w ∧ w ≤ w₀ / 2 := by
  constructor
  · by_contra hlt
    push Not at hlt
    apply hd
    have e : psi w₀ =ᶠ[𝓝 w] fun _ => π := by
      filter_upwards [Iio_mem_nhds hlt] with y hy using psi_of_le h (le_of_lt hy)
    rw [e.deriv_eq]; simp
  · by_contra hlt
    push Not at hlt
    apply hd
    have e : psi w₀ =ᶠ[𝓝 w] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hlt] with y hy using psi_of_ge h (le_of_lt hy)
    rw [e.deriv_eq]; simp

/-! ### 子午線 -/

/-- 子午線の第 1 成分 -/
def aa (p : ℝ) : ℝ := p / D p
/-- 子午線の第 2 成分 -/
def bb (p : ℝ) : ℝ := p ^ 3 / D p
/-- a′ -/
def da (p : ℝ) : ℝ := (1 - 3 * p ^ 4) / D p ^ 2
/-- b′ -/
def db (p : ℝ) : ℝ := p ^ 2 * (3 - p ^ 4) / D p ^ 2

theorem hasDerivAt_aa (p : ℝ) : HasDerivAt aa (da p) p := hasDerivAt_a p

theorem hasDerivAt_bb (p : ℝ) : HasDerivAt bb (db p) p := by
  have h := hasDerivAt_b_mul 1 p
  simp only [mul_one] at h
  exact h

theorem contDiff_D : ContDiff ℝ ∞ D := by
  unfold D
  exact contDiff_const.add (contDiff_id.pow 4)

theorem contDiff_aa : ContDiff ℝ ∞ aa := contDiff_id.div contDiff_D D_ne

theorem contDiff_bb : ContDiff ℝ ∞ bb := (contDiff_id.pow 3).div contDiff_D D_ne

theorem G_eq_aa_bb (w v : ℝ) : G w v = (aa w, bb w * cos v, bb w * sin v) := by
  simp only [G, aa, bb]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem aa_pos {p : ℝ} (h : 0 < p) : 0 < aa p := div_pos h (D_pos p)

theorem bb_eq (p : ℝ) : bb p = p ^ 2 * aa p := by
  simp only [aa, bb]; ring

theorem aa_neg (p : ℝ) : aa (-p) = -aa p := by
  simp only [aa, D_neg]; ring

theorem bb_neg (p : ℝ) : bb (-p) = -bb p := by
  simp only [bb, D_neg]; ring

theorem aa_sq_add (p : ℝ) : aa p ^ 2 + bb p ^ 2 = p ^ 2 / D p := by
  have h := D_ne p
  simp only [aa, bb]
  field_simp
  simp only [D]

/-- 子午線はベルヌーイのレムニスケート (q₁² + ρ²)² = q₁ρ である。 -/
theorem lemniscate (w : ℝ) : (aa w ^ 2 + bb w ^ 2) ^ 2 = aa w * bb w := by
  have h := D_ne w
  rw [aa_sq_add]
  simp only [aa, bb]
  field_simp

/-- 子午線の複素表示 C(w) = w/(1 − iw²)。 -/
theorem meridian_formula (w : ℝ) :
    (aa w : ℂ) + Complex.I * (bb w : ℂ) = (w : ℂ) / (1 - Complex.I * (w : ℂ) ^ 2) := by
  have hne : (1 - Complex.I * (w : ℂ) ^ 2) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [pow_two] at hre
  rw [eq_div_iff hne]
  have hD : ((D w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast D_ne w
  simp only [aa, bb, Complex.ofReal_div, Complex.ofReal_pow]
  field_simp
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  simp only [D, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_pow]
  linear_combination (-(w : ℂ) ^ 5) * hI

/-- 子午線の速度 C′(w) = (1 + iw²)³/D²。接線の角は 3 arctan w² である。 -/
theorem meridian_velocity (w : ℝ) :
    (da w : ℂ) + Complex.I * (db w : ℂ) =
      (1 + Complex.I * (w : ℂ) ^ 2) ^ 3 / ((D w : ℝ) : ℂ) ^ 2 := by
  have hD : ((D w : ℝ) : ℂ) ≠ 0 := by exact_mod_cast D_ne w
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hI3 : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, hI]; ring
  rw [eq_div_iff (pow_ne_zero 2 hD)]
  simp only [da, db, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_one, Complex.ofReal_ofNat]
  field_simp
  ring_nf
  rw [hI3, hI]
  ring

/-- 半径の式 a² + b² を p² の関数で書く。 -/
def Rad (x : ℝ) : ℝ := x / (1 + x ^ 2)

theorem aa_sq_add' (p : ℝ) : aa p ^ 2 + bb p ^ 2 = Rad (p ^ 2) := by
  rw [aa_sq_add]
  simp only [Rad, D]
  congr 1
  ring

theorem Rad_lt {x y : ℝ} (h0 : 0 ≤ x) (hxy : x < y) (h1 : y ≤ 1) : Rad x < Rad y := by
  simp only [Rad]
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), mul_pos (sub_pos.2 hxy) (sub_pos.2 (lt_of_lt_of_le hxy h1))]

theorem Rad_pos {x : ℝ} (h : 0 < x) : 0 < Rad x := by
  simp only [Rad]; positivity

theorem Rad_lt_self {x : ℝ} (h : 0 < x) : Rad x < x := by
  simp only [Rad]
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [pow_pos h 3]

theorem radial_id (p : ℝ) : aa p * da p + bb p * db p = p * (1 - p ^ 4) / D p ^ 2 := by
  have h := D_ne p
  simp only [aa, bb, da, db]
  field_simp
  simp only [D]
  ring

theorem da_db_ne (p : ℝ) : ¬ (da p = 0 ∧ db p = 0) := by
  rintro ⟨h1, h2⟩
  have hD : D p ^ 2 ≠ 0 := pow_ne_zero 2 (D_ne p)
  have e1 : 1 - 3 * p ^ 4 = 0 := by
    simp only [da] at h1
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact h
    · exact absurd h hD
  have e2 : p ^ 2 * (3 - p ^ 4) = 0 := by
    simp only [db] at h2
    rcases div_eq_zero_iff.mp h2 with h | h
    · exact h
    · exact absurd h hD
  rcases mul_eq_zero.mp e2 with h | h
  · have : p ^ 4 = 0 := by
      have : p ^ 4 = (p ^ 2) ^ 2 := by ring
      rw [this, h]; norm_num
    rw [this] at e1
    norm_num at e1
  · have : p ^ 4 = 3 := by linarith
    rw [this] at e1
    norm_num at e1

/-! ### 断面曲線 -/

/-- 断面の第 1 成分 A = a(ρ) cos κ − b(ρ) sin κ -/
def AA (w₀ w : ℝ) : ℝ := aa (rho w₀ w) * cos (kap w₀ w) - bb (rho w₀ w) * sin (kap w₀ w)

/-- 断面の第 2 成分 B = a(ρ) sin κ + b(ρ) cos κ -/
def BB (w₀ w : ℝ) : ℝ := aa (rho w₀ w) * sin (kap w₀ w) + bb (rho w₀ w) * cos (kap w₀ w)

theorem contDiff_AA {w₀ : ℝ} (h : w₀ ≠ 0) : ContDiff ℝ ∞ (AA w₀) := by
  unfold AA
  exact (contDiff_aa.comp (contDiff_rho h)).mul (Real.contDiff_cos.comp (contDiff_kap w₀)) |>.sub
    ((contDiff_bb.comp (contDiff_rho h)).mul (Real.contDiff_sin.comp (contDiff_kap w₀)))

theorem contDiff_BB {w₀ : ℝ} (h : w₀ ≠ 0) : ContDiff ℝ ∞ (BB w₀) := by
  unfold BB
  exact (contDiff_aa.comp (contDiff_rho h)).mul (Real.contDiff_sin.comp (contDiff_kap w₀)) |>.add
    ((contDiff_bb.comp (contDiff_rho h)).mul (Real.contDiff_cos.comp (contDiff_kap w₀)))

theorem AA_of {w₀ w : ℝ} (h : w₀ ≠ 0) (hw : w₀ ^ 2 / 2 ≤ w ^ 2) : AA w₀ w = aa |w| := by
  simp [AA, rho_of h hw, kap_of h hw]

theorem BB_of {w₀ w : ℝ} (h : w₀ ≠ 0) (hw : w₀ ^ 2 / 2 ≤ w ^ 2) : BB w₀ w = bb |w| := by
  simp [BB, rho_of h hw, kap_of h hw]

theorem AA_sq_add {w₀ : ℝ} (h : w₀ ≠ 0) (w : ℝ) :
    AA w₀ w ^ 2 + BB w₀ w ^ 2 = Rad (hh w₀ (w ^ 2)) := by
  rw [← rho_sq h, ← aa_sq_add']
  simp only [AA, BB]
  linear_combination (aa (rho w₀ w) ^ 2 + bb (rho w₀ w) ^ 2) * sin_sq_add_cos_sq (kap w₀ w)

/-- ρ′ -/
def drho (w₀ w : ℝ) : ℝ := dh w₀ (w ^ 2) * w / rho w₀ w

/-- 回転枠での断面の速度の第 1 成分 -/
def uu (w₀ w : ℝ) : ℝ := da (rho w₀ w) * drho w₀ w - deriv (kap w₀) w * bb (rho w₀ w)

/-- 回転枠での断面の速度の第 2 成分 -/
def vv (w₀ w : ℝ) : ℝ := db (rho w₀ w) * drho w₀ w + deriv (kap w₀) w * aa (rho w₀ w)

theorem hasDerivAt_kap (w₀ w : ℝ) : HasDerivAt (kap w₀) (deriv (kap w₀) w) w :=
  ((contDiff_kap w₀).differentiable (by simp) w).hasDerivAt

theorem hasDerivAt_AA {w₀ : ℝ} (h : w₀ ≠ 0) (w : ℝ) :
    HasDerivAt (AA w₀)
      (uu w₀ w * cos (kap w₀ w) - vv w₀ w * sin (kap w₀ w)) w := by
  have hρ := hasDerivAt_rho h w
  have hκ := hasDerivAt_kap w₀ w
  have ha := (hasDerivAt_aa (rho w₀ w)).comp w hρ
  have hb := (hasDerivAt_bb (rho w₀ w)).comp w hρ
  refine ((ha.mul hκ.cos).sub (hb.mul hκ.sin)).congr_deriv ?_
  simp only [uu, vv, drho, Function.comp]
  ring

theorem hasDerivAt_BB {w₀ : ℝ} (h : w₀ ≠ 0) (w : ℝ) :
    HasDerivAt (BB w₀)
      (uu w₀ w * sin (kap w₀ w) + vv w₀ w * cos (kap w₀ w)) w := by
  have hρ := hasDerivAt_rho h w
  have hκ := hasDerivAt_kap w₀ w
  have ha := (hasDerivAt_aa (rho w₀ w)).comp w hρ
  have hb := (hasDerivAt_bb (rho w₀ w)).comp w hρ
  refine ((ha.mul hκ.sin).add (hb.mul hκ.cos)).congr_deriv ?_
  simp only [uu, vv, drho, Function.comp]
  ring

/-- 半径の導関数の式。 -/
theorem radial_eq {w₀ : ℝ} (h : w₀ ≠ 0) (w : ℝ) :
    AA w₀ w * deriv (AA w₀) w + BB w₀ w * deriv (BB w₀) w =
      dh w₀ (w ^ 2) * w * (1 - rho w₀ w ^ 4) / D (rho w₀ w) ^ 2 := by
  have hρ := (rho_pos h w).ne'
  have hD := D_ne (rho w₀ w)
  rw [(hasDerivAt_AA h w).deriv, (hasDerivAt_BB h w).deriv]
  have e : AA w₀ w * (uu w₀ w * cos (kap w₀ w) - vv w₀ w * sin (kap w₀ w)) +
      BB w₀ w * (uu w₀ w * sin (kap w₀ w) + vv w₀ w * cos (kap w₀ w)) =
      aa (rho w₀ w) * uu w₀ w + bb (rho w₀ w) * vv w₀ w := by
    simp only [AA, BB]
    linear_combination (aa (rho w₀ w) * uu w₀ w + bb (rho w₀ w) * vv w₀ w) *
      sin_sq_add_cos_sq (kap w₀ w)
  rw [e]
  have e2 : aa (rho w₀ w) * uu w₀ w + bb (rho w₀ w) * vv w₀ w =
      (aa (rho w₀ w) * da (rho w₀ w) + bb (rho w₀ w) * db (rho w₀ w)) * drho w₀ w := by
    simp only [uu, vv]; ring
  rw [e2, radial_id]
  simp only [drho]
  field_simp

/-- w² < 1 なら ρ < 1。 -/
theorem rho_sq_lt_one {w₀ w : ℝ} (h : w₀ ≠ 0) (h1 : w₀ ^ 2 ≤ 1) (hw : w ^ 2 < 1) :
    rho w₀ w ^ 2 < 1 := by
  rw [rho_sq h, ← hh_one h h1]
  exact hh_strictMono h hw

theorem radial_ne {w₀ w : ℝ} (h : w₀ ≠ 0) (h1 : w₀ ^ 2 ≤ 1) (hw0 : w ≠ 0) (hw : w ^ 2 < 1) :
    AA w₀ w * deriv (AA w₀) w + BB w₀ w * deriv (BB w₀) w ≠ 0 := by
  rw [radial_eq h]
  have hr := rho_sq_lt_one h h1 hw
  have hrp := rho_pos h w
  have h4 : 0 < 1 - rho w₀ w ^ 4 := by nlinarith [pow_pos hrp 2]
  have hd := dh_pos h (w ^ 2)
  have hD : D (rho w₀ w) ^ 2 ≠ 0 := pow_ne_zero 2 (D_ne _)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hd.ne' hw0) h4.ne') hD

theorem deriv_kap_zero {w₀ : ℝ} (h : w₀ ≠ 0) : deriv (kap w₀) 0 = rsq w₀ / (4 * w₀) := by
  have hc : HasDerivAt (fun w : ℝ => cut (w₀ ^ 2) (w ^ 2))
      (-(deriv s₀ (4 * (0 : ℝ) ^ 2 / w₀ ^ 2 - 1) * (4 / w₀ ^ 2)) * (2 * 0)) 0 := by
    have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * 0) (0 : ℝ) := by
      simpa using hasDerivAt_pow 2 (0 : ℝ)
    exact HasDerivAt.comp (h₂ := cut (w₀ ^ 2)) (h := fun w : ℝ => w ^ 2) (0 : ℝ)
      (hasDerivAt_cut (w₀ ^ 2) ((0 : ℝ) ^ 2)) h2
  have hk := ((hasDerivAt_id' (0 : ℝ)).const_mul (rsq w₀ / (4 * w₀))).mul hc
  have hw : 0 < w₀ ^ 2 := by positivity
  have e : cut (w₀ ^ 2) 0 = 1 := cut_of_le hw (by positivity)
  have := hk.deriv
  refine Eq.trans ?_ (this.trans ?_)
  · rfl
  · simp [e]

theorem deriv_kap_of {w₀ w : ℝ} (h : w₀ ≠ 0) (hw : w₀ ^ 2 / 2 < w ^ 2) : deriv (kap w₀) w = 0 := by
  have hop : IsOpen {x : ℝ | w₀ ^ 2 / 2 < x ^ 2} :=
    isOpen_lt continuous_const (continuous_id.pow 2)
  have e : kap w₀ =ᶠ[𝓝 w] fun _ => 0 := by
    filter_upwards [hop.mem_nhds hw] with y hy using kap_of h (le_of_lt hy)
  rw [e.deriv_eq]; simp

/-- 断面曲線は正則である。 -/
theorem profile_ne {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (w : ℝ) :
    ¬ (deriv (AA w₀) w = 0 ∧ deriv (BB w₀) w = 0) := by
  rintro ⟨hA, hB⟩
  have hne := h0.ne'
  have hw1 : w₀ ^ 2 ≤ 1 := by nlinarith
  have hrp := rho_pos hne w
  by_cases hw0 : w = 0
  · -- 折り返しの点：κ′(0) > 0 で a(ρ(0)) > 0
    subst hw0
    rw [(hasDerivAt_AA hne 0).deriv] at hA
    rw [(hasDerivAt_BB hne 0).deriv] at hB
    have hv : vv w₀ 0 = 0 := by
      linear_combination (-(sin (kap w₀ 0))) * hA + (cos (kap w₀ 0)) * hB -
        vv w₀ 0 * sin_sq_add_cos_sq (kap w₀ 0)
    have hd : drho w₀ 0 = 0 := by simp [drho]
    simp only [vv, hd, mul_zero, zero_add, deriv_kap_zero hne] at hv
    have hk : 0 < rsq w₀ / (4 * w₀) := div_pos (rsq_pos hne) (by positivity)
    exact (mul_pos hk (aa_pos hrp)).ne' hv
  · by_cases hw : w ^ 2 < 1
    · exact radial_ne hne hw1 hw0 hw (by rw [hA, hB]; ring)
    · push Not at hw
      rw [(hasDerivAt_AA hne w).deriv] at hA
      rw [(hasDerivAt_BB hne w).deriv] at hB
      have hu : uu w₀ w = 0 := by
        linear_combination (cos (kap w₀ w)) * hA + (sin (kap w₀ w)) * hB -
          uu w₀ w * sin_sq_add_cos_sq (kap w₀ w)
      have hv : vv w₀ w = 0 := by
        linear_combination (-(sin (kap w₀ w))) * hA + (cos (kap w₀ w)) * hB -
          vv w₀ w * sin_sq_add_cos_sq (kap w₀ w)
      have hk : deriv (kap w₀) w = 0 := deriv_kap_of hne (by nlinarith)
      have hd : drho w₀ w ≠ 0 := by
        simp only [drho]
        exact div_ne_zero (mul_ne_zero (dh_pos hne _).ne' hw0) hrp.ne'
      simp only [uu, vv, hk, zero_mul, sub_zero, add_zero] at hu hv
      exact da_db_ne (rho w₀ w) ⟨(mul_eq_zero.mp hu).resolve_right hd,
        (mul_eq_zero.mp hv).resolve_right hd⟩

/-- B > 0。円は潰れない。 -/
theorem BB_pos {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (w : ℝ) : 0 < BB w₀ w := by
  have hne := h0.ne'
  have hr := rsq_pos hne
  have hrle : rsq w₀ ≤ w₀ ^ 2 / 8 := rsq_le
  have hw1 : w₀ ^ 2 ≤ 1 := by nlinarith
  have hk := abs_kap_le h0 w
  have hrp := rho_pos hne w
  have hρ2 : rsq w₀ ≤ rho w₀ w ^ 2 := by
    rw [rho_sq hne]; exact hh_ge_rsq hne (sq_nonneg w)
  set κ := kap w₀ w
  have hs : |sin κ| ≤ |κ| := Real.abs_sin_le_abs
  have hkle : |κ| ≤ 1 := by linarith
  have hc : 1 / 2 ≤ cos κ := by
    have := Real.one_sub_sq_div_two_le_cos (x := κ)
    have h2 : κ ^ 2 ≤ 1 := by
      rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hkle
    linarith
  have hs2 := (abs_le.mp hs).1
  have key : 0 < sin κ + rho w₀ w ^ 2 * cos κ := by
    have : rsq w₀ * (1 / 2) ≤ rho w₀ w ^ 2 * cos κ :=
      mul_le_mul hρ2 hc (by norm_num) (sq_nonneg _)
    have hkk := (abs_le.mp (hs.trans hk)).1
    linarith
  have e : BB w₀ w = aa (rho w₀ w) * (sin κ + rho w₀ w ^ 2 * cos κ) := by
    simp only [BB, bb_eq]
    ring
  rw [e]
  exact mul_pos (aa_pos hrp) key

/-! ### 面 Σ -/

/-- **定理 B の面 Σ**。 -/
def Sig (w₀ w v : ℝ) : V3 := sigmaOf (AA w₀) (BB w₀) (psi w₀) w v

/-- Σ の法線場 ∂Σ/∂v × ∂Σ/∂w。 -/
def Xf (w₀ w v : ℝ) : V3 :=
  cross (sigV (psi w₀ w) (BB w₀ w) v)
    (sigW (psi w₀ w) (AA w₀ w) (BB w₀ w) (deriv (AA w₀) w) (deriv (BB w₀) w) (deriv (psi w₀) w) v)

theorem hasDerivAt_Sig_v (w₀ w v : ℝ) :
    HasDerivAt (fun v => Sig w₀ w v) (sigV (psi w₀ w) (BB w₀ w) v) v :=
  hasDerivAt_sigma_v _ _ _ _ _

theorem hasDerivAt_Sig_w {w₀ : ℝ} (h : w₀ ≠ 0) (w v : ℝ) :
    HasDerivAt (fun w => Sig w₀ w v)
      (sigW (psi w₀ w) (AA w₀ w) (BB w₀ w) (deriv (AA w₀) w) (deriv (BB w₀) w)
        (deriv (psi w₀) w) v) w :=
  hasDerivAt_sigma_w ((contDiff_AA h).differentiable (by simp) w).hasDerivAt
    ((contDiff_BB h).differentiable (by simp) w).hasDerivAt
    ((contDiff_psi w₀).differentiable (by simp) w).hasDerivAt v

theorem contDiff_Sig {w₀ : ℝ} (h : w₀ ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => Sig w₀ p.1 p.2) := by
  have hA := contDiff_AA h
  have hB := contDiff_BB h
  have hψ := contDiff_psi w₀
  simp only [Sig, sigmaOf, rot2]
  fun_prop

theorem continuous_Xf {w₀ : ℝ} (h : w₀ ≠ 0) :
    Continuous (fun p : ℝ × ℝ => Xf w₀ p.1 p.2) := by
  have hA := (contDiff_AA h).continuous
  have hB := (contDiff_BB h).continuous
  have hψ := (contDiff_psi w₀).continuous
  have hdA : Continuous (deriv (AA w₀)) := (contDiff_AA h).continuous_deriv (by simp)
  have hdB : Continuous (deriv (BB w₀)) := (contDiff_BB h).continuous_deriv (by simp)
  have hdψ : Continuous (deriv (psi w₀)) := (contDiff_psi w₀).continuous_deriv (by simp)
  simp only [Xf, sigV, sigW, rot2, cross]
  fun_prop

/-- **首の補題の適用**：法線場は消えない。 -/
theorem Xf_ne {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (w v : ℝ) : Xf w₀ w v ≠ wp := by
  refine neck_lemma (BB_pos h0 h1 w).ne' (profile_ne h0 h1 w) ?_ v
  intro hd
  obtain ⟨h2, h3⟩ := deriv_psi_ne h0 hd
  have hw0 : w ≠ 0 := by
    have : 0 < w := by linarith
    exact this.ne'
  have hw2 : w ^ 2 < 1 := by nlinarith
  exact radial_ne h0.ne' (by nlinarith) hw0 hw2

theorem Sig_periodic (w₀ w v : ℝ) : Sig w₀ w (v + 2 * π) = Sig w₀ w v := by
  simp [Sig, sigmaOf]

/-! ### はめ込み -/

theorem fderiv_apply_of_partials {f : ℝ × ℝ → V3} {w v : ℝ} {W V : V3}
    (hf : DifferentiableAt ℝ f (w, v))
    (hw : HasDerivAt (fun w => f (w, v)) W w) (hv : HasDerivAt (fun v => f (w, v)) V v)
    (ξ : ℝ × ℝ) : fderiv ℝ f (w, v) ξ = ξ.1 • W + ξ.2 • V := by
  have h1 : fderiv ℝ f (w, v) (1, 0) = W := by
    have hl : HasDerivAt (fun x : ℝ => ((x, v) : ℝ × ℝ)) (1, 0) w :=
      (hasDerivAt_id' w).prodMk (hasDerivAt_const w v)
    have := hf.hasFDerivAt.comp_hasDerivAt w hl
    exact this.unique hw
  have h2 : fderiv ℝ f (w, v) (0, 1) = V := by
    have hl : HasDerivAt (fun x : ℝ => ((w, x) : ℝ × ℝ)) (0, 1) v :=
      (hasDerivAt_const v w).prodMk (hasDerivAt_id' v)
    have := hf.hasFDerivAt.comp_hasDerivAt v hl
    exact this.unique hv
  have e : ξ = ξ.1 • ((1, 0) : ℝ × ℝ) + ξ.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul, h1, h2]

theorem cross_add_smul (x y : ℝ) (V W : V3) (h : x • W + y • V = wp) :
    x • cross V W = wp ∧ y • cross V W = wp := by
  have h1 : x * W.1 + y * V.1 = 0 := congrArg Prod.fst h
  have h2 : x * W.2.1 + y * V.2.1 = 0 := congrArg (fun z : V3 => z.2.1) h
  have h3 : x * W.2.2 + y * V.2.2 = 0 := congrArg (fun z : V3 => z.2.2) h
  constructor
  · simp only [cross, wp]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.smul_fst, smul_eq_mul]; linear_combination V.2.1 * h3 - V.2.2 * h2
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination V.2.2 * h1 - V.1 * h3
    · simp only [Prod.smul_snd, smul_eq_mul]; linear_combination V.1 * h2 - V.2.1 * h1
  · simp only [cross, wp]
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · simp only [Prod.smul_fst, smul_eq_mul]; linear_combination W.2.2 * h2 - W.2.1 * h3
    · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      linear_combination W.1 * h3 - W.2.2 * h1
    · simp only [Prod.smul_snd, smul_eq_mul]; linear_combination W.2.1 * h1 - W.1 * h2

theorem smul_eq_wp_iff {x : ℝ} {u : V3} (hu : u ≠ wp) (h : x • u = wp) : x = 0 := by
  rcases smul_eq_zero.mp (show x • u = 0 from h) with h0 | h0
  · exact h0
  · exact absurd h0 hu

/-- 二つの偏導関数の外積が消えなければ、全微分は単射である。 -/
theorem injective_fderiv_of_cross {f : ℝ × ℝ → V3} {w v : ℝ} {W V : V3}
    (hf : DifferentiableAt ℝ f (w, v))
    (hw : HasDerivAt (fun w => f (w, v)) W w) (hv : HasDerivAt (fun v => f (w, v)) V v)
    (hX : cross V W ≠ wp) : Function.Injective (fderiv ℝ f (w, v)) := by
  refine (injective_iff_map_eq_zero _).mpr fun ξ hξ => ?_
  rw [fderiv_apply_of_partials hf hw hv] at hξ
  obtain ⟨h1, h2⟩ := cross_add_smul ξ.1 ξ.2 V W hξ
  have e1 := smul_eq_wp_iff hX h1
  have e2 := smul_eq_wp_iff hX h2
  exact Prod.ext e1 e2

/-- **B1**：Σ ははめ込みである。 -/
theorem Sig_immersion {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => Sig w₀ p.1 p.2) p) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => Sig w₀ p.1 p.2) p :=
    (contDiff_Sig h0.ne').differentiable (by simp) p
  obtain ⟨w, v⟩ := p
  exact injective_fderiv_of_cross hd (hasDerivAt_Sig_w h0.ne' w v) (hasDerivAt_Sig_v w₀ w v)
    (Xf_ne h0 h1 w v)

/-! ### 端の一致 -/

theorem cross_Tv_Tw_smul' (w v : ℝ) : cross (Tv w v) (Tw w v) = (w ^ 3 / D w ^ 3) • N w v := by
  rw [cross_Tv_Tw]
  rfl

theorem sq_of_right {w₀ w : ℝ} (h0 : 0 < w₀) (hw : w₀ * (4 / 5) < w) : w₀ ^ 2 / 2 < w ^ 2 := by
  have : (w₀ * (4 / 5)) ^ 2 < w ^ 2 := pow_lt_pow_left₀ hw (by positivity) (by norm_num)
  nlinarith [pow_pos h0 2]

theorem sq_of_left {w₀ w : ℝ} (h0 : 0 < w₀) (hw : w < -(w₀ * (4 / 5))) : w₀ ^ 2 / 2 < w ^ 2 := by
  have h := sq_of_right h0 (w := -w) (by linarith)
  simpa using h

/-- **B2**：右の端で Σ = G。 -/
theorem Sig_right {w₀ w : ℝ} (h0 : 0 < w₀) (hw : w₀ * (4 / 5) < w) (v : ℝ) :
    Sig w₀ w v = G w v := by
  have hs := (sq_of_right h0 hw).le
  have hpos : 0 < w := by
    have : 0 < w₀ * (4 / 5) := by positivity
    linarith
  have hψ : psi w₀ w = 0 := psi_of_ge h0 (by linarith)
  simp only [Sig, sigmaOf, hψ, rot2_zero, AA_of h0.ne' hs, BB_of h0.ne' hs, abs_of_pos hpos]
  rw [G_eq_aa_bb]

/-- **B2**：左の端で Σ(w, v) = G(w, π − v)。 -/
theorem Sig_left {w₀ w : ℝ} (h0 : 0 < w₀) (hw : w < -(w₀ * (4 / 5))) (v : ℝ) :
    Sig w₀ w v = G w (π - v) := by
  have hs := (sq_of_left h0 hw).le
  have hneg : w < 0 := by
    have : 0 < w₀ * (4 / 5) := by positivity
    linarith
  have hψ : psi w₀ w = π := psi_of_le h0 (by nlinarith)
  simp only [Sig, sigmaOf, hψ, rot2_pi, AA_of h0.ne' hs, BB_of h0.ne' hs, abs_of_neg hneg]
  rw [G_eq_aa_bb, aa_neg, bb_neg, cos_pi_sub, sin_pi_sub]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- 右の端で法線場は N の正の倍。 -/
theorem Xf_right {w₀ w : ℝ} (h0 : 0 < w₀) (hw : w₀ * (4 / 5) < w) (v : ℝ) :
    Xf w₀ w v = (w ^ 3 / D w ^ 3) • N w v := by
  have hop : IsOpen (Ioi (w₀ * (4 / 5))) := isOpen_Ioi
  have e1 : sigV (psi w₀ w) (BB w₀ w) v = Tv w v := by
    have h1 := hasDerivAt_Sig_v w₀ w v
    have h2 : (fun v => Sig w₀ w v) = fun v => G w v := funext fun v => Sig_right h0 hw v
    rw [h2] at h1
    exact h1.unique (hasDerivAt_G_v w v)
  have e2 := (hasDerivAt_Sig_w h0.ne' w v).unique
    ((hasDerivAt_G_w w v).congr_of_eventuallyEq (by
      filter_upwards [hop.mem_nhds hw] with y hy using Sig_right h0 hy v))
  simp only [Xf, e1, e2]
  exact cross_Tv_Tw_smul' w v

/-- 左の端で法線場は N(w, π − v) の正の倍である（w < 0 なので −w³ > 0）。 -/
theorem Xf_left {w₀ w : ℝ} (h0 : 0 < w₀) (hw : w < -(w₀ * (4 / 5))) (v : ℝ) :
    Xf w₀ w v = (-(w ^ 3 / D w ^ 3)) • N w (π - v) := by
  have hop : IsOpen (Iio (-(w₀ * (4 / 5)))) := isOpen_Iio
  have e1 : sigV (psi w₀ w) (BB w₀ w) v = -Tv w (π - v) := by
    have h1 := hasDerivAt_Sig_v w₀ w v
    have h2 : (fun v => Sig w₀ w v) = fun v => G w (π - v) := funext fun v => Sig_left h0 hw v
    rw [h2] at h1
    have h3 : HasDerivAt (fun v => π - v) (-1) v := by
      simpa using (hasDerivAt_id' v).const_sub π
    have h4 := (hasDerivAt_G_v w (π - v)).scomp v h3
    have h5 := h1.unique h4
    rw [h5]
    simp
  have e2 := (hasDerivAt_Sig_w h0.ne' w v).unique
    ((hasDerivAt_G_w w (π - v)).congr_of_eventuallyEq (by
      filter_upwards [hop.mem_nhds hw] with y hy using Sig_left h0 hy v))
  simp only [Xf, e1, e2, cross_neg_left]
  rw [cross_Tv_Tw_smul', neg_smul]

/-! ### 半径 -/

theorem nsq_sigmaOf (A B ψ : ℝ → ℝ) (w v : ℝ) :
    nsq (sigmaOf A B ψ w v) = A w ^ 2 + B w ^ 2 := by
  unfold sigmaOf
  rw [nsq_rot2]
  simp only [nsq, dot]
  linear_combination (B w ^ 2) * sin_sq_add_cos_sq v

/-- |Σ|² は v によらない。 -/
theorem nsq_Sig {w₀ : ℝ} (h : w₀ ≠ 0) (w v : ℝ) : nsq (Sig w₀ w v) = Rad (hh w₀ (w ^ 2)) := by
  simp only [Sig, nsq_sigmaOf, AA_sq_add h]

/-- 半径は |w| ≤ 1 で |w| について狭義単調である。 -/
theorem nsq_Sig_lt {w₀ : ℝ} (h : w₀ ≠ 0) (h1 : w₀ ^ 2 ≤ 1) {w₁ w₂ : ℝ} (hlt : |w₁| < |w₂|)
    (hle : |w₂| ≤ 1) (v₁ v₂ : ℝ) : nsq (Sig w₀ w₁ v₁) < nsq (Sig w₀ w₂ v₂) := by
  rw [nsq_Sig h, nsq_Sig h]
  have hs : w₁ ^ 2 < w₂ ^ 2 := sq_lt_sq.mpr hlt
  have hs2 : w₂ ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hle
  refine Rad_lt (hh_pos h (sq_nonneg _)).le (hh_strictMono h hs) ?_
  rw [← hh_one h h1]
  exact (hh_strictMono h).monotone hs2

/-- Σ は ℘ を通らない。 -/
theorem Sig_ne_wp {w₀ : ℝ} (h : w₀ ≠ 0) (w v : ℝ) : Sig w₀ w v ≠ wp := by
  intro he
  have h1 := nsq_Sig h w v
  rw [he] at h1
  have h2 := Rad_pos (hh_pos h (sq_nonneg w))
  rw [← h1] at h2
  simp [nsq, dot, wp] at h2

/-- 首 |w| ≤ w₀ は半径 w₀ の球の中にある。 -/
theorem nsq_Sig_neck {w₀ w : ℝ} (h0 : 0 < w₀) (hw : |w| ≤ w₀) (v : ℝ) :
    nsq (Sig w₀ w v) < w₀ ^ 2 := by
  have hne := h0.ne'
  rw [nsq_Sig hne]
  have hs : w ^ 2 ≤ w₀ ^ 2 := by
    rw [← sq_abs w]
    exact pow_le_pow_left₀ (abs_nonneg _) hw 2
  have hm : hh w₀ (w ^ 2) ≤ w₀ ^ 2 := by
    calc hh w₀ (w ^ 2) ≤ hh w₀ (w₀ ^ 2) := (hh_strictMono hne).monotone hs
      _ = w₀ ^ 2 := hh_of_ge hne (by nlinarith [pow_pos h0 2])
  exact (Rad_lt_self (hh_pos hne (sq_nonneg w))).trans_le hm

/-- 首の中央（w = 0）の円。 -/
theorem Sig_zero {w₀ : ℝ} (h0 : 0 < w₀) (v : ℝ) :
    Sig w₀ 0 v = (-AA w₀ 0, BB w₀ 0 * cos v, -(BB w₀ 0 * sin v)) := by
  have hψ : psi w₀ 0 = π := psi_of_le h0 (by positivity)
  simp only [Sig, sigmaOf, hψ, rot2_pi]

end Zeno.Model
