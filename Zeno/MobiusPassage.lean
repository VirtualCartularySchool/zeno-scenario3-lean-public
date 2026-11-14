/-
# Zeno.MobiusPassage : 射影平面の面の上の走者（読み M2 の定理）

競走 R と段数 n₁ ≥ 1 について、c = rⁿ¹、芯の半径 k = c/16、芯の窓 δ = rk/2、
ホーンの端 w₀ = (1 + r)k/4、近さ ε = k³/32 とする。亀は v = 0、アキレスは
窓の外できりもみ v = θ(w)、窓の内側（|w| ≤ c/2）で v = π/2 + 2πn₁ を歩く。
-/
import Zeno.MobiusRun

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### パラメータ -/

namespace Race

variable (R : Race)

def mc (n₁ : ℕ) : ℝ := R.r ^ n₁
def mkc (n₁ : ℕ) : ℝ := R.mc n₁ / 16
def mδ (n₁ : ℕ) : ℝ := R.r * R.mkc n₁ / 2
def mw (n₁ : ℕ) : ℝ := (1 + R.r) * R.mkc n₁ / 4
def mε (n₁ : ℕ) : ℝ := R.mkc n₁ ^ 3 / 32

variable {R} {n₁ : ℕ}

theorem mc_pos : 0 < R.mc n₁ := pow_pos R.r_pos n₁

theorem mc_le (hn : 1 ≤ n₁) : R.mc n₁ ≤ R.r := by
  unfold mc
  calc R.r ^ n₁ ≤ R.r ^ 1 := pow_le_pow_of_le_one R.r_pos.le R.r_lt_one.le hn
    _ = R.r := pow_one _

theorem mkc_pos : 0 < R.mkc n₁ := by unfold mkc; have := R.mc_pos (n₁ := n₁); positivity

theorem mkc_le (hn : 1 ≤ n₁) : R.mkc n₁ ≤ 1 / 16 := by
  unfold mkc; have := R.mc_le hn; have := R.r_lt_one; linarith

theorem mok (hn : 1 ≤ n₁) : MobOK (R.mkc n₁) (R.mδ n₁) (R.mw n₁) where
  k_pos := R.mkc_pos
  k_le := by have := R.mkc_le hn; linarith
  δ_pos := by unfold mδ; have := R.mkc_pos (n₁ := n₁); have := R.r_pos; positivity
  δ_lt := by
    unfold mδ mw; have := R.mkc_pos (n₁ := n₁); have := R.r_lt_one; nlinarith
  w₀_le := by unfold mw; have := R.mkc_pos (n₁ := n₁); have := R.r_lt_one; nlinarith

theorem rw_le_δ : R.r * R.mw n₁ ≤ R.mδ n₁ := by
  unfold mw mδ
  have hk := R.mkc_pos (n₁ := n₁)
  have hr := R.r_pos
  have hr1 := R.r_lt_one
  calc R.r * ((1 + R.r) * R.mkc n₁ / 4) = (R.r * R.mkc n₁ / 2) * ((1 + R.r) / 2) := by ring
    _ ≤ (R.r * R.mkc n₁ / 2) * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = R.r * R.mkc n₁ / 2 := mul_one _

theorem mε_pos : 0 < R.mε n₁ := by unfold mε; have := R.mkc_pos (n₁ := n₁); positivity

theorem mε_lt : R.mε n₁ < R.mkc n₁ := by
  unfold mε
  have hk := R.mkc_pos (n₁ := n₁)
  have hk1 : R.mkc n₁ ≤ 1 / 16 := by
    unfold mkc; have := R.mc_pos (n₁ := n₁)
    have : R.mc n₁ ≤ 1 := pow_le_one₀ R.r_pos.le R.r_lt_one.le
    linarith
  have : R.mkc n₁ ^ 2 ≤ 1 := by nlinarith
  nlinarith

end Race

/-! ### アキレスの角度 -/

/-- 窓の内側（|w| ≤ c/2）で 1、外側（|w| ≥ c）で 0。 -/
def ellM (c w : ℝ) : ℝ := 1 - s₀ ((w ^ 2 - (c / 2) ^ 2) / (c ^ 2 - (c / 2) ^ 2))

/-- アキレスの角度：窓の外できりもみ θ(w)、窓の内側で π/2 + 2πn₁。 -/
def VAM (r c : ℝ) (n₁ : ℕ) (w : ℝ) : ℝ :=
  (1 - ellM c w) * theta r w + ellM c w * (π / 2 + n₁ * (2 * π))

theorem ellM_den {c : ℝ} (hc : 0 < c) : 0 < c ^ 2 - (c / 2) ^ 2 := by nlinarith

theorem ellM_inner {c w : ℝ} (hc : 0 < c) (hw : |w| ≤ c / 2) : ellM c w = 1 := by
  unfold ellM
  have hw2 : w ^ 2 ≤ (c / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg w) hw 2
  rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (ellM_den hc).le), sub_zero]

theorem ellM_outer {c w : ℝ} (hc : 0 < c) (hw : c ≤ |w|) : ellM c w = 0 := by
  unfold ellM
  have hw2 : c ^ 2 ≤ w ^ 2 := by
    have := pow_le_pow_left₀ hc.le hw 2; rwa [sq_abs] at this
  rw [Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ (ellM_den hc)]; linarith), sub_self]

theorem VAM_inner {r c : ℝ} (n₁ : ℕ) {w : ℝ} (hc : 0 < c) (hw : |w| ≤ c / 2) :
    VAM r c n₁ w = π / 2 + n₁ * (2 * π) := by
  unfold VAM; rw [ellM_inner hc hw]; ring

theorem VAM_outer {r c : ℝ} (n₁ : ℕ) {w : ℝ} (hc : 0 < c) (hw : c ≤ |w|) :
    VAM r c n₁ w = theta r w := by
  unfold VAM; rw [ellM_outer hc hw]; ring

theorem contDiff_VAM (r : ℝ) {c : ℝ} (hc : 0 < c) (n₁ : ℕ) : ContDiff ℝ ∞ (VAM r c n₁) := by
  have hs : ContDiff ℝ ∞ s₀ := Real.smoothTransition.contDiff
  have hell : ContDiff ℝ ∞ (ellM c) := by
    unfold ellM
    exact contDiff_const.sub (hs.comp (((contDiff_id.pow 2).sub contDiff_const).div_const _))
  refine contDiff_iff_contDiffAt.mpr fun w => ?_
  by_cases hw : |w| < c / 2
  · have heq : VAM r c n₁ =ᶠ[𝓝 w] fun _ => π / 2 + n₁ * (2 * π) := by
      have hop : ∀ᶠ w' in 𝓝 w, |w'| < c / 2 :=
        continuous_abs.continuousAt.eventually (gt_mem_nhds hw)
      filter_upwards [hop] with w' hw'
      exact VAM_inner n₁ hc hw'.le
    exact contDiffAt_const.congr_of_eventuallyEq heq
  · have hw0 : w ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hw; exact hw (by linarith)
    have hth : ContDiffAt ℝ ∞ (theta r) w := by
      have e : theta r = fun w => 2 * π * (log w / log r) := by
        funext x; simp [theta, Real.log_abs]
      rw [e]
      exact contDiffAt_const.mul ((Real.contDiffAt_log.mpr hw0).div_const _)
    unfold VAM
    exact ((contDiffAt_const.sub hell.contDiffAt).mul hth).add
      (hell.contDiffAt.mul contDiffAt_const)

theorem theta_neg (r w : ℝ) : theta r (-w) = theta r w := by simp [theta, abs_neg]

/-! ### 特別な点の座標 -/

theorem mobC_v0 (k w : ℝ) : mobC k w 0 = (-w, k, 0) := by simp [mobC]

theorem mobC_vh (k w : ℝ) : mobC k w (π / 2) = (0, -(k + w), 0) := by
  simp only [mobC, cos_pi_div_two, sin_pi_div_two, mul_zero, neg_zero, mul_one,
    show 2 * (π / 2) = π by ring, cos_pi, sin_pi]
  refine Prod.ext rfl (Prod.ext ?_ rfl); simp only; ring

theorem foldG_v0 (w : ℝ) : foldG w 0 = (|w| / D w, w ^ 3 / D w, 0) := by simp [foldG]

theorem foldG_vh (w : ℝ) : foldG w (π / 2) = (|w| / D w, 0, w ^ 3 / D w) := by
  simp [foldG, cos_pi_div_two, sin_pi_div_two]

theorem abs_coord_le_dist (x y : V3) :
    |x.1 - y.1| ≤ dist x y ∧ |x.2.1 - y.2.1| ≤ dist x y ∧ |x.2.2 - y.2.2| ≤ dist x y := by
  have h1 : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h2 : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h3 : dist x.2.1 y.2.1 ≤ dist x.2 y.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h4 : dist x.2.2 y.2.2 ≤ dist x.2 y.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
  rw [Real.dist_eq] at h1 h3 h4
  exact ⟨h1, h3.trans h2, h4.trans h2⟩

theorem D_le_two {w : ℝ} (hw : |w| ≤ 1) : D w ≤ 2 := by
  unfold D
  have : w ^ 4 ≤ 1 := by
    rw [show w ^ 4 = |w| ^ 4 by rw [← abs_pow, abs_of_nonneg (by positivity)]]
    exact pow_le_one₀ (abs_nonneg _) hw
  linarith

theorem abs_div_D_ge {w : ℝ} (hw : |w| ≤ 1) : |w| / 2 ≤ |w| / D w := by
  exact div_le_div_of_nonneg_left (abs_nonneg w) (D_pos w) (D_le_two hw)

theorem bsM_Ypp (k δ w₀ : ℝ) {w : ℝ} (hw : w ≠ 0) (h2 : w ^ 2 ≤ 2) (v : ℝ) :
    bsM k δ w₀ (Ypp (w, v)) = foldG w v + sgC δ w₀ (1 / w ^ 2) • (mobC k w v - foldG w v) := by
  unfold bsM; rw [planeG_Ypp hw h2, mobCy_Ypp k hw, tau_Ypp hw]

/-! ### 非衝突の核 -/

theorem nsq_le_sq_of_foldG (w v : ℝ) : nsq (foldG w v) ≤ w ^ 2 := by
  rw [nsq_foldG]
  exact div_le_self (sq_nonneg _) (by unfold D; nlinarith [pow_nonneg (sq_nonneg w) 2])

theorem abs_div_D_le (w : ℝ) : |w| / D w ≤ |w| :=
  div_le_self (abs_nonneg _) (by unfold D; nlinarith [pow_nonneg (sq_nonneg w) 2])

/-- 芯と芯：q₂ が k と −(k + w_A)。 -/
theorem sep_core_core {k wT wA : ℝ} (hA : |wA| < k) :
    mobC k wT 0 ≠ mobC k wA (π / 2) := by
  rw [mobC_v0, mobC_vh]
  intro he
  have h1 := congrArg (fun z : V3 => z.2.1) he
  simp only at h1
  have := neg_le_abs wA
  have := abs_nonneg wA
  linarith

/-- 芯と中間：亀の q₂ = k、アキレスの基底の q₂ ≤ 0。 -/
theorem sep_core_mid {k ε σ wA : ℝ} {p : V3} (hkw : 0 < k + wA) (hσ : 0 ≤ σ) (hεk : ε < k)
    (wT : ℝ) (hd : dist p ((|wA| / D wA, 0, wA ^ 3 / D wA) +
        σ • ((0, -(k + wA), 0) - (|wA| / D wA, 0, wA ^ 3 / D wA))) ≤ ε) :
    ((-wT, k, 0) : V3) ≠ p := by
  intro he
  rw [← he] at hd
  have h2 := (abs_coord_le_dist _ _).2.1.trans hd
  simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul] at h2
  have h3 := (le_abs_self _).trans h2
  nlinarith [mul_nonneg hσ hkw.le]

/-- 芯とホーン。 -/
theorem sep_core_horn {k δ wT wA v : ℝ} (hT : |wT| ≤ δ) (hδk : δ < k / 2) (hA1 : |wA| ≤ 1) :
    ((-wT, k, 0) : V3) ≠ foldG wA v := by
  intro he
  by_cases hAk : |wA| < k
  · have h1 := congrArg nsq he
    have h2 : nsq ((-wT, k, 0) : V3) = wT ^ 2 + k ^ 2 := by simp [nsq, dot]; ring
    rw [h2] at h1
    have h3 := nsq_le_sq_of_foldG wA v
    have h4 : wA ^ 2 < k ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ hAk (abs_nonneg _) (by norm_num)
    nlinarith [sq_nonneg wT]
  · rw [not_lt] at hAk
    have h1 := congrArg Prod.fst he
    simp only [foldG] at h1
    have h2 := abs_div_D_ge hA1
    have h3 : |(-wT)| ≤ δ := by rw [abs_neg]; exact hT
    rw [h1] at h3
    have h4 : |wA| / D wA ≤ δ := (le_abs_self _).trans h3
    linarith

/-- 中間とホーン（アキレスが窓の内側：q₃ で分ける）。 -/
theorem sep_mid_horn_q3 {k ε σ wT wA : ℝ} {p : V3} (hk : 0 < k) (hA2 : k / 2 < |wA|)
    (hA1 : |wA| ≤ 1) (hε : ε < k ^ 3 / 16)
    (hd : dist p ((|wT| / D wT, wT ^ 3 / D wT, 0) +
        σ • ((-wT, k, 0) - (|wT| / D wT, wT ^ 3 / D wT, 0))) ≤ ε) :
    p ≠ foldG wA (π / 2) := by
  rw [foldG_vh]
  intro he
  rw [he] at hd
  have h3 := (abs_coord_le_dist _ _).2.2.trans hd
  simp only [Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul, sub_zero, mul_zero,
    add_zero] at h3
  have hb : k ^ 3 / 16 ≤ |wA ^ 3 / D wA| := by
    rw [abs_div, abs_of_pos (D_pos wA), abs_pow]
    have h5 : (k / 2) ^ 3 ≤ |wA| ^ 3 := pow_le_pow_left₀ (by linarith) hA2.le 3
    rw [le_div_iff₀ (D_pos wA)]
    nlinarith [D_le_two hA1, pow_pos hk 3]
  linarith

/-- 中間とホーン（アキレスが窓の外：q₁ で分ける）。 -/
theorem sep_mid_horn_q1 {k ε σ wT wA w₀ v : ℝ} {p : V3} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hT : |wT| < w₀) (hA1 : |wA| ≤ 1) (hgap : w₀ + ε < |wA| / 2)
    (hd : dist p ((|wT| / D wT, wT ^ 3 / D wT, 0) +
        σ • ((-wT, k, 0) - (|wT| / D wT, wT ^ 3 / D wT, 0))) ≤ ε) :
    p ≠ foldG wA v := by
  intro he
  rw [he] at hd
  have h3 := (abs_coord_le_dist _ _).1.trans hd
  simp only [foldG, Prod.smul_mk, Prod.mk_add_mk, Prod.mk_sub_mk, smul_eq_mul] at h3
  have h4 := abs_div_D_ge hA1
  have h5 := abs_div_D_le wT
  have h7 : 0 ≤ |wT| / D wT := div_nonneg (abs_nonneg _) (D_pos wT).le
  have h6 : |(|wT| / D wT + σ * (-wT - |wT| / D wT))| ≤ |wT| := by
    rw [abs_le]
    have := neg_abs_le wT
    have := le_abs_self wT
    constructor <;> nlinarith
  have h8 := abs_sub_abs_le_abs_sub (|wA| / D wA) (|wT| / D wT + σ * (-wT - |wT| / D wT))
  rw [abs_of_nonneg (div_nonneg (abs_nonneg _) (D_pos wA).le)] at h8
  linarith

section Sep

variable {R : Race} {n₁ : ℕ} {S X : ℝ → ℝ → V3}

local notation "cc" => R.mc n₁
local notation "kk" => R.mkc n₁
local notation "dd" => R.mδ n₁
local notation "ww" => R.mw n₁
local notation "ee" => R.mε n₁

theorem mob_A_inner (h : IsMobiusSurface kk dd ww ee S X) {w : ℝ}
    (hw : |w| ≤ cc / 2) : S w (VAM R.r cc n₁ w) = S w (π / 2) := by
  rw [VAM_inner n₁ R.mc_pos hw, h.periodic_nat]

theorem foldG_inner (w : ℝ) (n : ℕ) : foldG w (π / 2 + n * (2 * π)) = foldG w (π / 2) := by
  simp only [foldG]; rw [cos_add_nat_mul_two_pi, sin_add_nat_mul_two_pi]

/-- **非衝突の核**：|w_T| ≤ r|w_A|、|w_A| ≤ 1 なら、亀の点とアキレスの点は異なる。 -/
theorem mob_sep (hn : 1 ≤ n₁) (h : IsMobiusSurface kk dd ww ee S X) {wT wA : ℝ}
    (hTA : |wT| ≤ R.r * |wA|) (hA1 : |wA| ≤ 1) : S wT 0 ≠ S wA (VAM R.r cc n₁ wA) := by
  have hok := R.mok hn
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hk := R.mkc_pos (n₁ := n₁)
  have hc := R.mc_pos (n₁ := n₁)
  have hck : cc = 16 * kk := by simp only [Race.mkc]; ring
  have hδ : dd = R.r * kk / 2 := rfl
  have hεk := R.mε_lt (n₁ := n₁)
  have hrw := R.rw_le_δ (n₁ := n₁)
  have hk1 : kk ≤ 1 / 16 := R.mkc_le hn
  have hdk : dd < kk / 2 := by rw [hδ]; nlinarith
  have hw0le := hok.w₀_le
  have hT1 : |wT| ≤ |wA| := hTA.trans (by nlinarith [abs_nonneg wA])
  have hεsmall : ee < kk ^ 3 / 16 := by
    have : ee = kk ^ 3 / 32 := rfl
    rw [this]; have := pow_pos hk 3; linarith
  by_cases hA : |wA| ≤ dd
  · have hT : |wT| ≤ dd := hT1.trans hA
    rw [mob_A_inner h (by linarith [hok.δ_lt]), h.core _ _ hT, h.core _ _ hA]
    exact sep_core_core (by linarith)
  by_cases hA' : |wA| < ww
  · have hT : |wT| ≤ dd := hTA.trans (by nlinarith [abs_nonneg wA])
    have hwA0 : wA ≠ 0 := by intro h0; rw [h0, abs_zero] at hA; exact hA hok.δ_pos.le
    have hsq : wA ^ 2 ≤ 2 := by nlinarith [sq_abs wA, abs_nonneg wA]
    rw [mob_A_inner h (by linarith [hok.δ_lt]), h.core _ _ hT, mobC_v0]
    have hdist := h.near wA (π / 2) hwA0
    rw [bsM_Ypp _ _ _ hwA0 hsq, mobC_vh, foldG_vh] at hdist
    have hkw : 0 < kk + wA := by have := neg_abs_le wA; linarith
    exact sep_core_mid hkw (stg_nonneg _ _ _) hεk wT hdist
  rw [not_lt] at hA'
  have hwA0 : wA ≠ 0 := by intro h0; rw [h0, abs_zero] at hA'; linarith [hok.w₀_pos]
  have hsqA : wA ^ 2 ≤ 2 := by nlinarith [sq_abs wA, abs_nonneg wA]
  rw [h.horn _ _ hA' hsqA]
  by_cases hT : |wT| ≤ dd
  · rw [h.core _ _ hT, mobC_v0]
    exact sep_core_horn hT hdk hA1
  by_cases hT' : |wT| < ww
  · have hwT0 : wT ≠ 0 := by intro h0; rw [h0, abs_zero] at hT; exact hT hok.δ_pos.le
    have hsqT : wT ^ 2 ≤ 2 := by nlinarith [sq_abs wT, abs_nonneg wT]
    have hdist := h.near wT 0 hwT0
    rw [bsM_Ypp _ _ _ hwT0 hsqT, mobC_v0, foldG_v0] at hdist
    have hA2 : kk / 2 < |wA| := by
      rw [not_le] at hT
      have h1 : dd < R.r * |wA| := lt_of_lt_of_le hT hTA
      rw [hδ] at h1
      nlinarith
    by_cases hAc : |wA| < cc / 2
    · rw [VAM_inner n₁ hc hAc.le, foldG_inner]
      exact sep_mid_horn_q3 hk hA2 hA1 hεsmall hdist
    · rw [not_lt] at hAc
      refine sep_mid_horn_q1 (stg_nonneg _ _ _) (stg_le_one _ _ _) hT' hA1 ?_ hdist
      rw [hck] at hAc
      linarith
  rw [not_lt] at hT'
  have hsqT : wT ^ 2 ≤ 2 := by nlinarith [sq_abs wT, abs_nonneg wT, hT1]
  rw [h.horn _ _ hT' hsqT]
  intro he
  have h1 := congrArg nsq he
  rw [nsq_foldG, nsq_foldG, ← nsq_G wT 0, ← nsq_G wA (VAM R.r cc n₁ wA)] at h1
  have hlt : |wT| < |wA| := by
    have : 0 < |wA| := abs_pos.mpr hwA0
    nlinarith
  exact (nsq_G_lt hlt hA1 0 _).ne h1

end Sep

/-! ### 窓の中の大きさ -/

theorem nsq_mobC_le {k : ℝ} (hk : 0 ≤ k) (w v : ℝ) : nsq (mobC k w v) ≤ w ^ 2 + (k + |w|) ^ 2 := by
  have e : nsq (mobC k w v) = (w * cos v) ^ 2 + (k + w * sin v) ^ 2 := by
    simp only [nsq, dot, mobC]
    linear_combination (k + w * sin v) ^ 2 * sin_sq_add_cos_sq (2 * v)
  rw [e]
  have h1 : (w * cos v) ^ 2 ≤ w ^ 2 := by
    rw [mul_pow]; nlinarith [cos_sq_le_one v, sq_nonneg w]
  have h2 : |w * sin v| ≤ |w| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg w) (abs_sin_le_one v)
  have h3 : (k + w * sin v) ^ 2 ≤ (|k| + |w|) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ((abs_add_le _ _).trans (by linarith)) 2
  rw [abs_of_nonneg hk] at h3
  linarith

theorem nsq_convex (a b : V3) {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1) :
    nsq (a + σ • (b - a)) ≤ (1 - σ) * nsq a + σ * nsq b := by
  have e : (1 - σ) * nsq a + σ * nsq b - nsq (a + σ • (b - a)) = σ * (1 - σ) * nsq (b - a) := by
    simp only [nsq, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
      Prod.snd_sub, smul_eq_mul]
    ring
  have hn : 0 ≤ nsq (b - a) := by
    simp only [nsq, dot]; nlinarith [mul_self_nonneg (b - a).1, mul_self_nonneg (b - a).2.1,
      mul_self_nonneg (b - a).2.2]
  nlinarith [mul_nonneg (mul_nonneg h0 (sub_nonneg.mpr h1)) hn]

theorem nsq_le_of_dist3 {p q : V3} {ε : ℝ} (h : dist p q ≤ ε) : nsq (p - q) ≤ 3 * ε ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := abs_coord_le_dist p q
  have e1 : (p.1 - q.1) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h) 2
  have e2 : (p.2.1 - q.2.1) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h2.trans h) 2
  have e3 : (p.2.2 - q.2.2) ^ 2 ≤ ε ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (h3.trans h) 2
  simp only [nsq, dot, Prod.fst_sub, Prod.snd_sub]
  nlinarith

theorem nsq_add_le (a b : V3) : nsq (a + b) ≤ 2 * nsq a + 2 * nsq b := by
  simp only [nsq, dot, Prod.fst_add, Prod.snd_add]
  nlinarith [sq_nonneg (a.1 - b.1), sq_nonneg (a.2.1 - b.2.1), sq_nonneg (a.2.2 - b.2.2)]

section Window

variable {R : Race} {n₁ : ℕ} {S X : ℝ → ℝ → V3}

local notation "cc" => R.mc n₁
local notation "kk" => R.mkc n₁
local notation "dd" => R.mδ n₁
local notation "ww" => R.mw n₁
local notation "ee" => R.mε n₁

/-- **窓の中では ℘ の半径 c の球の中にある**。 -/
theorem mob_window (hn : 1 ≤ n₁) (h : IsMobiusSurface kk dd ww ee S X) {w : ℝ} (hw : |w| < cc)
    (hw1 : |w| ≤ 1) (v : ℝ) : nsq (S w v) < cc ^ 2 := by
  have hok := R.mok hn
  have hk := R.mkc_pos (n₁ := n₁)
  have hck : cc = 16 * kk := by simp only [Race.mkc]; ring
  have hεk := R.mε_lt (n₁ := n₁)
  have hε0 := R.mε_pos (n₁ := n₁)
  have hdk : dd < kk / 2 := by
    have : dd = R.r * kk / 2 := rfl
    rw [this]; have := R.r_lt_one; nlinarith
  have hw0le := hok.w₀_le
  by_cases hA : |w| ≤ dd
  · rw [h.core _ _ hA]
    have := nsq_mobC_le hk.le w v
    have h2 : w ^ 2 ≤ dd ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA 2
    have h3 : (kk + |w|) ^ 2 ≤ (kk + dd) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [hck]; nlinarith [hok.δ_pos]
  by_cases hA' : |w| < ww
  · have hw0 : w ≠ 0 := by intro h0; rw [h0, abs_zero] at hA; exact hA hok.δ_pos.le
    have hsq : w ^ 2 ≤ 2 := by nlinarith [sq_abs w, abs_nonneg w]
    have hd := h.near w v hw0
    rw [bsM_Ypp _ _ _ hw0 hsq] at hd
    have h1 := nsq_le_of_dist3 hd
    have h2 := nsq_convex (foldG w v) (mobC kk w v) (stg_nonneg _ _ _) (stg_le_one _ _ _)
      (σ := sgC dd ww (1 / w ^ 2))
    have h3 := nsq_le_sq_of_foldG w v
    have h4 := nsq_mobC_le hk.le w v
    have hb : nsq (foldG w v + sgC dd ww (1 / w ^ 2) • (mobC kk w v - foldG w v)) ≤
        w ^ 2 + (kk + |w|) ^ 2 := by
      have hσ0 := stg_nonneg (mT0 ww + 3 * mDl dd ww) (mDl dd ww) (1 / w ^ 2)
      have hσ1 := stg_le_one (mT0 ww + 3 * mDl dd ww) (mDl dd ww) (1 / w ^ 2)
      have : (1 - sgC dd ww (1 / w ^ 2)) * nsq (foldG w v) + sgC dd ww (1 / w ^ 2) * nsq (mobC kk w v)
          ≤ w ^ 2 + (kk + |w|) ^ 2 := by
        have hp : 0 ≤ (kk + |w|) ^ 2 := sq_nonneg _
        have : sgC dd ww (1 / w ^ 2) = stg (mT0 ww + 3 * mDl dd ww) (mDl dd ww) (1 / w ^ 2) := rfl
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_left h3 (sub_nonneg.mpr hσ1),
          mul_le_mul_of_nonneg_left h4 hσ0]
      linarith
    have h5 := nsq_add_le (foldG w v + sgC dd ww (1 / w ^ 2) • (mobC kk w v - foldG w v))
      (S w v - (foldG w v + sgC dd ww (1 / w ^ 2) • (mobC kk w v - foldG w v)))
    rw [add_sub_cancel] at h5
    have h6 : w ^ 2 ≤ ww ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hA'.le 2
    have h7 : (kk + |w|) ^ 2 ≤ (kk + ww) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h8 : ee ^ 2 ≤ kk ^ 2 := pow_le_pow_left₀ hε0.le hεk.le 2
    rw [hck]; nlinarith [hok.w₀_pos]
  rw [not_lt] at hA'
  have hsq : w ^ 2 ≤ 2 := by nlinarith [sq_abs w, abs_nonneg w]
  rw [h.horn _ _ hA' hsq]
  have := nsq_le_sq_of_foldG w v
  have h2 : w ^ 2 < cc ^ 2 := by rw [← sq_abs]; exact pow_lt_pow_left₀ hw (abs_nonneg _) (by norm_num)
  linarith

end Window

/-! ### 定理 M2：射影平面の面の上の走者 -/

/-- 亀の角度は 0。 -/
def VTM : ℝ → ℝ := fun _ => 0

/-- **定理 M2 の結論**（面 S の上の走者についての連言）。 -/
structure MobiusPassage (R : Race) (n₁ : ℕ) (S X : ℝ → ℝ → V3) : Prop where
  /-- 面：射影平面のはめ込み。τ 不変、法線は τ で反転、ホーンでは折り返したホーン。 -/
  surface : IsMobiusSurface (R.mkc n₁) (R.mδ n₁) (R.mw n₁) (R.mε n₁) S X
  smooth_T : ContDiff ℝ ∞ (R.runT S VTM)
  smooth_A : ContDiff ℝ ∞ (R.runA S (VAM R.r (R.mc n₁) n₁))
  /-- 読み M1：どの法線場でも、ホーンの二つの持ち上げで Φ のラベルが逆になる。 -/
  reversal : ∀ n, IsNormalField S n → ∀ w₁ w₂ v₁ v₂, R.mw n₁ < w₁ → w₁ ^ 2 < 2 →
    w₂ < -R.mw n₁ → w₂ ^ 2 < 2 → side (S w₁ v₁) (n (w₁, v₁)) * side (S w₂ v₂) (n (w₂, v₂)) < 0
  side_T_right : ∀ t ∈ Icc 0 (2 * R.tstar), R.mc n₁ ≤ R.r * R.g t →
    Front (R.runT S VTM t) (X (R.r * R.g t) 0)
  side_T_left : ∀ t ∈ Icc 0 (2 * R.tstar), R.r * R.g t ≤ -R.mc n₁ →
    Back (R.runT S VTM t) (X (R.r * R.g t) 0)
  side_A_right : ∀ t ∈ Icc 0 (2 * R.tstar), R.mc n₁ ≤ R.g t →
    Back (R.runA S (VAM R.r (R.mc n₁) n₁) t) (-X (R.g t) (VAM R.r (R.mc n₁) n₁ (R.g t)))
  side_A_left : ∀ t ∈ Icc 0 (2 * R.tstar), R.g t ≤ -R.mc n₁ →
    Front (R.runA S (VAM R.r (R.mc n₁) n₁) t) (-X (R.g t) (VAM R.r (R.mc n₁) n₁ (R.g t)))
  /-- 読み M2：一つの側しか持たない。 -/
  one_sided : ∀ w v, S (-w) (v + π) = S w v ∧ X (-w) (v + π) = -X w v
  no_side : ¬∃ n : ℝ × ℝ → V3, IsNormalField S n ∧ ∀ w v, n (-w, v + π) = n (w, v)
  /-- 読み M2：無限遠直線を一度横切る閉路に沿って運んだ側は反転する。 -/
  monodromy : ∀ γ : ℝ → ℝ × ℝ, Continuous γ → ∀ n : ℝ → V3, Continuous n → (∀ s, n s ≠ wp) →
    (∀ s, cross (n s) (X (γ s).1 (γ s).2) = wp) → γ 1 = (-(γ 0).1, (γ 0).2 + π) →
    S (γ 1).1 (γ 1).2 = S (γ 0).1 (γ 0).2 ∧ ∃ κ : ℝ, 0 < κ ∧ n 1 = -(κ • n 0)
  /-- 読み M2：亀はホーン H の表から、同じ H の裏へ移る（どう運んでも）。 -/
  exchange_T : R.runT S VTM 0 = S R.r 0 ∧ R.runT S VTM (2 * R.tstar) = S R.r π ∧
    ∀ n : ℝ → V3, Continuous n → (∀ t, n t ≠ wp) →
      (∀ t, cross (n t) (X (R.r * R.g t) 0) = wp) →
      (∃ κ : ℝ, 0 < κ ∧ n 0 = κ • X R.r 0) →
      ∃ κ : ℝ, 0 < κ ∧ n (2 * R.tstar) = -(κ • X R.r π)
  /-- 読み M2：アキレスは H の裏から、同じ H の表へ移る。 -/
  exchange_A : R.runA S (VAM R.r (R.mc n₁) n₁) 0 = S 1 0 ∧
    R.runA S (VAM R.r (R.mc n₁) n₁) (2 * R.tstar) = S 1 π ∧
    ∀ n : ℝ → V3, Continuous n → (∀ t, n t ≠ wp) →
      (∀ t, cross (n t) (X (R.g t) (VAM R.r (R.mc n₁) n₁ (R.g t))) = wp) →
      (∃ κ : ℝ, 0 < κ ∧ n 0 = -(κ • X 1 0)) →
      ∃ κ : ℝ, 0 < κ ∧ n (2 * R.tstar) = κ • X 1 π
  /-- 導線：窓の外では折り返した理想形と同じ点を通る。 -/
  agree_T : ∀ t ∈ Icc 0 (2 * R.tstar), R.mc n₁ ≤ |R.r * R.g t| →
    R.runT S VTM t = foldG (R.r * R.g t) 0
  agree_A : ∀ t ∈ Icc 0 (2 * R.tstar), R.mc n₁ ≤ |R.g t| →
    R.runA S (VAM R.r (R.mc n₁) n₁) t = foldG (R.g t) (theta R.r (R.g t))
  /-- ゼノンの段階。 -/
  step_before : ∀ k < n₁, R.runA S (VAM R.r (R.mc n₁) n₁) (R.tn (k + 1)) = R.runT S VTM (R.tn k)
  step_after : ∀ k < n₁, R.runT S VTM (R.tn' k) = R.runA S (VAM R.r (R.mc n₁) n₁) (R.tn' (k + 1))
  /-- 非衝突。t∗ に二人は無限遠直線（芯の円）の対蹠点を通る。 -/
  at_infinity : R.runT S VTM R.tstar = (0, R.mkc n₁, 0) ∧
    R.runA S (VAM R.r (R.mc n₁) n₁) R.tstar = (0, -R.mkc n₁, 0)
  no_collision : ∀ t ∈ Icc 0 (2 * R.tstar), R.runT S VTM t ≠ R.runA S (VAM R.r (R.mc n₁) n₁) t
  min_dist : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar),
    d ≤ nsq (R.runT S VTM t - R.runA S (VAM R.r (R.mc n₁) n₁) t)
  thick : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), ∀ e₁ e₂ : V3, nsq e₁ < d → nsq e₂ < d →
    R.runT S VTM t + e₁ ≠ R.runA S (VAM R.r (R.mc n₁) n₁) t + e₂
  /-- 前後。 -/
  compare_before : ∀ t, t < R.tstar → R.r * R.g t - R.g t < 0
  compare_after : ∀ t, R.tstar < t → 0 < R.r * R.g t - R.g t
  compare_zero : ∀ t, R.r * R.g t - R.g t = 0 ↔ t = R.tstar
  follow_before : ∀ s t, 0 ≤ s → s < t → t ≤ R.tstar →
    R.runT S VTM t ≠ R.runA S (VAM R.r (R.mc n₁) n₁) s
  follow_after : ∀ s t, R.tstar ≤ s → s < t → t ≤ 2 * R.tstar →
    R.runA S (VAM R.r (R.mc n₁) n₁) t ≠ R.runT S VTM s
  /-- 一様な極限：折り返した理想形への距離は 2c 未満。 -/
  uniform_T : ∀ t ∈ Icc 0 (2 * R.tstar),
    nsq (R.runT S VTM t - foldG (R.r * R.g t) 0) < 4 * R.mc n₁ ^ 2
  uniform_A : ∀ t ∈ Icc 0 (2 * R.tstar),
    nsq (R.runA S (VAM R.r (R.mc n₁) n₁) t - foldG (R.g t) (theta R.r (R.g t))) < 4 * R.mc n₁ ^ 2

section Proof

variable {R : Race} {n₁ : ℕ} {S X : ℝ → ℝ → V3}

local notation "cc" => R.mc n₁
local notation "kk" => R.mkc n₁
local notation "dd" => R.mδ n₁
local notation "ww" => R.mw n₁
local notation "ee" => R.mε n₁
local notation "VA" => VAM R.r (R.mc n₁) n₁

theorem g_zero' : R.g 0 = 1 := by rw [Race.g_eq]; simp

theorem g_two' : R.g (2 * R.tstar) = -1 := by
  have h := R.tstar_pos.ne'
  rw [Race.g_eq]; field_simp; ring

theorem abs_rg_le {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) : |R.r * R.g t| ≤ R.r * 1 := by
  rw [abs_mul, abs_of_pos R.r_pos]
  exact mul_le_mul_of_nonneg_left (R.abs_g_le ht.1 ht.2) R.r_pos.le

theorem mw_lt_mc (hn : 1 ≤ n₁) : ww < cc := by
  have hok := R.mok hn
  have hk := R.mkc_pos (n₁ := n₁)
  have : cc = 16 * kk := by simp only [Race.mkc]; ring
  linarith [hok.w₀_le]

theorem mc_lt_one (hn : 1 ≤ n₁) : cc < 1 := (R.mc_le hn).trans_lt R.r_lt_one

theorem S_neg_r (h : IsMobiusSurface kk dd ww ee S X) (w : ℝ) :
    S (-w) 0 = S w π ∧ X (-w) 0 = -X w π := by
  have e1 := h.deck w π
  have e2 := h.normal_deck w π
  rw [show π + π = 0 + 2 * π by ring, h.periodic] at e1
  rw [show π + π = 0 + 2 * π by ring, h.normal_periodic] at e2
  exact ⟨e1, e2⟩

theorem VA_one (hn : 1 ≤ n₁) : VA 1 = 0 := by
  rw [VAM_outer n₁ R.mc_pos (by rw [abs_one]; exact (mc_lt_one hn).le)]
  simp [theta]

theorem VA_neg_one (hn : 1 ≤ n₁) : VA (-1) = 0 := by
  rw [VAM_outer n₁ R.mc_pos (by rw [abs_neg, abs_one]; exact (mc_lt_one hn).le)]
  simp [theta]

/-- **定理 M2（走者）**。 -/
theorem mobius_passage (hn : 1 ≤ n₁) (h : IsMobiusSurface kk dd ww ee S X) :
    MobiusPassage R n₁ S X := by
  have hok := R.mok hn
  have hw0 := hok.w₀_pos
  have hwc := mw_lt_mc (R := R) hn
  have hc1 := mc_lt_one (R := R) hn
  have hc := R.mc_pos (n₁ := n₁)
  have hr := R.r_pos
  have hr1 := R.r_lt_one
  have hS := h.smooth
  have hg := R.contDiff_g
  have hsmT : ContDiff ℝ ∞ (R.runT S VTM) := by
    have hp : ContDiff ℝ ∞ (fun t => ((R.r * R.g t, (0 : ℝ)) : ℝ × ℝ)) :=
      (contDiff_const.mul hg).prodMk contDiff_const
    exact hS.comp hp
  have hsmA : ContDiff ℝ ∞ (R.runA S VA) := by
    have hp : ContDiff ℝ ∞ (fun t => ((R.g t, VA (R.g t)) : ℝ × ℝ)) :=
      hg.prodMk ((contDiff_VAM R.r hc n₁).comp hg)
    exact hS.comp hp
  have hsep := fun {wT wA : ℝ} (h1 : |wT| ≤ R.r * |wA|) (h2 : |wA| ≤ 1) =>
    mob_sep (R := R) (n₁ := n₁) hn h h1 h2
  have hnoc : ∀ t ∈ Icc 0 (2 * R.tstar), R.runT S VTM t ≠ R.runA S VA t := by
    intro t ht
    have h1 : |R.r * R.g t| ≤ R.r * |R.g t| := by rw [abs_mul, abs_of_pos hr]
    exact hsep h1 (R.abs_g_le ht.1 ht.2)
  refine
    { surface := h
      smooth_T := hsmT
      smooth_A := hsmA
      reversal := fun n hn' w₁ w₂ v₁ v₂ h₁ h₁' h₂ h₂' => h.reversal hw0 hn' h₁ h₁' h₂ h₂' v₁ v₂
      side_T_right := ?_
      side_T_left := ?_
      side_A_right := ?_
      side_A_left := ?_
      one_sided := fun w v => ⟨h.deck w v, h.normal_deck w v⟩
      no_side := h.no_side
      monodromy := fun γ hγ n hn' hn0 hpar hloop => h.monodromy hγ hn' hn0 hpar hloop
      exchange_T := ?_
      exchange_A := ?_
      agree_T := ?_
      agree_A := ?_
      step_before := ?_
      step_after := ?_
      at_infinity := ?_
      no_collision := hnoc
      min_dist := ?_
      thick := ?_
      compare_before := fun t ht => by
        have := R.g_pos_of_lt ht
        nlinarith [R.r_lt_one]
      compare_after := fun t ht => by
        have := R.g_neg_of_gt ht
        nlinarith [R.r_lt_one]
      compare_zero := reg_compare_zero R
      follow_before := ?_
      follow_after := ?_
      uniform_T := ?_
      uniform_A := ?_ }
  · intro t ht hct
    have hle := abs_rg_le ht
    have h1 : R.r * R.g t ≤ 1 := by
      have := le_abs_self (R.r * R.g t); linarith
    exact h.front_right hw0 (by linarith) (by nlinarith) 0
  · intro t ht hct
    have hle := abs_rg_le ht
    have h1 : -1 ≤ R.r * R.g t := by
      have := neg_abs_le (R.r * R.g t); linarith
    exact h.back_left hw0 (by linarith) (by nlinarith) 0
  · intro t ht hct
    have hle := R.abs_g_le ht.1 ht.2
    unfold Back
    rw [side_neg]
    have h1 : R.g t ≤ 1 := (le_abs_self _).trans hle
    exact neg_neg_of_pos (h.front_right hw0 (by linarith) (by nlinarith) _)
  · intro t ht hct
    have hle := R.abs_g_le ht.1 ht.2
    unfold Front
    rw [side_neg]
    have h1 : -1 ≤ R.g t := by have := neg_abs_le (R.g t); linarith
    exact neg_pos_of_neg (h.back_left hw0 (by linarith) (by nlinarith) _)
  · -- 亀の表裏の交換
    obtain ⟨e1, e2⟩ := S_neg_r h R.r
    refine ⟨by simp [Race.runT, g_zero', VTM], ?_, ?_⟩
    · simp only [Race.runT, g_two', VTM, mul_neg, mul_one]; exact e1
    · intro n hn' hn0 hpar ⟨κ, hκ, h0⟩
      have hXc : Continuous fun t => X (R.r * R.g t) 0 :=
        h.normal_cont.comp ((continuous_const.mul R.continuous_g).prodMk continuous_const)
      obtain ⟨c, -, hsm, hs⟩ := rigid_normal hXc (fun t => h.normal_ne _ _) hn' hn0 dense_univ
        (fun t _ => hpar t)
      have hc0 : c 0 = κ := by
        have := hsm 0
        rw [h0] at this
        simp only [g_zero', mul_one] at this
        have hX0 := h.normal_ne R.r 0
        have : (κ - c 0) • X R.r 0 = 0 := by rw [sub_smul, this, sub_self]
        rcases smul_eq_zero.mp this with h' | h'
        · linarith
        · exact absurd h' (fun h'' => hX0 (by rw [h'']; rfl))
      have hpos : ∀ t, 0 < c t := by
        rcases hs with hp | hp
        · exact hp
        · exact absurd (hp 0) (by rw [hc0]; exact not_lt.mpr hκ.le)
      refine ⟨c (2 * R.tstar), hpos _, ?_⟩
      rw [hsm, g_two', mul_neg, mul_one, e2, smul_neg]
  · -- アキレスの表裏の交換
    obtain ⟨e1, e2⟩ := S_neg_r h 1
    refine ⟨by simp [Race.runA, g_zero', VA_one hn], ?_, ?_⟩
    · simp only [Race.runA, g_two', VA_neg_one hn]; exact e1
    · intro n hn' hn0 hpar ⟨κ, hκ, h0⟩
      have hXc : Continuous fun t => X (R.g t) (VA (R.g t)) :=
        h.normal_cont.comp (R.continuous_g.prodMk
          ((contDiff_VAM R.r hc n₁).continuous.comp R.continuous_g))
      obtain ⟨c, -, hsm, hs⟩ := rigid_normal hXc (fun t => h.normal_ne _ _) hn' hn0 dense_univ
        (fun t _ => hpar t)
      have hc0 : c 0 = -κ := by
        have := hsm 0
        rw [h0] at this
        simp only [g_zero', VA_one hn] at this
        have hX0 := h.normal_ne 1 0
        have : (-κ - c 0) • X 1 0 = 0 := by rw [sub_smul, neg_smul, this, sub_self]
        rcases smul_eq_zero.mp this with h' | h'
        · linarith
        · exact absurd h' (fun h'' => hX0 (by rw [h'']; rfl))
      have hneg : ∀ t, c t < 0 := by
        rcases hs with hp | hp
        · exact absurd (hp 0) (by rw [hc0]; exact not_lt.mpr (by linarith))
        · exact hp
      refine ⟨-c (2 * R.tstar), by linarith [hneg (2 * R.tstar)], ?_⟩
      rw [hsm, g_two', VA_neg_one hn, e2, smul_neg, neg_smul]
  · intro t ht hct
    have hle := abs_rg_le ht
    simp only [Race.runT, VTM]
    exact h.horn _ _ (by linarith) (by nlinarith [sq_abs (R.r * R.g t), abs_nonneg (R.r * R.g t)])
  · intro t ht hct
    have hle := R.abs_g_le ht.1 ht.2
    simp only [Race.runA]
    rw [VAM_outer n₁ hc hct]
    exact h.horn _ _ (by linarith) (by nlinarith [sq_abs (R.g t), abs_nonneg (R.g t)])
  · intro j hj
    simp only [Race.runA, Race.runT, R.g_tn, VTM]
    have hp : cc ≤ R.r ^ (j + 1) := pow_le_pow_of_le_one hr.le hr1.le (by omega)
    have hp' : cc ≤ |R.r ^ (j + 1)| := by rw [abs_of_pos (pow_pos hr _)]; exact hp
    rw [VAM_outer n₁ hc hp', theta_pow hr hr1, ← pow_succ']
    have := h.periodic_nat (R.r ^ (j + 1)) 0 (j + 1)
    rw [zero_add] at this
    exact this
  · intro j hj
    simp only [Race.runA, Race.runT, R.g_tn', VTM]
    have hp : cc ≤ R.r ^ (j + 1) := pow_le_pow_of_le_one hr.le hr1.le (by omega)
    have hp' : cc ≤ |-R.r ^ (j + 1)| := by rw [abs_neg, abs_of_pos (pow_pos hr _)]; exact hp
    rw [VAM_outer n₁ hc hp', theta_neg, theta_pow hr hr1, mul_neg, ← pow_succ']
    have := h.periodic_nat (-R.r ^ (j + 1)) 0 (j + 1)
    rw [zero_add] at this
    exact this.symm
  · constructor
    · simp only [Race.runT, R.g_tstar, mul_zero, VTM]
      rw [h.core 0 0 (by rw [abs_zero]; exact hok.δ_pos.le), mobC_v0, neg_zero]
    · simp only [Race.runA, R.g_tstar]
      rw [mob_A_inner h (by rw [abs_zero]; linarith),
        h.core 0 _ (by rw [abs_zero]; exact hok.δ_pos.le), mobC_vh, add_zero]
  · -- 距離の最小値
    have hcont : Continuous fun t => nsq (R.runT S VTM t - R.runA S VA t) := by
      unfold nsq
      exact continuous_dot.comp ((hsmT.continuous.sub hsmA.continuous).prodMk
        (hsmT.continuous.sub hsmA.continuous))
    have hne' : (Icc 0 (2 * R.tstar)).Nonempty := ⟨0, le_rfl, by have := R.tstar_pos; positivity⟩
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne' hcont.continuousOn
    exact ⟨_, nsq_pos_of_ne (sub_ne_zero.mpr (hnoc t₀ ht₀)), fun t ht => hmin ht⟩
  · have hcont : Continuous fun t => nsq (R.runT S VTM t - R.runA S VA t) := by
      unfold nsq
      exact continuous_dot.comp ((hsmT.continuous.sub hsmA.continuous).prodMk
        (hsmT.continuous.sub hsmA.continuous))
    have hne' : (Icc 0 (2 * R.tstar)).Nonempty := ⟨0, le_rfl, by have := R.tstar_pos; positivity⟩
    obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne' hcont.continuousOn
    have hd := nsq_pos_of_ne (sub_ne_zero.mpr (hnoc t₀ ht₀))
    refine ⟨nsq (R.runT S VTM t₀ - R.runA S VA t₀) / 4, by positivity, fun t ht e₁ e₂ h₁ h₂ he => ?_⟩
    have h3 : nsq (R.runT S VTM t₀ - R.runA S VA t₀) ≤ nsq (R.runT S VTM t - R.runA S VA t) :=
      hmin ht
    have e : R.runT S VTM t - R.runA S VA t = e₂ - e₁ := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm e₂]
      exact he
    rw [e] at h3
    have h4 := nsq_sub_le e₂ e₁
    linarith
  · intro s t hs hst ht
    have h1 : 0 ≤ R.g t := by
      rcases eq_or_lt_of_le ht with h' | h'
      · rw [h', R.g_tstar]
      · exact (R.g_pos_of_lt h').le
    have h2 : R.g t < R.g s := R.g_lt_g hst
    have hgs := R.abs_g_le hs (by linarith [R.tstar_pos])
    have h3 : |R.r * R.g t| ≤ R.r * |R.g s| := by
      rw [abs_mul, abs_of_pos hr, abs_of_nonneg h1, abs_of_nonneg (by linarith)]
      exact mul_le_mul_of_nonneg_left h2.le hr.le
    exact hsep h3 hgs
  · intro s t hs hst ht
    have h1 : R.g s ≤ 0 := by
      rcases eq_or_lt_of_le hs with h' | h'
      · rw [← h', R.g_tstar]
      · exact (R.g_neg_of_gt h').le
    have h2 : R.g t < R.g s := R.g_lt_g hst
    have hgt := R.abs_g_le (by linarith [R.tstar_pos]) ht
    have h3 : |R.r * R.g s| ≤ R.r * |R.g t| := by
      rw [abs_mul, abs_of_pos hr, abs_of_nonpos h1, abs_of_nonpos (by linarith)]
      exact mul_le_mul_of_nonneg_left (by linarith) hr.le
    exact (hsep h3 hgt).symm
  · intro t ht
    have hle := abs_rg_le ht
    by_cases hct : cc ≤ |R.r * R.g t|
    · have e : R.runT S VTM t = foldG (R.r * R.g t) 0 := by
        simp only [Race.runT, VTM]
        exact h.horn _ _ (by linarith) (by nlinarith [sq_abs (R.r * R.g t), abs_nonneg (R.r * R.g t)])
      rw [e, sub_self]
      simp only [nsq, dot, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero]
      positivity
    · rw [not_le] at hct
      have h1 := mob_window hn h hct (by linarith) 0
      have h2 := nsq_le_sq_of_foldG (R.r * R.g t) 0
      have h3 : (R.r * R.g t) ^ 2 ≤ cc ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hct.le 2
      exact nsq_sub_lt h1 (h2.trans h3)
  · intro t ht
    have hle := R.abs_g_le ht.1 ht.2
    by_cases hct : cc ≤ |R.g t|
    · have e : R.runA S VA t = foldG (R.g t) (theta R.r (R.g t)) := by
        simp only [Race.runA]
        rw [VAM_outer n₁ hc hct]
        exact h.horn _ _ (by linarith) (by nlinarith [sq_abs (R.g t), abs_nonneg (R.g t)])
      rw [e, sub_self]
      simp only [nsq, dot, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero]
      positivity
    · rw [not_le] at hct
      have h1 := mob_window hn h hct hle (VA (R.g t))
      have h2 := nsq_le_sq_of_foldG (R.g t) (theta R.r (R.g t))
      have h3 : (R.g t) ^ 2 ≤ cc ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hct.le 2
      exact nsq_sub_lt h1 (h2.trans h3)

end Proof

end Zeno.Model
