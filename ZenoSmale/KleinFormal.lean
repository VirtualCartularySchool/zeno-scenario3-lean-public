/-
# ZenoSmale.KleinFormal : K3⁺ の形式解（基底 B と形式微分 L の明示的構成）

第 3 版 §3.5 (1)(2) の実現。首の環の上で、Σ の 2 枠 (∂wΣ, ∂ᵥΣ) から f₁ = −Σ∘φ の 2 枠
(∂wΣ∘φ, ∂ᵥΣ∘φ) へ、襟を固定したまま、一次独立な 2 枠の族 (J₁, J₂)(s, w, v) で結ぶ。
三段の道：
- 段 A：捻れの項 ψ′ を 1 → 0 へ縮める（`neck_lemma` により各段で階数 2）。
- 段 B：剛な枠を回す。回転 Ψ_rig = Φ₁Φ₀⁻¹ の S³ への持ち上げ Ψ̂ を明示し、
  Ψ̂ の像に入らない点 P = (i − k)/√2 から押し出す零ホモトピー H で結ぶ。
  Gram の対角因子（断面の速度の長さと B）は線形に補間する。
- 段 C：f₁ の捻れの項を 0 → 1 へ戻す。
形式微分 L(s, w, v) は、Σ の枠 {∂wΣ, ∂ᵥΣ, ∂wΣ × ∂ᵥΣ} に関する座標で
∂wΣ ↦ J₁、∂ᵥΣ ↦ J₂、法線 ↦ 法線 と定める。L∘dŜ は全域で単射であり、
s < ¼、s > ¾、|w| > 4w₀/5 では dB_s に一致する（ホロノミー）。

角 α（断面の速度 (AA′, BB′) の連続な偏角）は積分で定義し、(cos α, sin α) = ẑ を
微分方程式の一意性で示す。δ(w) := α(−w) + π − α(w) の半角が持ち上げに要る。
-/
import ZenoSmale.KleinQuat
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology intervalIntegral
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### 断面の速度の単位ベクトル ẑ と偏角 α -/

section Angle

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 in
theorem contDiff_dAA : ContDiff ℝ ∞ (deriv (AA w₀)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_AA h0.ne')).2

include h0 in
theorem contDiff_dBB : ContDiff ℝ ∞ (deriv (BB w₀)) :=
  (contDiff_infty_iff_deriv.mp (contDiff_BB h0.ne')).2

/-- 断面の速度の長さ |(AA′, BB′)|。 -/
def nrm (w₀ w : ℝ) : ℝ := √(deriv (AA w₀) w ^ 2 + deriv (BB w₀) w ^ 2)

include h0 h1 in
theorem nrm_sq_pos (w : ℝ) : 0 < deriv (AA w₀) w ^ 2 + deriv (BB w₀) w ^ 2 := by
  have h := profile_ne h0 h1 w
  by_contra hle
  push Not at hle
  have ha : deriv (AA w₀) w ^ 2 = 0 := by nlinarith [sq_nonneg (deriv (AA w₀) w), sq_nonneg (deriv (BB w₀) w)]
  have hb : deriv (BB w₀) w ^ 2 = 0 := by nlinarith [sq_nonneg (deriv (AA w₀) w), sq_nonneg (deriv (BB w₀) w)]
  exact h ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha, pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hb⟩

include h0 h1 in
theorem nrm_pos (w : ℝ) : 0 < nrm w₀ w := sqrt_pos.mpr (nrm_sq_pos h0 h1 w)

include h0 h1 in
theorem nrm_sq (w : ℝ) : nrm w₀ w ^ 2 = deriv (AA w₀) w ^ 2 + deriv (BB w₀) w ^ 2 :=
  sq_sqrt (nrm_sq_pos h0 h1 w).le

include h0 h1 in
theorem contDiff_nrm : ContDiff ℝ ∞ (nrm w₀) := by
  unfold nrm
  exact (((contDiff_dAA h0).pow 2).add ((contDiff_dBB h0).pow 2)).sqrt
    fun w => (nrm_sq_pos h0 h1 w).ne'

/-- ẑ₁ = AA′/|(AA′, BB′)|。 -/
def zh1 (w₀ w : ℝ) : ℝ := deriv (AA w₀) w / nrm w₀ w

/-- ẑ₂ = BB′/|(AA′, BB′)|。 -/
def zh2 (w₀ w : ℝ) : ℝ := deriv (BB w₀) w / nrm w₀ w

include h0 h1 in
theorem zh_sq (w : ℝ) : zh1 w₀ w ^ 2 + zh2 w₀ w ^ 2 = 1 := by
  have hn := (nrm_pos h0 h1 w).ne'
  simp only [zh1, zh2, div_pow]
  rw [← add_div, nrm_sq h0 h1, div_self]
  exact (nrm_sq_pos h0 h1 w).ne'

include h0 h1 in
theorem contDiff_zh1 : ContDiff ℝ ∞ (zh1 w₀) :=
  (contDiff_dAA h0).div (contDiff_nrm h0 h1) fun w => (nrm_pos h0 h1 w).ne'

include h0 h1 in
theorem contDiff_zh2 : ContDiff ℝ ∞ (zh2 w₀) :=
  (contDiff_dBB h0).div (contDiff_nrm h0 h1) fun w => (nrm_pos h0 h1 w).ne'

include h0 h1 in
theorem nrm_mul_zh1 (w : ℝ) : nrm w₀ w * zh1 w₀ w = deriv (AA w₀) w := by
  simp only [zh1]; field_simp [(nrm_pos h0 h1 w).ne']

include h0 h1 in
theorem nrm_mul_zh2 (w : ℝ) : nrm w₀ w * zh2 w₀ w = deriv (BB w₀) w := by
  simp only [zh2]; field_simp [(nrm_pos h0 h1 w).ne']

/-- 角速度 ẑ₁ ẑ₂′ − ẑ₂ ẑ₁′。 -/
def avel (w₀ w : ℝ) : ℝ := zh1 w₀ w * deriv (zh2 w₀) w - zh2 w₀ w * deriv (zh1 w₀) w

include h0 h1 in
theorem contDiff_avel : ContDiff ℝ ∞ (avel w₀) := by
  have h1' := contDiff_zh1 h0 h1
  have h2' := contDiff_zh2 h0 h1
  have d1 : ContDiff ℝ ∞ (deriv (zh1 w₀)) := (contDiff_infty_iff_deriv.mp h1').2
  have d2 : ContDiff ℝ ∞ (deriv (zh2 w₀)) := (contDiff_infty_iff_deriv.mp h2').2
  unfold avel
  exact (h1'.mul d2).sub (h2'.mul d1)

/-- 基点 w = 0 での偏角。 -/
def alph0 (w₀ : ℝ) : ℝ := Complex.arg ⟨zh1 w₀ 0, zh2 w₀ 0⟩

/-- 連続な偏角 α(w) = α₀ + ∫₀ʷ (ẑ₁ ẑ₂′ − ẑ₂ ẑ₁′)。 -/
def alph (w₀ w : ℝ) : ℝ := alph0 w₀ + ∫ u in (0 : ℝ)..w, avel w₀ u

include h0 h1 in
theorem hasDerivAt_alph (w : ℝ) : HasDerivAt (alph w₀) (avel w₀ w) w := by
  have h := ((contDiff_avel h0 h1).continuous.integral_hasStrictDerivAt 0 w).hasDerivAt
  exact (h.const_add (alph0 w₀))

include h0 h1 in
theorem deriv_alph (w : ℝ) : deriv (alph w₀) w = avel w₀ w := (hasDerivAt_alph h0 h1 w).deriv

include h0 h1 in
theorem contDiff_alph : ContDiff ℝ ∞ (alph w₀) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun w => (hasDerivAt_alph h0 h1 w).differentiableAt, ?_⟩
  have e : deriv (alph w₀) = avel w₀ := funext (deriv_alph h0 h1)
  rw [e]
  exact contDiff_avel h0 h1

include h0 h1 in
theorem cos_alph0 : cos (alph0 w₀) = zh1 w₀ 0 := by
  have hz : (⟨zh1 w₀ 0, zh2 w₀ 0⟩ : ℂ) ≠ 0 := by
    intro h
    have h1' : zh1 w₀ 0 = 0 := congrArg Complex.re h
    have h2' : zh2 w₀ 0 = 0 := congrArg Complex.im h
    have := zh_sq h0 h1 0
    rw [h1', h2'] at this
    norm_num at this
  have hn : ‖(⟨zh1 w₀ 0, zh2 w₀ 0⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only
    rw [zh_sq h0 h1 0, sqrt_one]
  rw [alph0, Complex.cos_arg hz, hn]
  simp

include h0 h1 in
theorem sin_alph0 : sin (alph0 w₀) = zh2 w₀ 0 := by
  have hn : ‖(⟨zh1 w₀ 0, zh2 w₀ 0⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    simp only
    rw [zh_sq h0 h1 0, sqrt_one]
  rw [alph0, Complex.sin_arg, hn]
  simp

include h0 h1 in
/-- ẑ ẑ′ = 0（単位ベクトルの速度は直交する）。 -/
theorem zh_dot_deriv (w : ℝ) :
    zh1 w₀ w * deriv (zh1 w₀) w + zh2 w₀ w * deriv (zh2 w₀) w = 0 := by
  have h1' := ((contDiff_zh1 h0 h1).differentiable (by simp) w).hasDerivAt
  have h2' := ((contDiff_zh2 h0 h1).differentiable (by simp) w).hasDerivAt
  have hsum := (h1'.pow 2).add (h2'.pow 2)
  have e : (zh1 w₀ ^ 2 + zh2 w₀ ^ 2 : ℝ → ℝ) = fun _ => (1 : ℝ) := by
    funext x; simp only [Pi.add_apply, Pi.pow_apply]; exact zh_sq h0 h1 x
  rw [e] at hsum
  have := hsum.unique (hasDerivAt_const w (1 : ℝ))
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at this
  linarith

include h0 h1 in
/-- **(cos α, sin α) = ẑ**。微分方程式の一意性による。 -/
theorem zh_eq_cos_sin (w : ℝ) : zh1 w₀ w = cos (alph w₀ w) ∧ zh2 w₀ w = sin (alph w₀ w) := by
  -- Z := ẑ₁ cos α + ẑ₂ sin α、Y := −ẑ₁ sin α + ẑ₂ cos α は定数である
  set Z : ℝ → ℝ := fun x => zh1 w₀ x * cos (alph w₀ x) + zh2 w₀ x * sin (alph w₀ x) with hZ
  set Y : ℝ → ℝ := fun x => -(zh1 w₀ x) * sin (alph w₀ x) + zh2 w₀ x * cos (alph w₀ x) with hY
  have hd : ∀ x, HasDerivAt Z 0 x ∧ HasDerivAt Y 0 x := by
    intro x
    have h1' := ((contDiff_zh1 h0 h1).differentiable (by simp) x).hasDerivAt
    have h2' := ((contDiff_zh2 h0 h1).differentiable (by simp) x).hasDerivAt
    have ha := hasDerivAt_alph h0 h1 x
    have hperp := zh_dot_deriv h0 h1 x
    have hsq := zh_sq h0 h1 x
    set d1 := deriv (zh1 w₀) x
    set d2 := deriv (zh2 w₀) x
    have hv : avel w₀ x = zh1 w₀ x * d2 - zh2 w₀ x * d1 := rfl
    have e1 : d1 = -(avel w₀ x) * zh2 w₀ x := by
      rw [hv]; linear_combination (-d1) * hsq + zh1 w₀ x * hperp
    have e2 : d2 = avel w₀ x * zh1 w₀ x := by
      rw [hv]; linear_combination (-d2) * hsq + zh2 w₀ x * hperp
    constructor
    · refine ((h1'.mul ha.cos).add (h2'.mul ha.sin)).congr_deriv ?_
      rw [e1, e2]; ring
    · refine (((h1'.neg).mul ha.sin).add (h2'.mul ha.cos)).congr_deriv ?_
      rw [e1, e2]; simp only [Pi.neg_apply]; ring
  have hZc : ∀ x, Z x = Z 0 := fun x =>
    is_const_of_deriv_eq_zero (fun x => (hd x).1.differentiableAt) (fun x => (hd x).1.deriv) x 0
  have hYc : ∀ x, Y x = Y 0 := fun x =>
    is_const_of_deriv_eq_zero (fun x => (hd x).2.differentiableAt) (fun x => (hd x).2.deriv) x 0
  have hZ0 : Z 0 = 1 := by
    simp only [hZ, alph, intervalIntegral.integral_same, add_zero, cos_alph0 h0 h1, sin_alph0 h0 h1]
    have := zh_sq h0 h1 0
    linear_combination this
  have hY0 : Y 0 = 0 := by
    simp only [hY, alph, intervalIntegral.integral_same, add_zero, cos_alph0 h0 h1, sin_alph0 h0 h1]
    ring
  have hZw : zh1 w₀ w * cos (alph w₀ w) + zh2 w₀ w * sin (alph w₀ w) = 1 := by
    have := hZc w; rw [hZ0] at this; exact this
  have hYw : -(zh1 w₀ w) * sin (alph w₀ w) + zh2 w₀ w * cos (alph w₀ w) = 0 := by
    have := hYc w; rw [hY0] at this; exact this
  have hcs := sin_sq_add_cos_sq (alph w₀ w)
  constructor
  · linear_combination cos (alph w₀ w) * hZw - sin (alph w₀ w) * hYw - zh1 w₀ w * hcs
  · linear_combination sin (alph w₀ w) * hZw + cos (alph w₀ w) * hYw - zh2 w₀ w * hcs

end Angle

/-! ### 襟での対称性：|w| ≥ w₀/√2 で (AA′, BB′) は奇 -/

section Collar

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 in
theorem dh_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : dh w₀ (w ^ 2) = 1 := by
  have hw0 : 0 < w₀ ^ 2 := by positivity
  have hx : 4 * w ^ 2 / w₀ ^ 2 - 1 ∉ Icc (0 : ℝ) 1 := by
    intro ⟨_, h2⟩
    have : 4 * w ^ 2 / w₀ ^ 2 ≤ 2 := by linarith
    rw [div_le_iff₀ hw0] at this
    linarith
  simp only [dh, deriv_s0_eq_zero hx]
  ring

include h0 in
theorem drho_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : drho w₀ w = w / |w| := by
  simp only [drho, dh_collar h0 hw, rho_of h0.ne' hw.le, one_mul]

include h0 in
/-- 襟では AA′(w) = da(|w|)·(w/|w|)。 -/
theorem dAA_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) :
    deriv (AA w₀) w = da |w| * (w / |w|) := by
  rw [(hasDerivAt_AA h0.ne' w).deriv]
  simp only [uu, vv, kap_of h0.ne' hw.le, deriv_kap_of h0.ne' hw, drho_collar h0 hw,
    rho_of h0.ne' hw.le, cos_zero, sin_zero]
  ring

include h0 in
theorem dBB_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) :
    deriv (BB w₀) w = db |w| * (w / |w|) := by
  rw [(hasDerivAt_BB h0.ne' w).deriv]
  simp only [uu, vv, kap_of h0.ne' hw.le, deriv_kap_of h0.ne' hw, drho_collar h0 hw,
    rho_of h0.ne' hw.le, cos_zero, sin_zero]
  ring

include h0 in
theorem dAA_neg_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) :
    deriv (AA w₀) (-w) = -deriv (AA w₀) w := by
  have hw' : w₀ ^ 2 / 2 < (-w) ^ 2 := by rwa [neg_sq]
  rw [dAA_collar h0 hw, dAA_collar h0 hw', abs_neg]
  ring

include h0 in
theorem dBB_neg_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) :
    deriv (BB w₀) (-w) = -deriv (BB w₀) w := by
  have hw' : w₀ ^ 2 / 2 < (-w) ^ 2 := by rwa [neg_sq]
  rw [dBB_collar h0 hw, dBB_collar h0 hw', abs_neg]
  ring

include h0 in
theorem nrm_neg_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : nrm w₀ (-w) = nrm w₀ w := by
  simp only [nrm, dAA_neg_collar h0 hw, dBB_neg_collar h0 hw, neg_sq]

include h0 in
theorem zh1_neg_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : zh1 w₀ (-w) = -zh1 w₀ w := by
  simp only [zh1, dAA_neg_collar h0 hw, nrm_neg_collar h0 hw, neg_div]

include h0 in
theorem zh2_neg_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : zh2 w₀ (-w) = -zh2 w₀ w := by
  simp only [zh2, dBB_neg_collar h0 hw, nrm_neg_collar h0 hw, neg_div]

include h0 in
theorem BB_neg_collar {w : ℝ} (hw : w₀ ^ 2 / 2 ≤ w ^ 2) : BB w₀ (-w) = BB w₀ w := by
  have hw' : w₀ ^ 2 / 2 ≤ (-w) ^ 2 := by rwa [neg_sq]
  rw [BB_of h0.ne' hw, BB_of h0.ne' hw', abs_neg]

include h0 in
theorem deriv_psi_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : deriv (psi w₀) w = 0 := by
  by_contra hd
  obtain ⟨h2, h3⟩ := deriv_psi_ne h0 hd
  have : w ^ 2 ≤ (w₀ / 2) ^ 2 := by nlinarith
  nlinarith

include h0 in
theorem deriv_psi_neg_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : deriv (psi w₀) (-w) = 0 :=
  deriv_psi_collar h0 (by rwa [neg_sq])

end Collar

/-! ### δ = α(−w) + π − α(w) と、その半角 -/

section Delta

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

/-- δ(w) = α(−w) + π − α(w)。 -/
def del (w₀ w : ℝ) : ℝ := alph w₀ (-w) + π - alph w₀ w

/-- cos(δ/2)。 -/
def cdel (w₀ w : ℝ) : ℝ := cos (del w₀ w / 2)

/-- sin(δ/2)。 -/
def sdel (w₀ w : ℝ) : ℝ := sin (del w₀ w / 2)

include h0 h1 in
theorem contDiff_del : ContDiff ℝ ∞ (del w₀) := by
  unfold del
  exact (((contDiff_alph h0 h1).comp contDiff_neg).add contDiff_const).sub (contDiff_alph h0 h1)

include h0 h1 in
theorem contDiff_cdel : ContDiff ℝ ∞ (cdel w₀) :=
  Real.contDiff_cos.comp ((contDiff_del h0 h1).div_const 2)

include h0 h1 in
theorem contDiff_sdel : ContDiff ℝ ∞ (sdel w₀) :=
  Real.contDiff_sin.comp ((contDiff_del h0 h1).div_const 2)

theorem cdel_sq_add_sdel_sq (w : ℝ) : cdel w₀ w ^ 2 + sdel w₀ w ^ 2 = 1 := by
  simp only [cdel, sdel]
  linear_combination cos_sq_add_sin_sq (del w₀ w / 2)

include h0 h1 in
theorem cos_del (w : ℝ) :
    cos (del w₀ w) = -(zh1 w₀ (-w) * zh1 w₀ w + zh2 w₀ (-w) * zh2 w₀ w) := by
  obtain ⟨c1, s1⟩ := zh_eq_cos_sin h0 h1 w
  obtain ⟨c2, s2⟩ := zh_eq_cos_sin h0 h1 (-w)
  rw [c1, s1, c2, s2]
  have e : del w₀ w = (alph w₀ (-w) - alph w₀ w) + π := by simp only [del]; ring
  rw [e, cos_add_pi, cos_sub]

include h0 h1 in
theorem sin_del (w : ℝ) :
    sin (del w₀ w) = -(zh2 w₀ (-w) * zh1 w₀ w - zh1 w₀ (-w) * zh2 w₀ w) := by
  obtain ⟨c1, s1⟩ := zh_eq_cos_sin h0 h1 w
  obtain ⟨c2, s2⟩ := zh_eq_cos_sin h0 h1 (-w)
  rw [c1, s1, c2, s2]
  have e : del w₀ w = (alph w₀ (-w) - alph w₀ w) + π := by simp only [del]; ring
  rw [e, sin_add_pi, sin_sub]

include h0 h1 in
theorem cos_del_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : cos (del w₀ w) = 1 := by
  rw [cos_del h0 h1, zh1_neg_collar h0 hw, zh2_neg_collar h0 hw]
  have := zh_sq h0 h1 w
  linear_combination this

include h0 h1 in
theorem sdel_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : sdel w₀ w = 0 := by
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp (cos_del_collar h0 h1 hw)
  simp only [sdel]
  rw [← hk]
  have e : (k : ℝ) * (2 * π) / 2 = k * π := by ring
  rw [e]
  exact Real.sin_int_mul_pi k

include h0 h1 in
theorem cdel_sq_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) : cdel w₀ w ^ 2 = 1 := by
  have := cdel_sq_add_sdel_sq (w₀ := w₀) w
  rw [sdel_collar h0 h1 hw] at this
  linarith

/-- 符号 ε₀ := cos(δ(−w₀)/2) ∈ {±1}。 -/
def eps0 (w₀ : ℝ) : ℝ := cdel w₀ (-w₀)

include h0 h1 in
theorem eps0_sq : eps0 w₀ ^ 2 = 1 := by
  unfold eps0
  exact cdel_sq_collar h0 h1 (by rw [neg_sq]; nlinarith)

include h0 h1 in
/-- 偏角の差の偶奇：cos(δ(w₀)/2) = −cos(δ(−w₀)/2)。 -/
theorem cdel_w0 : cdel w₀ w₀ = -eps0 w₀ := by
  have hw : w₀ ^ 2 / 2 < w₀ ^ 2 := by nlinarith
  obtain ⟨c1, s1⟩ := zh_eq_cos_sin h0 h1 w₀
  obtain ⟨c2, s2⟩ := zh_eq_cos_sin h0 h1 (-w₀)
  -- cos(α(w₀) − α(−w₀)) = −1
  have hcos : cos (alph w₀ w₀ - alph w₀ (-w₀)) = -1 := by
    rw [cos_sub, ← c1, ← s1, ← c2, ← s2, zh1_neg_collar h0 hw, zh2_neg_collar h0 hw]
    have := zh_sq h0 h1 w₀
    linear_combination -this
  obtain ⟨k, hk⟩ := Real.cos_eq_neg_one_iff.mp hcos
  have e1 : del w₀ w₀ / 2 = -(k * π) := by
    simp only [del]; linarith
  have e2 : del w₀ (-w₀) / 2 = k * π + π := by
    simp only [del, neg_neg]; linarith
  simp only [eps0, cdel, e1, e2, cos_neg, cos_add_pi]
  ring

include h0 h1 in
/-- 襟の各成分の上で cos(δ/2) は定数である（中間値の定理）。 -/
theorem cdel_const_of_collar {u w : ℝ} (hu : w₀ ^ 2 / 2 < u ^ 2) (hw : w₀ ^ 2 / 2 < w ^ 2)
    (hsame : 0 < u * w) : cdel w₀ u = cdel w₀ w := by
  -- u と w の間の点はすべて襟にある
  have hmid : ∀ x, x ∈ uIcc u w → w₀ ^ 2 / 2 < x ^ 2 := by
    intro x hx
    rcases le_total u w with huw | huw
    · rw [uIcc_of_le huw] at hx
      rcases lt_or_gt_of_ne (show u ≠ 0 by rintro rfl; simp at hsame) with hneg | hpos
      · have hwneg : w < 0 := by nlinarith
        have : x ≤ w := hx.2
        nlinarith
      · have : u ≤ x := hx.1
        nlinarith
    · rw [uIcc_of_ge huw] at hx
      rcases lt_or_gt_of_ne (show w ≠ 0 by rintro rfl; simp at hsame) with hneg | hpos
      · have huneg : u < 0 := by nlinarith
        have : x ≤ u := hx.2
        nlinarith
      · have : w ≤ x := hx.1
        nlinarith
  have hcont : ContinuousOn (cdel w₀) (uIcc u w) := (contDiff_cdel h0 h1).continuous.continuousOn
  by_contra hne
  have hu2 := cdel_sq_collar h0 h1 hu
  have hw2 := cdel_sq_collar h0 h1 hw
  have hzero : (0 : ℝ) ∈ uIcc (cdel w₀ u) (cdel w₀ w) := by
    have hu' : cdel w₀ u = 1 ∨ cdel w₀ u = -1 := mul_self_eq_one_iff.mp (by nlinarith)
    have hw' : cdel w₀ w = 1 ∨ cdel w₀ w = -1 := mul_self_eq_one_iff.mp (by nlinarith)
    rcases hu' with hu' | hu' <;> rcases hw' with hw' | hw'
    · exact absurd (hu'.trans hw'.symm) hne
    · rw [hu', hw', uIcc_of_ge (by norm_num)]; exact ⟨by norm_num, by norm_num⟩
    · rw [hu', hw', uIcc_of_le (by norm_num)]; exact ⟨by norm_num, by norm_num⟩
    · exact absurd (hu'.trans hw'.symm) hne
  obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hcont hzero
  have := cdel_sq_collar h0 h1 (hmid x hx)
  rw [hx0] at this
  norm_num at this

include h0 h1 in
theorem cdel_left {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) (hneg : w < 0) : cdel w₀ w = eps0 w₀ := by
  unfold eps0
  exact cdel_const_of_collar h0 h1 hw (by rw [neg_sq]; nlinarith) (by nlinarith)

include h0 h1 in
theorem cdel_right {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) (hpos : 0 < w) : cdel w₀ w = -eps0 w₀ := by
  rw [← cdel_w0 h0 h1]
  exact cdel_const_of_collar h0 h1 hw (by nlinarith) (by nlinarith)

end Delta

/-! ### 持ち上げ Ψ̂ と、その像に入らない点 P -/

section Lift

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

/-- ψ̃(w) = ψ(−w) + π（f₁ = −Σ∘φ の回転角）。 -/
def psit (w₀ w : ℝ) : ℝ := psi w₀ (-w) + π

theorem contDiff_psit : ContDiff ℝ ∞ (psit w₀) :=
  ((contDiff_psi w₀).comp contDiff_neg).add contDiff_const

/-- θ₁ = (ψ̃ − ψ)/2。 -/
def th1 (w₀ w : ℝ) : ℝ := (psit w₀ w - psi w₀ w) / 2

/-- θ₂ = (ψ̃ + ψ)/2。 -/
def th2 (w₀ w : ℝ) : ℝ := (psit w₀ w + psi w₀ w) / 2

theorem contDiff_th1 : ContDiff ℝ ∞ (th1 w₀) :=
  ((contDiff_psit).sub (contDiff_psi w₀)).div_const 2

theorem contDiff_th2 : ContDiff ℝ ∞ (th2 w₀) :=
  ((contDiff_psit).add (contDiff_psi w₀)).div_const 2

/-- 積の公式：E_j(β)·(E_i(h)(c + s k)E_i(−h))·E_j(−γ) の閉じた形。 -/
theorem lift_prod (β γ h c s : ℝ) :
    qmul (Ej β) (qmul (qmul (Ei h) (qmul (c, 0, 0, s) (Ei (-h)))) (Ej (-γ))) =
      (c * cos (β - γ) + s * sin (2 * h) * sin (β - γ), s * cos (2 * h) * sin (β + γ),
        c * sin (β - γ) - s * sin (2 * h) * cos (β - γ), s * cos (2 * h) * cos (β + γ)) := by
  have hs := sin_sq_add_cos_sq h
  simp only [qmul, Ei, Ej, cos_sub, sin_sub, cos_add, sin_add, cos_two_mul', sin_two_mul, cos_neg,
    sin_neg]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only
  · linear_combination (c * (cos β * cos γ + sin β * sin γ)) * hs
  · ring
  · linear_combination (c * (sin β * cos γ - cos β * sin γ)) * hs
  · ring

/-- **持ち上げ Ψ̂**（閉じた形）。
Ψ̂ = ε₀ E_j(ψ̃/2) E_i(v/2) E_k(δ/2) E_i(−v/2) E_j(−ψ/2)。 -/
def Psih (w₀ w v : ℝ) : Q4 :=
  eps0 w₀ • (cdel w₀ w * cos (th1 w₀ w) + sdel w₀ w * sin v * sin (th1 w₀ w),
    sdel w₀ w * cos v * sin (th2 w₀ w),
    cdel w₀ w * sin (th1 w₀ w) - sdel w₀ w * sin v * cos (th1 w₀ w),
    sdel w₀ w * cos v * cos (th2 w₀ w))

theorem Psih_eq_prod (w v : ℝ) :
    Psih w₀ w v = eps0 w₀ • qmul (Ej (psit w₀ w / 2))
      (qmul (qmul (Ei (v / 2)) (qmul (Ek (del w₀ w / 2)) (Ei (-(v / 2)))))
        (Ej (-(psi w₀ w / 2)))) := by
  have e := lift_prod (psit w₀ w / 2) (psi w₀ w / 2) (v / 2) (cdel w₀ w) (sdel w₀ w)
  have e2 : (2 : ℝ) * (v / 2) = v := by ring
  have e3 : psit w₀ w / 2 - psi w₀ w / 2 = th1 w₀ w := by simp only [th1]; ring
  have e4 : psit w₀ w / 2 + psi w₀ w / 2 = th2 w₀ w := by simp only [th2]; ring
  rw [e2, e3, e4] at e
  unfold Psih
  congr 1
  exact e.symm

include h0 h1 in
theorem qnsq_Psih (w v : ℝ) : qnsq (Psih w₀ w v) = 1 := by
  rw [Psih_eq_prod, qnsq_smul, eps0_sq h0 h1]
  simp only [qnsq_mul, qnsq_Ei, qnsq_Ej, qnsq_Ek]
  ring

theorem Psih_periodic (w v : ℝ) : Psih w₀ w (v + 2 * π) = Psih w₀ w v := by
  simp only [Psih, sin_add_two_pi, cos_add_two_pi]

include h0 h1 in
theorem contDiff_Psih : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Psih w₀ p.1 p.2) := by
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => cdel w₀ p.1) := (contDiff_cdel h0 h1).comp contDiff_fst
  have hs : ContDiff ℝ ∞ (fun p : ℝ × ℝ => sdel w₀ p.1) := (contDiff_sdel h0 h1).comp contDiff_fst
  have ht1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => th1 w₀ p.1) := contDiff_th1.comp contDiff_fst
  have ht2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => th2 w₀ p.1) := contDiff_th2.comp contDiff_fst
  unfold Psih
  fun_prop

include h0 h1 in
/-- 襟では Ψ̂ = 1。 -/
theorem Psih_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) (v : ℝ) : Psih w₀ w v = qone := by
  have hs := sdel_collar h0 h1 hw
  have he := eps0_sq h0 h1
  have hw0 : w ≠ 0 := by rintro rfl; nlinarith
  rcases lt_or_gt_of_ne hw0 with hneg | hpos
  · have hc := cdel_left h0 h1 hw hneg
    have hψ : psi w₀ w = π := psi_of_le h0 (by linarith)
    have hψ' : psi w₀ (-w) = 0 := by
      apply psi_of_ge h0
      nlinarith
    have e1 : th1 w₀ w = 0 := by simp only [th1, psit, hψ, hψ']; ring
    have e2 : th2 w₀ w = π := by simp only [th2, psit, hψ, hψ']; ring
    simp only [Psih, e1, e2, hs, hc, cos_zero, sin_zero, qone]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> nlinarith
  · have hc := cdel_right h0 h1 hw hpos
    have hψ : psi w₀ w = 0 := by
      apply psi_of_ge h0
      nlinarith
    have hψ' : psi w₀ (-w) = π := psi_of_le h0 (by linarith)
    have e1 : th1 w₀ w = π := by simp only [th1, psit, hψ, hψ']; ring
    have e2 : th2 w₀ w = π := by simp only [th2, psit, hψ, hψ']; ring
    simp only [Psih, e1, e2, hs, hc, cos_pi, sin_pi, qone]
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> nlinarith

/-- 避ける点 P = (i − k)/√2。 -/
def Pq : Q4 := (0, 1 / √2, 0, -(1 / √2))

theorem qnsq_Pq : qnsq Pq = 1 := by
  have h2 : (√2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  simp only [qnsq, Pq]
  rw [div_pow, one_pow, h2, neg_sq, div_pow, one_pow, h2]
  norm_num

theorem one_ne_Pq : qone ≠ Pq := by
  intro h
  have := congrArg Prod.fst h
  simp [qone, Pq] at this

theorem psi_nonneg (w₀ w : ℝ) : 0 ≤ psi w₀ w := by
  simp only [psi]
  have := smoothTransition.le_one ((4 * w - w₀) / w₀)
  nlinarith [pi_pos]

theorem psi_le_pi (w₀ w : ℝ) : psi w₀ w ≤ π := by
  simp only [psi]
  have := smoothTransition.nonneg ((4 * w - w₀) / w₀)
  nlinarith [pi_pos]

include h0 in
theorem th2_mem (w : ℝ) : π ≤ th2 w₀ w ∧ th2 w₀ w ≤ 3 * π / 2 := by
  have a1 := psi_nonneg w₀ w
  have a2 := psi_le_pi w₀ w
  have b1 := psi_nonneg w₀ (-w)
  have b2 := psi_le_pi w₀ (-w)
  simp only [th2, psit]
  rcases le_or_gt w 0 with hw | hw
  · have : psi w₀ w = π := psi_of_le h0 (by linarith)
    constructor <;> linarith
  · have : psi w₀ (-w) = π := psi_of_le h0 (by linarith)
    constructor <;> linarith

include h0 in
theorem sin_th2_nonpos (w : ℝ) : sin (th2 w₀ w) ≤ 0 := by
  obtain ⟨hl, hu⟩ := th2_mem h0 w
  have e : th2 w₀ w = (th2 w₀ w - π) + π := by ring
  rw [e, sin_add_pi]
  have : 0 ≤ sin (th2 w₀ w - π) :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [pi_pos])
  linarith

include h0 in
theorem cos_th2_nonpos (w : ℝ) : cos (th2 w₀ w) ≤ 0 := by
  obtain ⟨hl, hu⟩ := th2_mem h0 w
  have e : th2 w₀ w = (th2 w₀ w - π) + π := by ring
  rw [e, cos_add_pi]
  have : 0 ≤ cos (th2 w₀ w - π) :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], by linarith⟩
  linarith

include h0 h1 in
/-- **P は Ψ̂ の像に入らない**。 -/
theorem Psih_ne_Pq (w v : ℝ) : Psih w₀ w v ≠ Pq := by
  intro h
  have he := eps0_sq h0 h1
  have hε : eps0 w₀ ≠ 0 := by
    intro h'; rw [h'] at he; norm_num at he
  simp only [Psih, Pq] at h
  have h0' := congrArg Prod.fst h
  have h1' := congrArg (fun q : Q4 => q.2.1) h
  have h2' := congrArg (fun q : Q4 => q.2.2.1) h
  have h3' := congrArg (fun q : Q4 => q.2.2.2) h
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h0' h1' h2' h3'
  have hA : cdel w₀ w * cos (th1 w₀ w) + sdel w₀ w * sin v * sin (th1 w₀ w) = 0 :=
    (mul_eq_zero.mp h0').resolve_left hε
  have hB : cdel w₀ w * sin (th1 w₀ w) - sdel w₀ w * sin v * cos (th1 w₀ w) = 0 :=
    (mul_eq_zero.mp h2').resolve_left hε
  have hcs := sin_sq_add_cos_sq (th1 w₀ w)
  have hc : cdel w₀ w = 0 := by
    linear_combination cos (th1 w₀ w) * hA + sin (th1 w₀ w) * hB - cdel w₀ w * hcs
  have hs : sdel w₀ w * sin v = 0 := by
    linear_combination sin (th1 w₀ w) * hA - cos (th1 w₀ w) * hB - sdel w₀ w * sin v * hcs
  have hs2 : sdel w₀ w ^ 2 = 1 := by
    have := cdel_sq_add_sdel_sq (w₀ := w₀) w
    rw [hc] at this; linarith
  have hsne : sdel w₀ w ≠ 0 := by
    intro h'; rw [h'] at hs2; norm_num at hs2
  have hsinv : sin v = 0 := (mul_eq_zero.mp hs).resolve_left hsne
  have hcosv : cos v ^ 2 = 1 := by
    have := sin_sq_add_cos_sq v
    rw [hsinv] at this; linarith
  have hm : eps0 w₀ * (sdel w₀ w * cos v * sin (th2 w₀ w)) *
      (eps0 w₀ * (sdel w₀ w * cos v * cos (th2 w₀ w))) = 1 / √2 * -(1 / √2) := by
    rw [h1', h3']
  have e1 : eps0 w₀ * (sdel w₀ w * cos v * sin (th2 w₀ w)) *
      (eps0 w₀ * (sdel w₀ w * cos v * cos (th2 w₀ w))) =
      eps0 w₀ ^ 2 * sdel w₀ w ^ 2 * cos v ^ 2 * (sin (th2 w₀ w) * cos (th2 w₀ w)) := by ring
  have e2 : (1 / √2 : ℝ) * -(1 / √2) = -(1 / 2) := by
    rw [mul_neg, div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num)]
  rw [e1, he, hs2, hcosv, e2] at hm
  have hnn : 0 ≤ sin (th2 w₀ w) * cos (th2 w₀ w) :=
    mul_nonneg_of_nonpos_of_nonpos (sin_th2_nonpos h0 w) (cos_th2_nonpos h0 w)
  linarith

end Lift

/-! ### 剛な枠の方向と、Ψ̂ による対応 -/

section Frame

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

/-- Φ₀ e₁ = rot2(ψ) R₁(v) ẑ。 -/
def e1dir (w₀ w v : ℝ) : V3 :=
  rot2 (psi w₀ w) (zh1 w₀ w, zh2 w₀ w * cos v, zh2 w₀ w * sin v)

/-- Φ₀ e₂ = rot2(ψ) R₁(v) e₃。 -/
def e2dir (w₀ w v : ℝ) : V3 := rot2 (psi w₀ w) (0, -sin v, cos v)

/-- Φ₁ e₁ = rot2(ψ̃) R₁(v) (−ẑ(−w))。 -/
def f1dir (w₀ w v : ℝ) : V3 :=
  rot2 (psit w₀ w) (-(zh1 w₀ (-w)), -(zh2 w₀ (-w)) * cos v, -(zh2 w₀ (-w)) * sin v)

/-- Φ₁ e₂ = rot2(ψ̃) R₁(v) e₃。 -/
def f2dir (w₀ w v : ℝ) : V3 := rot2 (psit w₀ w) (0, -sin v, cos v)

theorem rot2_neg_self (ψ : ℝ) (q : V3) : rot2 (-ψ) (rot2 ψ q) = q := by
  rw [← rot2_add, neg_add_cancel, rot2_zero]

theorem rot2_smul (ψ c : ℝ) (q : V3) : rot2 ψ (c • q) = c • rot2 ψ q := by
  simp only [rot2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    ring

theorem rot2_neg (ψ : ℝ) (q : V3) : rot2 ψ (-q) = -rot2 ψ q := by
  simp only [rot2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring

theorem R1_apply_e3' (v : ℝ) : R1 v (0, 0, 1) = (0, -sin v, cos v) := by
  simp [R1]

include h0 h1 in
/-- ρ(Ψ̂) Φ₀ e₁ = Φ₁ e₁。 -/
theorem rotQ_Psih_e1 (w v : ℝ) : rotQ (Psih w₀ w v) (e1dir w₀ w v) = f1dir w₀ w v := by
  rw [Psih_eq_prod, rotQ_smul, eps0_sq h0 h1, one_smul]
  simp only [rotQ_mul, rotQ_Ej, rotQ_Ei, rotQ_Ek]
  have e1 : 2 * (psit w₀ w / 2) = psit w₀ w := by ring
  have e2 : 2 * (v / 2) = v := by ring
  have e3 : 2 * (del w₀ w / 2) = del w₀ w := by ring
  have e4 : 2 * (-(v / 2)) = -v := by ring
  have e5 : 2 * (-(psi w₀ w / 2)) = -(psi w₀ w) := by ring
  rw [e1, e2, e3, e4, e5]
  simp only [e1dir, f1dir]
  rw [rot2_neg_self, ← R1_apply_axis, R1_neg_self]
  have hR3 : R3 (del w₀ w) (zh1 w₀ w, zh2 w₀ w, 0) = (-(zh1 w₀ (-w)), -(zh2 w₀ (-w)), 0) := by
    simp only [R3, cos_del h0 h1, sin_del h0 h1]
    have := zh_sq h0 h1 w
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only
    · linear_combination (-(zh1 w₀ (-w))) * this
    · linear_combination (-(zh2 w₀ (-w))) * this
  rw [hR3, R1_apply_axis]

include h0 h1 in
/-- ρ(Ψ̂) Φ₀ e₂ = Φ₁ e₂。 -/
theorem rotQ_Psih_e2 (w v : ℝ) : rotQ (Psih w₀ w v) (e2dir w₀ w v) = f2dir w₀ w v := by
  rw [Psih_eq_prod, rotQ_smul, eps0_sq h0 h1, one_smul]
  simp only [rotQ_mul, rotQ_Ej, rotQ_Ei, rotQ_Ek]
  have e1 : 2 * (psit w₀ w / 2) = psit w₀ w := by ring
  have e2 : 2 * (v / 2) = v := by ring
  have e3 : 2 * (del w₀ w / 2) = del w₀ w := by ring
  have e4 : 2 * (-(v / 2)) = -v := by ring
  have e5 : 2 * (-(psi w₀ w / 2)) = -(psi w₀ w) := by ring
  rw [e1, e2, e3, e4, e5]
  simp only [e2dir, f2dir]
  rw [rot2_neg_self, ← R1_apply_e3', R1_neg_self, R3_e3, R1_apply_e3']

/-! ### 三段の時間割と零ホモトピー H -/

/-- 段 A の助変数：s ≤ ¼ で 1、s ≥ 5/12 で 0。 -/
def tauA (s : ℝ) : ℝ := 1 - s₀ (6 * s - 3 / 2)

/-- 段 B の助変数：s ≤ 5/12 で 0、s ≥ 7/12 で 1。 -/
def sigB (s : ℝ) : ℝ := s₀ (6 * s - 5 / 2)

/-- 段 C の助変数：s ≤ 7/12 で 0、s ≥ ¾ で 1。 -/
def tauC (s : ℝ) : ℝ := s₀ (6 * s - 7 / 2)

theorem tauA_of_le {s : ℝ} (hs : s ≤ 1 / 4) : tauA s = 1 := by
  simp [tauA, smoothTransition.zero_of_nonpos (by linarith : 6 * s - 3 / 2 ≤ 0)]

theorem tauA_of_ge {s : ℝ} (hs : 5 / 12 ≤ s) : tauA s = 0 := by
  simp [tauA, smoothTransition.one_of_one_le (by linarith : 1 ≤ 6 * s - 3 / 2)]

theorem sigB_of_le {s : ℝ} (hs : s ≤ 5 / 12) : sigB s = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

theorem sigB_of_ge {s : ℝ} (hs : 7 / 12 ≤ s) : sigB s = 1 :=
  smoothTransition.one_of_one_le (by linarith)

theorem tauC_of_le {s : ℝ} (hs : s ≤ 7 / 12) : tauC s = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

theorem tauC_of_ge {s : ℝ} (hs : 3 / 4 ≤ s) : tauC s = 1 :=
  smoothTransition.one_of_one_le (by linarith)

theorem sigB_nonneg (s : ℝ) : 0 ≤ sigB s := smoothTransition.nonneg _

theorem sigB_le_one (s : ℝ) : sigB s ≤ 1 := smoothTransition.le_one _

theorem contDiff_tauA : ContDiff ℝ ∞ tauA := by
  unfold tauA; exact contDiff_const.sub (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem contDiff_sigB : ContDiff ℝ ∞ sigB := by
  unfold sigB; exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem contDiff_tauC : ContDiff ℝ ∞ tauC := by
  unfold tauC; exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem qnsq_neg (q : Q4) : qnsq (-q) = qnsq q := by
  simp only [qnsq, Prod.fst_neg, Prod.snd_neg]; ring

/-- σ q − (1 − σ) P は、|q| = 1、q ≠ P なら消えない。 -/
theorem qnsq_comb_ne {q : Q4} (hq : qnsq q = 1) (hne : q ≠ Pq) (σ : ℝ) :
    qnsq (σ • q - (1 - σ) • Pq) ≠ 0 := by
  intro h
  have h0' := qnsq_eq_zero h
  have e : σ • q = (1 - σ) • Pq := sub_eq_zero.mp h0'
  have hn : qnsq (σ • q) = qnsq ((1 - σ) • Pq) := by rw [e]
  rw [qnsq_smul, qnsq_smul, hq, qnsq_Pq] at hn
  have hσ : σ = 1 / 2 := by nlinarith
  rw [hσ] at e
  have e' : (1 / 2 : ℝ) • q = (1 / 2 : ℝ) • Pq := by
    rw [e]; norm_num
  exact hne (smul_right_injective Q4 (by norm_num : (1 / 2 : ℝ) ≠ 0) e')

/-- g(σ) = N(σ·1 − (1 − σ) P)。 -/
def gq (σ : ℝ) : Q4 := qnorm (σ • qone - (1 - σ) • Pq)

/-- 零ホモトピー H(σ) = g(σ)⁻¹ N(σ Ψ̂ − (1 − σ) P)：H(0) = 1、H(1) = Ψ̂、Ψ̂ = 1 のところで 1。 -/
def Hq (w₀ σ w v : ℝ) : Q4 :=
  qmul (qconj (gq σ)) (qnorm (σ • Psih w₀ w v - (1 - σ) • Pq))

theorem gq_ne (σ : ℝ) : qnsq (σ • qone - (1 - σ) • Pq) ≠ 0 := qnsq_comb_ne qnsq_one one_ne_Pq σ

theorem qnsq_gq (σ : ℝ) : qnsq (gq σ) = 1 := qnsq_qnorm (gq_ne σ)

include h0 h1 in
theorem qnsq_Hq (σ w v : ℝ) : qnsq (Hq w₀ σ w v) = 1 := by
  rw [Hq, qnsq_mul, qnsq_conj, qnsq_gq,
    qnsq_qnorm (qnsq_comb_ne (qnsq_Psih h0 h1 w v) (Psih_ne_Pq h0 h1 w v) σ)]
  ring

theorem Hq_zero (w v : ℝ) : Hq w₀ 0 w v = qone := by
  simp only [Hq, gq, zero_smul, sub_zero, zero_sub, one_smul]
  rw [qconj_mul_self, qnsq_qnorm]
  · rfl
  · rw [qnsq_neg, qnsq_Pq]; norm_num

include h0 h1 in
theorem Hq_one (w v : ℝ) : Hq w₀ 1 w v = Psih w₀ w v := by
  simp only [Hq, gq, one_smul, sub_self, zero_smul, sub_zero]
  rw [qnorm_of_unit qnsq_one, qconj_one, one_qmul, qnorm_of_unit (qnsq_Psih h0 h1 w v)]

theorem Hq_of_Psih_one {w v : ℝ} (h : Psih w₀ w v = qone) (σ : ℝ) : Hq w₀ σ w v = qone := by
  simp only [Hq, h]
  show qmul (qconj (gq σ)) (gq σ) = qone
  rw [qconj_mul_self, qnsq_gq]
  rfl

theorem Hq_periodic (σ w v : ℝ) : Hq w₀ σ w (v + 2 * π) = Hq w₀ σ w v := by
  simp only [Hq, Psih_periodic]

include h0 h1 in
theorem contDiff_Hq : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Hq w₀ q.1 q.2.1 q.2.2) := by
  have hP : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Psih w₀ q.2.1 q.2.2) :=
    (contDiff_Psih h0 h1).comp (contDiff_fst.comp contDiff_snd |>.prodMk
      (contDiff_snd.comp contDiff_snd))
  have hg : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => gq q.1) := by
    unfold gq
    refine ContDiff.qnorm ?_ fun q => gq_ne q.1
    exact (contDiff_fst.smul contDiff_const).sub ((contDiff_const.sub contDiff_fst).smul contDiff_const)
  have hc : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => q.1 • Psih w₀ q.2.1 q.2.2 - (1 - q.1) • Pq) :=
    (contDiff_fst.smul hP).sub ((contDiff_const.sub contDiff_fst).smul contDiff_const)
  have hn : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ =>
      qnorm (q.1 • Psih w₀ q.2.1 q.2.2 - (1 - q.1) • Pq)) :=
    ContDiff.qnorm hc fun q => qnsq_comb_ne (qnsq_Psih h0 h1 _ _) (Psih_ne_Pq h0 h1 _ _) q.1
  exact hg.qconj.qmul hn

/-! ### 2 枠の族 (J₁, J₂) -/

/-- Gram の対角因子の補間：断面の速度の長さ。 -/
def nB (w₀ σ w : ℝ) : ℝ := (1 - σ) * nrm w₀ w + σ * nrm w₀ (-w)

/-- Gram の対角因子の補間：B。 -/
def bB (w₀ σ w : ℝ) : ℝ := (1 - σ) * BB w₀ w + σ * BB w₀ (-w)

/-- Σ の捻れの項 ψ′ rot2(ψ)(B sin v, 0, −A)。 -/
def T0 (w₀ w v : ℝ) : V3 :=
  deriv (psi w₀) w • rot2 (psi w₀ w) (BB w₀ w * sin v, 0, -(AA w₀ w))

/-- f₁ の捻れの項。 -/
def T1 (w₀ w v : ℝ) : V3 :=
  deriv (psi w₀) (-w) • rot2 (psi w₀ (-w)) (BB w₀ (-w) * sin v, 0, -(AA w₀ (-w)))

/-- 形式的な 2 枠の第一ベクトル。 -/
def J1 (w₀ s w v : ℝ) : V3 :=
  rotQ (Hq w₀ (sigB s) w v) (nB w₀ (sigB s) w • e1dir w₀ w v) + tauA s • T0 w₀ w v +
    tauC s • T1 w₀ w v

/-- 形式的な 2 枠の第二ベクトル。 -/
def J2 (w₀ s w v : ℝ) : V3 :=
  rotQ (Hq w₀ (sigB s) w v) (bB w₀ (sigB s) w • e2dir w₀ w v)

/-- ∂wΣ の式。 -/
def aS (w₀ w v : ℝ) : V3 :=
  sigW (psi w₀ w) (AA w₀ w) (BB w₀ w) (deriv (AA w₀) w) (deriv (BB w₀) w) (deriv (psi w₀) w) v

/-- ∂ᵥΣ の式。 -/
def bS (w₀ w v : ℝ) : V3 := sigV (psi w₀ w) (BB w₀ w) v

theorem sigW_split (ψ A B dA dB dψ v : ℝ) :
    sigW ψ A B dA dB dψ v =
      rot2 ψ (dA, dB * cos v, dB * sin v) + dψ • rot2 ψ (B * sin v, 0, -A) := by
  simp only [sigW, rot2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

include h0 h1 in
theorem nrm_smul_e1dir (w v : ℝ) :
    nrm w₀ w • e1dir w₀ w v =
      rot2 (psi w₀ w) (deriv (AA w₀) w, deriv (BB w₀) w * cos v, deriv (BB w₀) w * sin v) := by
  rw [e1dir, ← rot2_smul]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  · exact nrm_mul_zh1 h0 h1 w
  · rw [← nrm_mul_zh2 h0 h1 w]; ring
  · rw [← nrm_mul_zh2 h0 h1 w]; ring

theorem BB_smul_e2dir (w v : ℝ) : BB w₀ w • e2dir w₀ w v = bS w₀ w v := by
  rw [e2dir, ← rot2_smul, bS, sigV]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

include h0 h1 in
theorem nrm_smul_f1dir (w v : ℝ) :
    nrm w₀ (-w) • f1dir w₀ w v =
      rot2 (psi w₀ (-w)) (deriv (AA w₀) (-w), deriv (BB w₀) (-w) * cos (π - v),
        deriv (BB w₀) (-w) * sin (π - v)) := by
  rw [f1dir, ← rot2_smul, psit, rot2_add_pi, cos_pi_sub, sin_pi_sub]
  have e : nrm w₀ (-w) • (-(zh1 w₀ (-w)), -(zh2 w₀ (-w)) * cos v, -(zh2 w₀ (-w)) * sin v) =
      (-(deriv (AA w₀) (-w)), -(deriv (BB w₀) (-w)) * cos v, -(deriv (BB w₀) (-w)) * sin v) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · rw [← nrm_mul_zh1 h0 h1 (-w)]; ring
    · rw [← nrm_mul_zh2 h0 h1 (-w)]; ring
    · rw [← nrm_mul_zh2 h0 h1 (-w)]; ring
  rw [e]
  simp only [rot2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring

theorem BB_smul_f2dir (w v : ℝ) : BB w₀ (-w) • f2dir w₀ w v = bS w₀ (-w) (π - v) := by
  rw [f2dir, ← rot2_smul, psit, rot2_add_pi, bS, sigV, cos_pi_sub, sin_pi_sub]
  simp only [rot2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Prod.fst_neg, Prod.snd_neg, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

include h0 h1 in
/-- 段 A（s ≤ 5/12）：捻れの項を τ_A ψ′ に縮めた Σ の枠。 -/
theorem J1_of_le {s : ℝ} (hs : s ≤ 5 / 12) (w v : ℝ) :
    J1 w₀ s w v = sigW (psi w₀ w) (AA w₀ w) (BB w₀ w) (deriv (AA w₀) w) (deriv (BB w₀) w)
      (tauA s * deriv (psi w₀) w) v := by
  have hσ : sigB s = 0 := sigB_of_le hs
  have hC : tauC s = 0 := tauC_of_le (by linarith)
  simp only [J1, hσ, hC, Hq_zero, rotQ_one, nB, sub_zero, one_mul, zero_mul, add_zero, zero_smul]
  rw [nrm_smul_e1dir h0 h1, sigW_split, T0, smul_smul]

theorem J2_of_le {s : ℝ} (hs : s ≤ 5 / 12) (w v : ℝ) : J2 w₀ s w v = bS w₀ w v := by
  simp only [J2, sigB_of_le hs, Hq_zero, rotQ_one, bB, sub_zero, one_mul, zero_mul, add_zero]
  exact BB_smul_e2dir w v

include h0 h1 in
/-- 段 C（s ≥ 7/12）：捻れの項を τ_C ψ̃′ に戻した f₁ の枠。 -/
theorem J1_of_ge {s : ℝ} (hs : 7 / 12 ≤ s) (w v : ℝ) :
    J1 w₀ s w v = sigW (psi w₀ (-w)) (AA w₀ (-w)) (BB w₀ (-w)) (deriv (AA w₀) (-w))
      (deriv (BB w₀) (-w)) (tauC s * deriv (psi w₀) (-w)) (π - v) := by
  have hσ : sigB s = 1 := sigB_of_ge hs
  have hA : tauA s = 0 := tauA_of_ge (by linarith)
  simp only [J1, hσ, hA, Hq_one h0 h1, nB, sub_self, zero_mul, zero_add, one_mul, zero_smul,
    add_zero]
  rw [rotQ_smul_vec, rotQ_Psih_e1 h0 h1, nrm_smul_f1dir h0 h1, sigW_split, T1, smul_smul,
    sin_pi_sub]

include h0 h1 in
theorem J2_of_ge {s : ℝ} (hs : 7 / 12 ≤ s) (w v : ℝ) : J2 w₀ s w v = bS w₀ (-w) (π - v) := by
  simp only [J2, sigB_of_ge hs, Hq_one h0 h1, bB, sub_self, zero_mul, zero_add, one_mul]
  rw [rotQ_smul_vec, rotQ_Psih_e2 h0 h1, BB_smul_f2dir]

include h0 h1 in
theorem J1_start {s : ℝ} (hs : s ≤ 1 / 4) (w v : ℝ) : J1 w₀ s w v = aS w₀ w v := by
  rw [J1_of_le h0 h1 (by linarith) w v, tauA_of_le hs, one_mul]
  rfl

theorem J2_start {s : ℝ} (hs : s ≤ 1 / 4) (w v : ℝ) : J2 w₀ s w v = bS w₀ w v :=
  J2_of_le (by linarith) w v

include h0 h1 in
theorem J1_finish {s : ℝ} (hs : 3 / 4 ≤ s) (w v : ℝ) : J1 w₀ s w v = aS w₀ (-w) (π - v) := by
  rw [J1_of_ge h0 h1 (by linarith) w v, tauC_of_ge hs, one_mul]
  rfl

include h0 h1 in
theorem J2_finish {s : ℝ} (hs : 3 / 4 ≤ s) (w v : ℝ) : J2 w₀ s w v = bS w₀ (-w) (π - v) :=
  J2_of_ge h0 h1 (by linarith) w v

include h0 h1 in
/-- 襟では枠は Σ の枠のままである。 -/
theorem J1_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) (s v : ℝ) : J1 w₀ s w v = aS w₀ w v := by
  have hP := Psih_collar h0 h1 hw v
  simp only [J1, Hq_of_Psih_one hP, rotQ_one, nB, nrm_neg_collar h0 hw]
  have e : (1 - sigB s) * nrm w₀ w + sigB s * nrm w₀ w = nrm w₀ w := by ring
  rw [e, nrm_smul_e1dir h0 h1]
  simp only [T0, T1, deriv_psi_collar h0 hw, deriv_psi_neg_collar h0 hw, zero_smul, smul_zero,
    add_zero]
  simp only [aS, sigW_split, deriv_psi_collar h0 hw, zero_smul, add_zero]

include h0 h1 in
theorem J2_collar {w : ℝ} (hw : w₀ ^ 2 / 2 < w ^ 2) (s v : ℝ) : J2 w₀ s w v = bS w₀ w v := by
  simp only [J2, Hq_of_Psih_one (Psih_collar h0 h1 hw v), rotQ_one, bB, BB_neg_collar h0 hw.le]
  have e : (1 - sigB s) * BB w₀ w + sigB s * BB w₀ w = BB w₀ w := by ring
  rw [e]
  exact BB_smul_e2dir w v

theorem dot_smul_left (c : ℝ) (a b : V3) : dot (c • a) b = c * dot a b := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot_smul_right' (c : ℝ) (a b : V3) : dot a (c • b) = c * dot a b := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem nsq_smul' (c : ℝ) (a : V3) : nsq (c • a) = c ^ 2 * nsq a := by
  simp only [nsq, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

include h0 h1 in
theorem nsq_e1dir (w v : ℝ) : nsq (e1dir w₀ w v) = 1 := by
  rw [e1dir, nsq_rot2]
  simp only [nsq, dot]
  have := zh_sq h0 h1 w
  have hv := sin_sq_add_cos_sq v
  linear_combination this + zh2 w₀ w ^ 2 * hv

theorem nsq_e2dir (w v : ℝ) : nsq (e2dir w₀ w v) = 1 := by
  rw [e2dir, nsq_rot2]
  simp only [nsq, dot]
  linear_combination sin_sq_add_cos_sq v

theorem dot_e2dir_e1dir (w v : ℝ) : dot (e2dir w₀ w v) (e1dir w₀ w v) = 0 := by
  rw [e2dir, e1dir, rot2_dot]
  simp only [dot]
  ring

include h0 h1 in
theorem nrm_neg_pos (w : ℝ) : 0 < nrm w₀ (-w) := nrm_pos h0 h1 (-w)

include h0 h1 in
theorem nB_pos {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (w : ℝ) : 0 < nB w₀ σ w := by
  have h1' := nrm_pos h0 h1 w
  have h2' := nrm_pos h0 h1 (-w)
  simp only [nB]
  rcases eq_or_lt_of_le hσ0 with h | h
  · rw [← h]; simp; exact h1'
  · nlinarith

include h0 h1 in
theorem bB_pos {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (w : ℝ) : 0 < bB w₀ σ w := by
  have h1' := BB_pos h0 h1 w
  have h2' := BB_pos h0 h1 (-w)
  simp only [bB]
  rcases eq_or_lt_of_le hσ0 with h | h
  · rw [← h]; simp; exact h1'
  · nlinarith

include h0 h1 in
/-- **2 枠はつねに一次独立である**。 -/
theorem cross_J_ne (s w v : ℝ) : cross (J2 w₀ s w v) (J1 w₀ s w v) ≠ wp := by
  rcases le_or_gt s (5 / 12) with hs | hs
  · rw [J1_of_le h0 h1 hs, J2_of_le hs]
    refine neck_lemma (BB_pos h0 h1 w).ne' (profile_ne h0 h1 w) ?_ v
    intro hd
    have hd' : deriv (psi w₀) w ≠ 0 := fun h => hd (by rw [h, mul_zero])
    obtain ⟨h2, h3⟩ := deriv_psi_ne h0 hd'
    have hw0 : w ≠ 0 := by
      have : 0 < w := by linarith
      exact this.ne'
    exact radial_ne h0.ne' (by nlinarith) hw0 (by nlinarith)
  · rcases le_or_gt (7 / 12) s with hs' | hs'
    · rw [J1_of_ge h0 h1 hs', J2_of_ge h0 h1 hs']
      refine neck_lemma (BB_pos h0 h1 (-w)).ne' (profile_ne h0 h1 (-w)) ?_ (π - v)
      intro hd
      have hd' : deriv (psi w₀) (-w) ≠ 0 := fun h => hd (by rw [h, mul_zero])
      obtain ⟨h2, h3⟩ := deriv_psi_ne h0 hd'
      have hw0 : -w ≠ 0 := by
        have : 0 < -w := by linarith
        exact this.ne'
      exact radial_ne h0.ne' (by nlinarith) hw0 (by nlinarith)
    · have hA : tauA s = 0 := tauA_of_ge hs.le
      have hC : tauC s = 0 := tauC_of_le hs'.le
      intro h
      simp only [J1, J2, hA, hC, zero_smul, add_zero] at h
      have hn := nsq_cross (rotQ (Hq w₀ (sigB s) w v) (bB w₀ (sigB s) w • e2dir w₀ w v))
        (rotQ (Hq w₀ (sigB s) w v) (nB w₀ (sigB s) w • e1dir w₀ w v))
      rw [h, dot_rotQ, nsq_rotQ, nsq_rotQ, qnsq_Hq h0 h1, nsq_smul', nsq_smul', dot_smul_left,
        dot_smul_right', nsq_e1dir h0 h1, nsq_e2dir, dot_e2dir_e1dir] at hn
      have hb := bB_pos h0 h1 (sigB_nonneg s) (sigB_le_one s) w
      have hnn := nB_pos h0 h1 (sigB_nonneg s) (sigB_le_one s) w
      have hz : nsq wp = 0 := by simp [nsq, dot, wp]
      rw [hz] at hn
      have : 0 < bB w₀ (sigB s) w ^ 2 * nB w₀ (sigB s) w ^ 2 := by positivity
      nlinarith

theorem aS_periodic (w v : ℝ) : aS w₀ w (v + 2 * π) = aS w₀ w v := by
  simp only [aS, sigW, sin_add_two_pi, cos_add_two_pi]

theorem bS_periodic (w v : ℝ) : bS w₀ w (v + 2 * π) = bS w₀ w v := by
  simp only [bS, sigV, sin_add_two_pi, cos_add_two_pi]

theorem J1_periodic (s w v : ℝ) : J1 w₀ s w (v + 2 * π) = J1 w₀ s w v := by
  simp only [J1, Hq_periodic, e1dir, T0, T1, sin_add_two_pi, cos_add_two_pi]

theorem J2_periodic (s w v : ℝ) : J2 w₀ s w (v + 2 * π) = J2 w₀ s w v := by
  simp only [J2, Hq_periodic, e2dir, sin_add_two_pi, cos_add_two_pi]

include h0 h1 in
theorem contDiff_e1dir : ContDiff ℝ ∞ (fun p : ℝ × ℝ => e1dir w₀ p.1 p.2) := by
  have hψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => psi w₀ p.1) := (contDiff_psi w₀).comp contDiff_fst
  have hz1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => zh1 w₀ p.1) := (contDiff_zh1 h0 h1).comp contDiff_fst
  have hz2 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => zh2 w₀ p.1) := (contDiff_zh2 h0 h1).comp contDiff_fst
  unfold e1dir rot2
  fun_prop

theorem contDiff_e2dir : ContDiff ℝ ∞ (fun p : ℝ × ℝ => e2dir w₀ p.1 p.2) := by
  have hψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => psi w₀ p.1) := (contDiff_psi w₀).comp contDiff_fst
  unfold e2dir rot2
  fun_prop

include h0 in
theorem contDiff_T0 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => T0 w₀ p.1 p.2) := by
  have hψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => psi w₀ p.1) := (contDiff_psi w₀).comp contDiff_fst
  have hdψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (psi w₀) p.1) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_psi w₀)).2).comp contDiff_fst
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℝ => AA w₀ p.1) := (contDiff_AA h0.ne').comp contDiff_fst
  have hB : ContDiff ℝ ∞ (fun p : ℝ × ℝ => BB w₀ p.1) := (contDiff_BB h0.ne').comp contDiff_fst
  unfold T0 rot2
  fun_prop

include h0 in
theorem contDiff_T1 : ContDiff ℝ ∞ (fun p : ℝ × ℝ => T1 w₀ p.1 p.2) := by
  have hψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => psi w₀ (-p.1)) :=
    (contDiff_psi w₀).comp (contDiff_fst.neg)
  have hdψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (psi w₀) (-p.1)) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_psi w₀)).2).comp contDiff_fst.neg
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℝ => AA w₀ (-p.1)) :=
    (contDiff_AA h0.ne').comp contDiff_fst.neg
  have hB : ContDiff ℝ ∞ (fun p : ℝ × ℝ => BB w₀ (-p.1)) :=
    (contDiff_BB h0.ne').comp contDiff_fst.neg
  unfold T1 rot2
  fun_prop

include h0 h1 in
theorem contDiff_J1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => J1 w₀ q.1 q.2.1 q.2.2) := by
  have hwv : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (q.2.1, q.2.2)) :=
    (contDiff_fst.comp contDiff_snd).prodMk (contDiff_snd.comp contDiff_snd)
  have hσ : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => sigB q.1) := contDiff_sigB.comp contDiff_fst
  have hH : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Hq w₀ (sigB q.1) q.2.1 q.2.2) := by
    have h := (contDiff_Hq h0 h1).comp (hσ.prodMk hwv)
    exact h
  have hn : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => nB w₀ (sigB q.1) q.2.1) := by
    have h1' : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => nrm w₀ q.2.1) :=
      (contDiff_nrm h0 h1).comp (contDiff_fst.comp contDiff_snd)
    have h2' : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => nrm w₀ (-q.2.1)) :=
      (contDiff_nrm h0 h1).comp (contDiff_fst.comp contDiff_snd).neg
    unfold nB
    fun_prop
  have he : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => e1dir w₀ q.2.1 q.2.2) := by
    have h := (contDiff_e1dir h0 h1).comp hwv
    exact h
  have hT0 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => T0 w₀ q.2.1 q.2.2) := by
    have h := (contDiff_T0 h0).comp hwv
    exact h
  have hT1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => T1 w₀ q.2.1 q.2.2) := by
    have h := (contDiff_T1 h0).comp hwv
    exact h
  have hA : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => tauA q.1) := contDiff_tauA.comp contDiff_fst
  have hC : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => tauC q.1) := contDiff_tauC.comp contDiff_fst
  have h1' : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ =>
      rotQ (Hq w₀ (sigB q.1) q.2.1 q.2.2) (nB w₀ (sigB q.1) q.2.1 • e1dir w₀ q.2.1 q.2.2)) :=
    hH.rotQ (hn.smul he)
  have h2' : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => tauA q.1 • T0 w₀ q.2.1 q.2.2) := hA.smul hT0
  have h3' : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => tauC q.1 • T1 w₀ q.2.1 q.2.2) := hC.smul hT1
  exact (h1'.add h2').add h3'

include h0 h1 in
theorem contDiff_J2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => J2 w₀ q.1 q.2.1 q.2.2) := by
  have hwv : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (q.2.1, q.2.2)) :=
    (contDiff_fst.comp contDiff_snd).prodMk (contDiff_snd.comp contDiff_snd)
  have hσ : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => sigB q.1) := contDiff_sigB.comp contDiff_fst
  have hH : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Hq w₀ (sigB q.1) q.2.1 q.2.2) := by
    have h := (contDiff_Hq h0 h1).comp (hσ.prodMk hwv)
    exact h
  have hb : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => bB w₀ (sigB q.1) q.2.1) := by
    have h1' : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => BB w₀ q.2.1) :=
      (contDiff_BB h0.ne').comp (contDiff_fst.comp contDiff_snd)
    have h2' : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => BB w₀ (-q.2.1)) :=
      (contDiff_BB h0.ne').comp (contDiff_fst.comp contDiff_snd).neg
    unfold bB
    fun_prop
  have he : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => e2dir w₀ q.2.1 q.2.2) := by
    have h := (contDiff_e2dir (w₀ := w₀)).comp hwv
    exact h
  exact hH.rotQ (hb.smul he)

include h0 in
theorem contDiff_aS : ContDiff ℝ ∞ (fun p : ℝ × ℝ => aS w₀ p.1 p.2) := by
  have hψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => psi w₀ p.1) := (contDiff_psi w₀).comp contDiff_fst
  have hdψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (psi w₀) p.1) :=
    ((contDiff_infty_iff_deriv.mp (contDiff_psi w₀)).2).comp contDiff_fst
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℝ => AA w₀ p.1) := (contDiff_AA h0.ne').comp contDiff_fst
  have hB : ContDiff ℝ ∞ (fun p : ℝ × ℝ => BB w₀ p.1) := (contDiff_BB h0.ne').comp contDiff_fst
  have hdA : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (AA w₀) p.1) :=
    (contDiff_dAA h0).comp contDiff_fst
  have hdB : ContDiff ℝ ∞ (fun p : ℝ × ℝ => deriv (BB w₀) p.1) :=
    (contDiff_dBB h0).comp contDiff_fst
  unfold aS sigW rot2
  fun_prop

include h0 in
theorem contDiff_bS : ContDiff ℝ ∞ (fun p : ℝ × ℝ => bS w₀ p.1 p.2) := by
  have hψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => psi w₀ p.1) := (contDiff_psi w₀).comp contDiff_fst
  have hB : ContDiff ℝ ∞ (fun p : ℝ × ℝ => BB w₀ p.1) := (contDiff_BB h0.ne').comp contDiff_fst
  unfold bS sigV rot2
  fun_prop

end Frame

/-! ### 形式微分 L：Σ の枠に関する座標で ∂wΣ ↦ J₁、∂ᵥΣ ↦ J₂ -/

section Formal

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

theorem dot_comm' (a b : V3) : dot a b = dot b a := by
  simp only [dot]; ring

theorem dot_add_left (a b u : V3) : dot (a + b) u = dot a u + dot b u := by
  simp only [dot, Prod.fst_add, Prod.snd_add]; ring

/-- u の ∂wΣ 成分（基底 {a, b, a × b} に関する座標）。 -/
def coefA (a b u : V3) : ℝ := (nsq b * dot u a - dot a b * dot u b) / nsq (cross a b)

/-- u の ∂ᵥΣ 成分。 -/
def coefB (a b u : V3) : ℝ := (nsq a * dot u b - dot a b * dot u a) / nsq (cross a b)

theorem coefA_add (a b u u' : V3) : coefA a b (u + u') = coefA a b u + coefA a b u' := by
  simp only [coefA, dot_add_left]; ring

theorem coefB_add (a b u u' : V3) : coefB a b (u + u') = coefB a b u + coefB a b u' := by
  simp only [coefB, dot_add_left]; ring

theorem coefA_smul (a b : V3) (c : ℝ) (u : V3) : coefA a b (c • u) = c * coefA a b u := by
  simp only [coefA, dot_smul_left]; ring

theorem coefB_smul (a b : V3) (c : ℝ) (u : V3) : coefB a b (c • u) = c * coefB a b u := by
  simp only [coefB, dot_smul_left]; ring

theorem coefA_fst {a b : V3} (h : nsq (cross a b) ≠ 0) : coefA a b a = 1 := by
  simp only [coefA]
  rw [div_eq_one_iff_eq h, nsq_cross, dot_comm' a b]
  simp only [nsq]; ring

theorem coefB_fst (a b : V3) : coefB a b a = 0 := by
  simp only [coefB]
  rw [div_eq_zero_iff]; left
  rw [dot_comm' a b]; simp only [nsq]; ring

theorem coefA_snd (a b : V3) : coefA a b b = 0 := by
  simp only [coefA]
  rw [div_eq_zero_iff]; left
  rw [dot_comm' b a]; simp only [nsq]; ring

theorem coefB_snd {a b : V3} (h : nsq (cross a b) ≠ 0) : coefB a b b = 1 := by
  simp only [coefB]
  rw [div_eq_one_iff_eq h, nsq_cross, dot_comm' b a]
  simp only [nsq]; ring

/-- 形式微分の値：u + x (J₁ − ∂wΣ) + y (J₂ − ∂ᵥΣ)。 -/
def Lfun (w₀ s w v : ℝ) (u : V3) : V3 :=
  u + coefA (aS w₀ w v) (bS w₀ w v) u • (J1 w₀ s w v - aS w₀ w v) +
    coefB (aS w₀ w v) (bS w₀ w v) u • (J2 w₀ s w v - bS w₀ w v)

theorem Lfun_add (s w v : ℝ) (u u' : V3) :
    Lfun w₀ s w v (u + u') = Lfun w₀ s w v u + Lfun w₀ s w v u' := by
  simp only [Lfun, coefA_add, coefB_add, add_smul]
  abel

theorem Lfun_smul (s w v : ℝ) (c : ℝ) (u : V3) : Lfun w₀ s w v (c • u) = c • Lfun w₀ s w v u := by
  simp only [Lfun, coefA_smul, coefB_smul, smul_add, smul_smul]

/-- 形式微分 L(s, w, v) ∈ End(ℝ³)。 -/
def Lform (w₀ s w v : ℝ) : V3 →L[ℝ] V3 :=
  LinearMap.toContinuousLinearMap
    { toFun := Lfun w₀ s w v
      map_add' := Lfun_add s w v
      map_smul' := fun c u => by simp only [Lfun_smul, RingHom.id_apply] }

@[simp] theorem Lform_apply (s w v : ℝ) (u : V3) : Lform w₀ s w v u = Lfun w₀ s w v u := rfl

/-- 法線 ∂ᵥΣ × ∂wΣ = Xf は消えない。 -/
theorem cross_bS_aS (w v : ℝ) : cross (bS w₀ w v) (aS w₀ w v) = Xf w₀ w v := rfl

include h0 h1 in
theorem nsq_cross_aS_bS_ne (w v : ℝ) : nsq (cross (aS w₀ w v) (bS w₀ w v)) ≠ 0 := by
  have e : nsq (cross (aS w₀ w v) (bS w₀ w v)) = nsq (cross (bS w₀ w v) (aS w₀ w v)) := by
    rw [nsq_cross, nsq_cross, dot_comm' (aS w₀ w v)]; ring
  rw [e, cross_bS_aS]
  exact (nsq_pos_of_ne (Xf_ne h0 h1 w v)).ne'

include h0 h1 in
theorem Lform_aS (s w v : ℝ) : Lform w₀ s w v (aS w₀ w v) = J1 w₀ s w v := by
  have h := nsq_cross_aS_bS_ne h0 h1 w v
  simp only [Lform_apply, Lfun, coefA_fst h, coefB_fst, one_smul, zero_smul, add_zero]
  abel

include h0 h1 in
theorem Lform_bS (s w v : ℝ) : Lform w₀ s w v (bS w₀ w v) = J2 w₀ s w v := by
  have h := nsq_cross_aS_bS_ne h0 h1 w v
  simp only [Lform_apply, Lfun, coefA_snd, coefB_snd h, one_smul, zero_smul, add_zero]
  abel

theorem Lform_eq_id {s w v : ℝ} (ha : J1 w₀ s w v = aS w₀ w v) (hb : J2 w₀ s w v = bS w₀ w v)
    (u : V3) : Lform w₀ s w v u = u := by
  simp [Lfun, ha, hb]

theorem Lform_periodic (s w v : ℝ) : Lform w₀ s w (v + 2 * π) = Lform w₀ s w v := by
  refine ContinuousLinearMap.ext fun u => ?_
  simp only [Lform_apply, Lfun, aS_periodic, bS_periodic, J1_periodic, J2_periodic]

include h0 h1 in
theorem contDiff_Lform : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Lform w₀ q.1 q.2.1 q.2.2) := by
  rw [contDiff_clm_apply_iff]
  intro u
  have hwv : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (q.2.1, q.2.2)) :=
    (contDiff_fst.comp contDiff_snd).prodMk (contDiff_snd.comp contDiff_snd)
  have ha : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => aS w₀ q.2.1 q.2.2) := by
    have h := (contDiff_aS h0).comp hwv
    exact h
  have hb : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => bS w₀ q.2.1 q.2.2) := by
    have h := (contDiff_bS h0).comp hwv
    exact h
  have hJ1 := contDiff_J1 h0 h1
  have hJ2 := contDiff_J2 h0 h1
  have hdot : ∀ {x y : ℝ × ℝ × ℝ → V3}, ContDiff ℝ ∞ x → ContDiff ℝ ∞ y →
      ContDiff ℝ ∞ (fun q => dot (x q) (y q)) := by
    intro x y hx hy
    have x1 : ContDiff ℝ ∞ (fun q => (x q).1) := contDiff_fst.comp hx
    have x2 : ContDiff ℝ ∞ (fun q => (x q).2.1) := contDiff_fst.comp (contDiff_snd.comp hx)
    have x3 : ContDiff ℝ ∞ (fun q => (x q).2.2) := contDiff_snd.comp (contDiff_snd.comp hx)
    have y1 : ContDiff ℝ ∞ (fun q => (y q).1) := contDiff_fst.comp hy
    have y2 : ContDiff ℝ ∞ (fun q => (y q).2.1) := contDiff_fst.comp (contDiff_snd.comp hy)
    have y3 : ContDiff ℝ ∞ (fun q => (y q).2.2) := contDiff_snd.comp (contDiff_snd.comp hy)
    unfold dot
    fun_prop
  have hcross : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => cross (aS w₀ q.2.1 q.2.2) (bS w₀ q.2.1 q.2.2)) := by
    have x1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (aS w₀ q.2.1 q.2.2).1) := contDiff_fst.comp ha
    have x2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (aS w₀ q.2.1 q.2.2).2.1) :=
      contDiff_fst.comp (contDiff_snd.comp ha)
    have x3 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (aS w₀ q.2.1 q.2.2).2.2) :=
      contDiff_snd.comp (contDiff_snd.comp ha)
    have y1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (bS w₀ q.2.1 q.2.2).1) := contDiff_fst.comp hb
    have y2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (bS w₀ q.2.1 q.2.2).2.1) :=
      contDiff_fst.comp (contDiff_snd.comp hb)
    have y3 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => (bS w₀ q.2.1 q.2.2).2.2) :=
      contDiff_snd.comp (contDiff_snd.comp hb)
    unfold cross
    fun_prop
  have hden : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => nsq (cross (aS w₀ q.2.1 q.2.2) (bS w₀ q.2.1 q.2.2))) :=
    hdot hcross hcross
  have hdenne : ∀ q : ℝ × ℝ × ℝ, nsq (cross (aS w₀ q.2.1 q.2.2) (bS w₀ q.2.1 q.2.2)) ≠ 0 :=
    fun q => nsq_cross_aS_bS_ne h0 h1 _ _
  have hcA : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => coefA (aS w₀ q.2.1 q.2.2) (bS w₀ q.2.1 q.2.2) u) := by
    unfold coefA
    exact (((hdot hb hb).mul (hdot contDiff_const ha)).sub
      ((hdot ha hb).mul (hdot contDiff_const hb))).div hden hdenne
  have hcB : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => coefB (aS w₀ q.2.1 q.2.2) (bS w₀ q.2.1 q.2.2) u) := by
    unfold coefB
    exact (((hdot ha ha).mul (hdot contDiff_const hb)).sub
      ((hdot ha hb).mul (hdot contDiff_const ha))).div hden hdenne
  simp only [Lform_apply, Lfun]
  exact (contDiff_const.add (hcA.smul (hJ1.sub ha))).add (hcB.smul (hJ2.sub hb))

/-! ### Σ と Ŝ の全微分、ホロノミー、単射性 -/

include h0 in
theorem fderiv_Sig_apply (w v : ℝ) (ξ : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => Sig w₀ p.1 p.2) (w, v) ξ = ξ.1 • aS w₀ w v + ξ.2 • bS w₀ w v :=
  fderiv_apply_of_partials ((contDiff_Sig h0.ne').differentiable (by simp) _)
    (hasDerivAt_Sig_w h0.ne' w v) (hasDerivAt_Sig_v w₀ w v) ξ

theorem isOpen_abs_lt_one : IsOpen {p : ℝ × ℝ | |p.1| < 1} :=
  isOpen_lt (continuous_abs.comp continuous_fst) continuous_const

include h0 h1 in
theorem fderiv_Shat_eq_Sig {w : ℝ} (hw : |w| < 1) (v : ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) (w, v) =
      fderiv ℝ (fun p : ℝ × ℝ => Sig w₀ p.1 p.2) (w, v) := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [isOpen_abs_lt_one.mem_nhds (show (w, v) ∈ {p : ℝ × ℝ | |p.1| < 1} from hw)]
    with p hp using Shat_neck h0 h1 (le_of_lt hp) p.2

include h0 h1 in
theorem fderiv_Shat_apply {w : ℝ} (hw : |w| < 1) (v : ℝ) (ξ : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) (w, v) ξ = ξ.1 • aS w₀ w v + ξ.2 • bS w₀ w v := by
  rw [fderiv_Shat_eq_Sig h0 h1 hw, fderiv_Sig_apply h0]

include h0 in
theorem collar_of_abs_ge {w : ℝ} (hw : w₀ * (4 / 5) ≤ |w|) : w₀ ^ 2 / 2 < w ^ 2 := by
  have h2 : (w₀ * (4 / 5)) ^ 2 ≤ |w| ^ 2 := pow_le_pow_left₀ (by positivity) hw 2
  rw [sq_abs] at h2
  nlinarith

include h0 h1 in
/-- **L∘dŜ は全域で単射**。首では 2 枠 (J₁, J₂) の一次独立性、外では L = I と Ŝ のはめ込み性。 -/
theorem Lform_comp_inj (s w v : ℝ) :
    Function.Injective ((Lform w₀ s w v).comp
      (fderiv ℝ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) (w, v))) := by
  by_cases hw : |w| < 1
  · refine (injective_iff_map_eq_zero _).mpr fun ξ hξ => ?_
    rw [ContinuousLinearMap.comp_apply, fderiv_Shat_apply h0 h1 hw, map_add, map_smul, map_smul,
      Lform_aS h0 h1, Lform_bS h0 h1] at hξ
    obtain ⟨h1', h2'⟩ := cross_add_smul ξ.1 ξ.2 (J2 w₀ s w v) (J1 w₀ s w v) hξ
    exact Prod.ext (smul_eq_wp_iff (cross_J_ne h0 h1 s w v) h1')
      (smul_eq_wp_iff (cross_J_ne h0 h1 s w v) h2')
  · push Not at hw
    have hcol : w₀ ^ 2 / 2 < w ^ 2 := collar_of_abs_ge h0 (by nlinarith)
    have hid : (Lform w₀ s w v).comp (fderiv ℝ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) (w, v)) =
        fderiv ℝ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) (w, v) := by
      refine ContinuousLinearMap.ext fun ξ => ?_
      simp only [ContinuousLinearMap.comp_apply]
      exact Lform_eq_id (J1_collar h0 h1 hcol s v) (J2_collar h0 h1 hcol s v) _
    rw [hid]
    exact Shat_immersion h0 h1 (w, v)

/-! ### 基底 B の性質（ホロノミーに要るもの） -/

include h0 h1 in
theorem Bfam_of_le {s : ℝ} (hs : s ≤ 1 / 4) (w v : ℝ) : Bfam w₀ s w v = Shat w₀ w v := by
  simp only [Bfam, lam_of_le hs, Bneck_lam_zero]
  split_ifs with h
  · exact (Shat_neck h0 h1 h v).symm
  · rfl

theorem Bfam_of_ge_neck {s : ℝ} (hs : 3 / 4 ≤ s) {w : ℝ} (hw : |w| ≤ 1) (v : ℝ) :
    Bfam w₀ s w v = -(Sig w₀ (-w) (π - v)) := by
  simp only [Bfam, hw, ↓reduceIte, lam_of_ge hs, Bneck_lam_one]

theorem Sig_sub_two_pi (w v : ℝ) : Sig w₀ w (v - 2 * π) = Sig w₀ w v := by
  rw [← Sig_periodic w₀ w (v - 2 * π), sub_add_cancel]

theorem Bfam_periodic (s w v : ℝ) : Bfam w₀ s w (v + 2 * π) = Bfam w₀ s w v := by
  simp only [Bfam, Bneck, Bline, Brot, sigmaOf, sin_add_two_pi, cos_add_two_pi, Shat_periodic,
    Sig_periodic]
  have e : π - (v + 2 * π) = (π - v) - 2 * π := by ring
  rw [e, Sig_sub_two_pi]

include h0 in
theorem hasDerivAt_negphi_w (w v : ℝ) :
    HasDerivAt (fun w => -(Sig w₀ (-w) (π - v))) (aS w₀ (-w) (π - v)) w := by
  have h := hasDerivAt_Sig_w h0.ne' (-w) (π - v)
  have hneg : HasDerivAt (fun w : ℝ => -w) (-1) w := (hasDerivAt_id w).neg
  have := (h.scomp w hneg).neg
  refine this.congr_deriv ?_
  simp only [aS]
  rw [neg_one_smul, neg_neg]

theorem hasDerivAt_negphi_v (w v : ℝ) :
    HasDerivAt (fun v => -(Sig w₀ (-w) (π - v))) (bS w₀ (-w) (π - v)) v := by
  have h := hasDerivAt_Sig_v w₀ (-w) (π - v)
  have hneg : HasDerivAt (fun v : ℝ => π - v) (-1) v := (hasDerivAt_id v).const_sub π
  have := (h.scomp v hneg).neg
  refine this.congr_deriv ?_
  simp only [bS]
  rw [neg_one_smul, neg_neg]

include h0 in
theorem differentiableAt_negphi (w v : ℝ) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => -(Sig w₀ (-p.1) (π - p.2))) (w, v) := by
  have hS := (contDiff_Sig h0.ne').differentiable (by simp)
  have hl : Differentiable ℝ (fun p : ℝ × ℝ => ((-p.1, π - p.2) : ℝ × ℝ)) := by fun_prop
  exact ((hS.comp hl).neg) (w, v)

include h0 h1 in
/-- **ホロノミー**：s < ¼、s > ¾、|w| > 4w₀/5 では dB_s = L∘dŜ。 -/
theorem klein_hol_identity {s w : ℝ} (hp : s < 1 / 4 ∨ 3 / 4 < s ∨ w₀ * (4 / 5) < |w|) (v : ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => Bfam w₀ s p.1 p.2) (w, v) =
      (Lform w₀ s w v).comp (fderiv ℝ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) (w, v)) := by
  rcases hp with hs | hs | hw
  · have e : (fun p : ℝ × ℝ => Bfam w₀ s p.1 p.2) = fun p => Shat w₀ p.1 p.2 :=
      funext fun p => Bfam_of_le h0 h1 hs.le p.1 p.2
    rw [e]
    refine ContinuousLinearMap.ext fun ξ => ?_
    simp only [ContinuousLinearMap.comp_apply]
    exact (Lform_eq_id (J1_start h0 h1 hs.le w v) (J2_start hs.le w v) _).symm
  · by_cases hw : w₀ * (4 / 5) < |w|
    · -- 襟：B = Ŝ、L = I
      have hopen : IsOpen {p : ℝ × ℝ | w₀ * (4 / 5) < |p.1|} :=
        isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
      have e : (fun p : ℝ × ℝ => Bfam w₀ s p.1 p.2) =ᶠ[𝓝 (w, v)] fun p => Shat w₀ p.1 p.2 := by
        filter_upwards [hopen.mem_nhds (show (w, v) ∈ {p : ℝ × ℝ | w₀ * (4 / 5) < |p.1|} from hw)]
          with p hp using Bfam_eq_Shat h0 h1 hp s p.2
      rw [e.fderiv_eq]
      have hcol := collar_of_abs_ge h0 hw.le
      refine ContinuousLinearMap.ext fun ξ => ?_
      simp only [ContinuousLinearMap.comp_apply]
      exact (Lform_eq_id (J1_collar h0 h1 hcol s v) (J2_collar h0 h1 hcol s v) _).symm
    · push Not at hw
      have hw1 : |w| < 1 := by nlinarith [abs_nonneg w]
      have e : (fun p : ℝ × ℝ => Bfam w₀ s p.1 p.2) =ᶠ[𝓝 (w, v)]
          fun p => -(Sig w₀ (-p.1) (π - p.2)) := by
        filter_upwards [isOpen_abs_lt_one.mem_nhds (show (w, v) ∈ {p : ℝ × ℝ | |p.1| < 1} from hw1)]
          with p hp using Bfam_of_ge_neck hs.le (le_of_lt hp) p.2
      rw [e.fderiv_eq]
      refine ContinuousLinearMap.ext fun ξ => ?_
      rw [fderiv_apply_of_partials (differentiableAt_negphi h0 w v) (hasDerivAt_negphi_w h0 w v)
        (hasDerivAt_negphi_v w v), ContinuousLinearMap.comp_apply, fderiv_Shat_apply h0 h1 hw1,
        map_add, map_smul, map_smul, Lform_aS h0 h1, Lform_bS h0 h1, J1_finish h0 h1 hs.le,
        J2_finish h0 h1 hs.le]
  · have hopen : IsOpen {p : ℝ × ℝ | w₀ * (4 / 5) < |p.1|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_fst)
    have e : (fun p : ℝ × ℝ => Bfam w₀ s p.1 p.2) =ᶠ[𝓝 (w, v)] fun p => Shat w₀ p.1 p.2 := by
      filter_upwards [hopen.mem_nhds (show (w, v) ∈ {p : ℝ × ℝ | w₀ * (4 / 5) < |p.1|} from hw)]
        with p hp using Bfam_eq_Shat h0 h1 hp s p.2
    rw [e.fderiv_eq]
    have hcol := collar_of_abs_ge h0 hw.le
    refine ContinuousLinearMap.ext fun ξ => ?_
    simp only [ContinuousLinearMap.comp_apply]
    exact (Lform_eq_id (J1_collar h0 h1 hcol s v) (J2_collar h0 h1 hcol s v) _).symm

end Formal

end Zeno.Model
