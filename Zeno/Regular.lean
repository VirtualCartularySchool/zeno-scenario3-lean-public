/-
# Zeno.Regular : 定理 B（静止した正則な接続の上の走者）

一枚の静止した面 Σ の上を、亀とアキレスが全時刻で衝突せずに通過する。
岸では走者は理想形の道と同じ点を通り、ゼノンの段階が正確に成り立つ。
無限捻転は有限の捻転数で近似される（設定 2 の「或いは近似的に」）。
表裏の反転、前後の反転、非衝突は別々の結論である。どれも定義に含まれていない。
-/
import Zeno.Neck
import Zeno.Ideal

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### 面の性質 -/

/-- **B1、B2**：正則な接続の面。走者も Side も含まない。 -/
structure IsNeckSurface (w₀ : ℝ) (S X : ℝ → ℝ → V3) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p.1 p.2)
  periodic : ∀ w v, S w (v + 2 * π) = S w v
  normal : ∀ w v, X w v = cross (deriv (fun v => S w v) v) (deriv (fun w => S w v) w)
  normal_cont : Continuous (fun p : ℝ × ℝ => X p.1 p.2)
  normal_ne : ∀ w v, X w v ≠ wp
  immersion : ∀ p, Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => S p.1 p.2) p)
  right : ∀ w v, w₀ ≤ w → S w v = G w v ∧ ∃ k : ℝ, 0 < k ∧ X w v = k • N w v
  left : ∀ w v, w ≤ -w₀ → S w v = G w (π - v) ∧ ∃ k : ℝ, 0 < k ∧ X w v = k • N w (π - v)
  neck_ball : ∀ w v, |w| ≤ w₀ → nsq (S w v) < w₀ ^ 2
  avoids : ∀ w v, S w v ≠ wp

theorem Sig_isNeckSurface {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) :
    IsNeckSurface w₀ (Sig w₀) (Xf w₀) where
  smooth := contDiff_Sig h0.ne'
  periodic := Sig_periodic w₀
  normal := fun w v => by
    rw [(hasDerivAt_Sig_v w₀ w v).deriv, (hasDerivAt_Sig_w h0.ne' w v).deriv]
    rfl
  normal_cont := continuous_Xf h0.ne'
  normal_ne := Xf_ne h0 h1
  immersion := Sig_immersion h0 h1
  right := fun w v hw => by
    have hw' : w₀ * (4 / 5) < w := by nlinarith
    have hpos : 0 < w := by linarith
    refine ⟨Sig_right h0 hw' v, w ^ 3 / D w ^ 3, ?_, Xf_right h0 hw' v⟩
    have := D_pos w
    positivity
  left := fun w v hw => by
    have hw' : w < -(w₀ * (4 / 5)) := by nlinarith
    have hneg : w < 0 := by linarith
    refine ⟨Sig_left h0 hw' v, -(w ^ 3 / D w ^ 3), ?_, Xf_left h0 hw' v⟩
    have hD : 0 < D w ^ 3 := pow_pos (D_pos w) 3
    have h3 : w ^ 3 < 0 := Odd.pow_neg (by decide) hneg
    have := div_neg_of_neg_of_pos h3 hD
    linarith
  neck_ball := fun w v hw => nsq_Sig_neck h0 hw v
  avoids := Sig_ne_wp h0.ne'

/-- 面の連続な法線場。 -/
structure IsNormalField (S : ℝ → ℝ → V3) (n : ℝ × ℝ → V3) : Prop where
  cont : Continuous n
  ne : ∀ p, n p ≠ wp
  perp : ∀ p, dot (n p) (deriv (fun v => S p.1 v) p.2) = 0 ∧
    dot (n p) (deriv (fun w => S w p.2) p.1) = 0

/-- **面の法線の剛性**：連続な法線場は X の定符号の倍に限る。 -/
theorem normal_rigid {S X : ℝ → ℝ → V3} (hX : Continuous (fun p : ℝ × ℝ => X p.1 p.2))
    (hne : ∀ w v, X w v ≠ wp)
    (hdef : ∀ w v, X w v = cross (deriv (fun v => S w v) v) (deriv (fun w => S w v) w))
    {n : ℝ × ℝ → V3} (hn : IsNormalField S n) :
    ∃ c : ℝ × ℝ → ℝ, Continuous c ∧ (∀ p, n p = c p • X p.1 p.2) ∧
      ((∀ p, 0 < c p) ∨ (∀ p, c p < 0)) := by
  refine rigid_normal hX (fun p => hne p.1 p.2) hn.cont hn.ne dense_univ fun p _ => ?_
  obtain ⟨h1, h2⟩ := hn.perp p
  rw [hdef]
  exact cross_of_perp h1 h2

/-- X 自身は法線場である。 -/
theorem dot_cross_left (a b : V3) : dot (cross a b) a = 0 := by
  simp only [dot, cross]; ring

theorem dot_cross_right (a b : V3) : dot (cross a b) b = 0 := by
  simp only [dot, cross]; ring

theorem IsNeckSurface.isNormalField {w₀ : ℝ} {S X : ℝ → ℝ → V3} (h : IsNeckSurface w₀ S X) :
    IsNormalField S (fun p => X p.1 p.2) where
  cont := h.normal_cont
  ne := fun p => h.normal_ne p.1 p.2
  perp := fun p => by
    simp only [h.normal p.1 p.2]
    exact ⟨dot_cross_left _ _, dot_cross_right _ _⟩

theorem side_right {w k : ℝ} (hw : 0 < w) (hk : 0 < k) (v : ℝ) :
    0 < side (G w v) (k • N w v) := by
  rw [side_smul]
  exact mul_pos hk (side_G_N_pos hw v)

theorem side_left {w k : ℝ} (hw : w < 0) (hk : 0 < k) (v : ℝ) :
    side (G w v) (k • N w v) < 0 := by
  rw [side_smul]
  exact mul_neg_of_pos_of_neg hk (side_G_N_neg hw v)

/-- **B3（ラベルによらない形）**：どの連続な法線場でも、右岸と左岸で Φ のラベルが逆になる。 -/
theorem IsNeckSurface.reversal {w₀ : ℝ} (h0 : 0 < w₀) {S X : ℝ → ℝ → V3}
    (h : IsNeckSurface w₀ S X) {n : ℝ × ℝ → V3} (hn : IsNormalField S n) {w₁ w₂ : ℝ}
    (h₁ : w₀ ≤ w₁) (h₂ : w₂ ≤ -w₀) (v₁ v₂ : ℝ) :
    side (S w₁ v₁) (n (w₁, v₁)) * side (S w₂ v₂) (n (w₂, v₂)) < 0 := by
  obtain ⟨c, -, hsm, hs⟩ := normal_rigid h.normal_cont h.normal_ne h.normal hn
  have hh := (side_mul_of_rigid (α := ℝ × ℝ) (n := n) (N₀ := fun p => X p.1 p.2) (c := c) hsm hs
    (q₁ := S w₁ v₁) (q₂ := S w₂ v₂) (p₁ := (w₁, v₁)) (p₂ := (w₂, v₂))).1
  refine hh (mul_neg_of_pos_of_neg ?_ ?_)
  · obtain ⟨e, k, hk, hX⟩ := h.right w₁ v₁ h₁
    simp only [e, hX]
    exact side_right (by linarith) hk v₁
  · obtain ⟨e, k, hk, hX⟩ := h.left w₂ v₂ h₂
    simp only [e, hX]
    exact side_left (by linarith) hk _

/-! ### 走者の角度 -/

theorem s0_half : s₀ (1 / 2) = 1 / 2 := by
  have h : 0 < expNegInvGlue (1 / 2) := expNegInvGlue.pos_of_pos (by norm_num)
  have e : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  unfold Real.smoothTransition
  rw [e]
  field_simp
  norm_num

/-- 岸の間の階段：w ≥ c で 0、w ≤ −c で 1、w = 0 で ½。 -/
def ell (c w : ℝ) : ℝ := 1 - s₀ ((w + c) / (2 * c))

theorem ell_of_ge {c w : ℝ} (hc : 0 < c) (h : c ≤ w) : ell c w = 0 := by
  have : 1 ≤ (w + c) / (2 * c) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  simp [ell, smoothTransition.one_of_one_le this]

theorem ell_of_le {c w : ℝ} (hc : 0 < c) (h : w ≤ -c) : ell c w = 1 := by
  have : (w + c) / (2 * c) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  simp [ell, smoothTransition.zero_of_nonpos this]

theorem ell_zero {c : ℝ} (hc : 0 < c) : ell c 0 = 1 / 2 := by
  have e : ((0 : ℝ) + c) / (2 * c) = 1 / 2 := by field_simp; norm_num
  simp only [ell, e, s0_half]
  norm_num

theorem contDiff_ell (c : ℝ) : ContDiff ℝ ∞ (ell c) := by
  unfold ell
  refine contDiff_const.sub (Real.smoothTransition.contDiff.comp ?_)
  fun_prop

/-- 亀の角度：右岸で 0、左岸で −π、w = 0 で −π/2。 -/
def VtR (c w : ℝ) : ℝ := -π * ell c w

/-- 滑らかにした捻転。ρ > 0 なので w = 0 でも定義される。 -/
def thetaSm (r w₀ w : ℝ) : ℝ := 2 * π * (log (rho w₀ w) / log r)

/-- アキレスの角度：右岸で θ、左岸で π + 4πn₁ − θ、w = 0 で 2πn₁ + π/2。 -/
def VaR (r w₀ c : ℝ) (n₁ : ℕ) (w : ℝ) : ℝ :=
  (1 - ell c w) * thetaSm r w₀ w + ell c w * (π + 4 * π * n₁ - thetaSm r w₀ w)

theorem contDiff_VtR (c : ℝ) : ContDiff ℝ ∞ (VtR c) := by
  unfold VtR
  exact contDiff_const.mul (contDiff_ell c)

theorem contDiff_thetaSm (r : ℝ) {w₀ : ℝ} (h : w₀ ≠ 0) : ContDiff ℝ ∞ (thetaSm r w₀) := by
  unfold thetaSm
  refine contDiff_const.mul (ContDiff.div_const ?_ _)
  exact (contDiff_rho h).log fun w => (rho_pos h w).ne'

theorem contDiff_VaR (r : ℝ) {w₀ : ℝ} (h : w₀ ≠ 0) (c : ℝ) (n₁ : ℕ) :
    ContDiff ℝ ∞ (VaR r w₀ c n₁) := by
  have h1 := contDiff_ell c
  have h2 := contDiff_thetaSm r h
  unfold VaR
  exact ((contDiff_const.sub h1).mul h2).add (h1.mul (contDiff_const.sub h2))

theorem thetaSm_of {r w₀ w : ℝ} (h : w₀ ≠ 0) (hw : w₀ ^ 2 / 2 ≤ w ^ 2) :
    thetaSm r w₀ w = theta r w := by
  simp only [thetaSm, theta, rho_of h hw]

theorem VtR_zero {c : ℝ} (hc : 0 < c) : VtR c 0 = -(π / 2) := by
  simp only [VtR, ell_zero hc]; ring

theorem VaR_zero {r w₀ c : ℝ} (hc : 0 < c) (n₁ : ℕ) :
    VaR r w₀ c n₁ 0 = π / 2 + n₁ * (2 * π) := by
  simp only [VaR, ell_zero hc]; ring

theorem G_sub_nat (w v : ℝ) (n : ℕ) : G w (v - n * (2 * π)) = G w v := by
  simp only [G, cos_sub_nat_mul_two_pi, sin_sub_nat_mul_two_pi]

section OnSurface

variable {w₀ c r : ℝ}

theorem T_right (h0 : 0 < w₀) (hc : w₀ ≤ c) {w : ℝ} (hw : c ≤ w) :
    Sig w₀ w (VtR c w) = G w 0 := by
  have hcp : 0 < c := by linarith
  have e : VtR c w = 0 := by simp [VtR, ell_of_ge hcp hw]
  rw [Sig_right h0 (by nlinarith), e]

theorem T_left (h0 : 0 < w₀) (hc : w₀ ≤ c) {w : ℝ} (hw : w ≤ -c) :
    Sig w₀ w (VtR c w) = G w 0 := by
  have hcp : 0 < c := by linarith
  have e : π - VtR c w = 0 + 2 * π := by simp only [VtR, ell_of_le hcp hw]; ring
  rw [Sig_left h0 (by nlinarith), e, G_periodic]

theorem A_right (h0 : 0 < w₀) (hc : w₀ ≤ c) {w : ℝ} (hw : c ≤ w) (n₁ : ℕ) :
    Sig w₀ w (VaR r w₀ c n₁ w) = G w (theta r w) := by
  have hcp : 0 < c := by linarith
  have hs : w₀ ^ 2 / 2 ≤ w ^ 2 := (sq_of_right h0 (by nlinarith)).le
  have e : VaR r w₀ c n₁ w = theta r w := by
    simp only [VaR, ell_of_ge hcp hw, thetaSm_of h0.ne' hs]; ring
  rw [Sig_right h0 (by nlinarith), e]

theorem A_left (h0 : 0 < w₀) (hc : w₀ ≤ c) {w : ℝ} (hw : w ≤ -c) (n₁ : ℕ) :
    Sig w₀ w (VaR r w₀ c n₁ w) = G w (theta r w) := by
  have hcp : 0 < c := by linarith
  have hs : w₀ ^ 2 / 2 ≤ w ^ 2 := (sq_of_left h0 (by nlinarith)).le
  have e : π - VaR r w₀ c n₁ w = theta r w - ((2 * n₁ : ℕ) : ℝ) * (2 * π) := by
    simp only [VaR, ell_of_le hcp hw, thetaSm_of h0.ne' hs]
    push_cast
    ring
  rw [Sig_left h0 (by nlinarith), e, G_sub_nat]

end OnSurface

/-! ### 走者 -/

namespace Race

variable (R : Race)

/-- 面 S の上の亀。助変数は w = r g(t)、角度は V(w)。 -/
def runT (S : ℝ → ℝ → V3) (V : ℝ → ℝ) (t : ℝ) : V3 := S (R.r * R.g t) (V (R.r * R.g t))

/-- 面 S の上のアキレス。助変数は w = g(t)、角度は V(w)。 -/
def runA (S : ℝ → ℝ → V3) (V : ℝ → ℝ) (t : ℝ) : V3 := S (R.g t) (V (R.g t))

theorem contDiff_g : ContDiff ℝ ∞ R.g := by
  unfold g T A
  fun_prop

end Race

/-! ### 定理 B の結論 -/

/-- **定理 B**：静止した正則な接続の上の走者についての結論の連言。 -/
structure RegularPassage (R : Race) (w₀ c : ℝ) (n₁ : ℕ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ) :
    Prop where
  /-- B1、B2：面。 -/
  surface : IsNeckSurface w₀ S X
  /-- 導線は滑らかである。 -/
  smooth_T : ContDiff ℝ ∞ (R.runT S Vt)
  smooth_A : ContDiff ℝ ∞ (R.runA S Va)
  /-- B3：表裏（ラベルによらない形）。 -/
  reversal : ∀ n, IsNormalField S n → ∀ w₁ w₂ v₁ v₂, w₀ ≤ w₁ → w₂ ≤ -w₀ →
    side (S w₁ v₁) (n (w₁, v₁)) * side (S w₂ v₂) (n (w₂, v₂)) < 0
  /-- B3：亀は +X に立つ。 -/
  side_T_right : ∀ t, c ≤ R.r * R.g t →
    Front (R.runT S Vt t) (X (R.r * R.g t) (Vt (R.r * R.g t)))
  side_T_left : ∀ t, R.r * R.g t ≤ -c →
    Back (R.runT S Vt t) (X (R.r * R.g t) (Vt (R.r * R.g t)))
  /-- B3：アキレスは −X に立つ。 -/
  side_A_right : ∀ t, c ≤ R.g t → Back (R.runA S Va t) (-X (R.g t) (Va (R.g t)))
  side_A_left : ∀ t, R.g t ≤ -c → Front (R.runA S Va t) (-X (R.g t) (Va (R.g t)))
  /-- B4：岸では理想形と同じ点を通る。 -/
  agree_T : ∀ t, c ≤ |R.r * R.g t| → R.runT S Vt t = R.idealT t
  agree_A : ∀ t, c ≤ |R.g t| → R.runA S Va t = R.idealA t
  /-- B5：ゼノンの段階。 -/
  step_before : ∀ k < n₁, R.runA S Va (R.tn (k + 1)) = R.runT S Vt (R.tn k)
  step_after : ∀ k < n₁, R.runT S Vt (R.tn' k) = R.runA S Va (R.tn' (k + 1))
  /-- B6：非衝突。 -/
  nearer : ∀ t ∈ Icc 0 (2 * R.tstar), t ≠ R.tstar → nsq (R.runT S Vt t) < nsq (R.runA S Va t)
  antipodal : ∃ A₀ B₀ : ℝ, 0 < B₀ ∧ R.runT S Vt R.tstar = (-A₀, 0, B₀) ∧
    R.runA S Va R.tstar = (-A₀, 0, -B₀)
  no_collision : ∀ t ∈ Icc 0 (2 * R.tstar), R.runT S Vt t ≠ R.runA S Va t
  min_dist : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), d ≤ nsq (R.runT S Vt t - R.runA S Va t)
  thick : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), ∀ e₁ e₂ : V3, nsq e₁ < d → nsq e₂ < d →
    R.runT S Vt t + e₁ ≠ R.runA S Va t + e₂
  /-- B7：比較の値の一致は位置の一致ではない。 -/
  compare_before : ∀ t, t < R.tstar → R.r * R.g t - R.g t < 0
  compare_after : ∀ t, R.tstar < t → 0 < R.r * R.g t - R.g t
  compare_zero : ∀ t, R.r * R.g t - R.g t = 0 ↔ t = R.tstar
  compare_not_collision : R.r * R.g R.tstar - R.g R.tstar = 0 ∧
    R.runT S Vt R.tstar ≠ R.runA S Va R.tstar
  /-- B7：どちらの走者も t∗ までは ℘ に近づき、以後は遠ざかる。 -/
  approach_T : StrictAntiOn (fun t => nsq (R.runT S Vt t)) (Icc 0 R.tstar)
  approach_A : StrictAntiOn (fun t => nsq (R.runA S Va t)) (Icc 0 R.tstar)
  recede_T : StrictMonoOn (fun t => nsq (R.runT S Vt t)) (Icc R.tstar (2 * R.tstar))
  recede_A : StrictMonoOn (fun t => nsq (R.runA S Va t)) (Icc R.tstar (2 * R.tstar))
  /-- B7：追従の向き。t∗ までは亀がアキレスの過去の位置に来ることはなく、t∗ 以後はその逆。 -/
  follow_before : ∀ s t, 0 ≤ s → s < t → t ≤ R.tstar → R.runT S Vt t ≠ R.runA S Va s
  follow_after : ∀ s t, R.tstar ≤ s → s < t → t ≤ 2 * R.tstar → R.runA S Va t ≠ R.runT S Vt s

theorem nsq_pos_of_ne {q : V3} (h : q ≠ wp) : 0 < nsq q := by
  have h1 := dot_self_ne h
  have h2 : 0 ≤ dot q q := by
    simp only [dot]; nlinarith [mul_self_nonneg q.1, mul_self_nonneg q.2.1, mul_self_nonneg q.2.2]
  exact lt_of_le_of_ne h2 h1.symm

theorem nsq_sub_le (a b : V3) : nsq (a - b) ≤ 2 * nsq a + 2 * nsq b := by
  simp only [nsq, dot, Prod.fst_sub, Prod.snd_sub]
  nlinarith [sq_nonneg (a.1 + b.1), sq_nonneg (a.2.1 + b.2.1), sq_nonneg (a.2.2 + b.2.2)]

section Proof

variable (R : Race) {w₀ c : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (hc : w₀ ≤ c) (n₁ : ℕ)

local notation "TT" => Race.runT R (Sig w₀) (VtR c)
local notation "AR" => Race.runA R (Sig w₀) (VaR (Race.r R) w₀ c n₁)

include h0 in
theorem reg_smooth_T : ContDiff ℝ ∞ TT := by
  have h := contDiff_Sig (w₀ := w₀) h0.ne'
  have hrg : ContDiff ℝ ∞ (fun t => R.r * R.g t) := contDiff_const.mul R.contDiff_g
  have hV : ContDiff ℝ ∞ (fun t => VtR c (R.r * R.g t)) := (contDiff_VtR c).comp hrg
  have hp : ContDiff ℝ ∞ (fun t => ((R.r * R.g t, VtR c (R.r * R.g t)) : ℝ × ℝ)) := hrg.prodMk hV
  have h2 := h.comp hp
  exact h2

include h0 in
theorem reg_smooth_A : ContDiff ℝ ∞ AR := by
  have h := contDiff_Sig (w₀ := w₀) h0.ne'
  have hg := R.contDiff_g
  have hV : ContDiff ℝ ∞ (fun t => VaR R.r w₀ c n₁ (R.g t)) :=
    (contDiff_VaR R.r h0.ne' c n₁).comp hg
  have hp : ContDiff ℝ ∞ (fun t => ((R.g t, VaR R.r w₀ c n₁ (R.g t)) : ℝ × ℝ)) := hg.prodMk hV
  have h2 := h.comp hp
  exact h2

include h0 h1 in
theorem reg_nearer : ∀ t ∈ Icc 0 (2 * R.tstar), t ≠ R.tstar → nsq (TT t) < nsq (AR t) := by
  intro t ht htne
  exact nsq_Sig_lt h0.ne' (by nlinarith) (R.abs_r_g_lt htne) (R.abs_g_le ht.1 ht.2) _ _

include h0 hc in
theorem reg_Ts : TT R.tstar = (-AA w₀ 0, 0, BB w₀ 0) := by
  have hcp : 0 < c := by linarith
  simp only [Race.runT, R.g_tstar, mul_zero, VtR_zero hcp, Sig_zero h0, cos_neg, sin_neg,
    cos_pi_div_two, sin_pi_div_two]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp

include h0 hc in
theorem reg_As : AR R.tstar = (-AA w₀ 0, 0, -BB w₀ 0) := by
  have hcp : 0 < c := by linarith
  simp only [Race.runA, R.g_tstar, VaR_zero hcp, Sig_zero h0, cos_add_nat_mul_two_pi,
    sin_add_nat_mul_two_pi, cos_pi_div_two, sin_pi_div_two]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp

include h0 h1 hc in
theorem reg_TAs : TT R.tstar ≠ AR R.tstar := by
  rw [reg_Ts R h0 hc, reg_As R h0 hc n₁]
  intro h
  have h2 : BB w₀ 0 = -BB w₀ 0 := congrArg (fun z : V3 => z.2.2) h
  have := BB_pos h0 h1 0
  linarith

include h0 h1 hc in
theorem reg_no_collision : ∀ t ∈ Icc 0 (2 * R.tstar), TT t ≠ AR t := by
  intro t ht
  by_cases hts' : t = R.tstar
  · rw [hts']; exact reg_TAs R h0 h1 hc n₁
  · intro h
    have := reg_nearer (c := c) R h0 h1 n₁ t ht hts'
    rw [h] at this
    exact lt_irrefl _ this

include h0 h1 hc in
theorem reg_min : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), d ≤ nsq (TT t - AR t) := by
  have hcont : Continuous fun t => nsq (TT t - AR t) := by
    have hT := (reg_smooth_T (c := c) R h0).continuous
    have hA := (reg_smooth_A (c := c) R h0 n₁).continuous
    unfold nsq
    exact continuous_dot.comp ((hT.sub hA).prodMk (hT.sub hA))
  have hne' : (Icc 0 (2 * R.tstar)).Nonempty := ⟨0, le_rfl, by have := R.tstar_pos; positivity⟩
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne' hcont.continuousOn
  exact ⟨_, nsq_pos_of_ne (sub_ne_zero.mpr (reg_no_collision R h0 h1 hc n₁ t₀ ht₀)),
    fun t ht => hmin ht⟩

include h0 h1 hc in
theorem reg_thick : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), ∀ e₁ e₂ : V3, nsq e₁ < d → nsq e₂ < d →
    TT t + e₁ ≠ AR t + e₂ := by
  obtain ⟨d, hd, hdm⟩ := reg_min R h0 h1 hc n₁
  refine ⟨d / 4, by positivity, fun t ht e₁ e₂ h₁ h₂ he => ?_⟩
  have h3 := hdm t ht
  have e : TT t - AR t = e₂ - e₁ := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm e₂]
    exact he
  rw [e] at h3
  have h4 := nsq_sub_le e₂ e₁
  linarith

include h0 h1 in
theorem reg_approach_T : StrictAntiOn (fun t => nsq (TT t)) (Icc 0 R.tstar) := by
  intro s hs t ht hst
  have hts := R.tstar_pos
  refine nsq_Sig_lt h0.ne' (by nlinarith) ?_
    ((R.abs_r_g_le s).trans (R.abs_g_le hs.1 (hs.2.trans (by linarith)))) _ _
  rw [abs_mul, abs_mul, abs_of_pos R.r_pos]
  exact mul_lt_mul_of_pos_left (R.abs_g_lt_before hst ht.2) R.r_pos

include h0 h1 in
theorem reg_approach_A : StrictAntiOn (fun t => nsq (AR t)) (Icc 0 R.tstar) := by
  intro s hs t ht hst
  have hts := R.tstar_pos
  exact nsq_Sig_lt h0.ne' (by nlinarith) (R.abs_g_lt_before hst ht.2)
    (R.abs_g_le hs.1 (hs.2.trans (by linarith))) _ _

include h0 h1 in
theorem reg_recede_T : StrictMonoOn (fun t => nsq (TT t)) (Icc R.tstar (2 * R.tstar)) := by
  intro s hs t ht hst
  have hts := R.tstar_pos
  refine nsq_Sig_lt h0.ne' (by nlinarith) ?_
    ((R.abs_r_g_le t).trans (R.abs_g_le (by linarith [ht.1]) ht.2)) _ _
  rw [abs_mul, abs_mul, abs_of_pos R.r_pos]
  exact mul_lt_mul_of_pos_left (R.abs_g_lt_after hs.1 hst) R.r_pos

include h0 h1 in
theorem reg_recede_A : StrictMonoOn (fun t => nsq (AR t)) (Icc R.tstar (2 * R.tstar)) := by
  intro s hs t ht hst
  have hts := R.tstar_pos
  exact nsq_Sig_lt h0.ne' (by nlinarith) (R.abs_g_lt_after hs.1 hst)
    (R.abs_g_le (by linarith [ht.1]) ht.2) _ _

include h0 h1 in
theorem reg_follow_before : ∀ s t, 0 ≤ s → s < t → t ≤ R.tstar → TT t ≠ AR s := by
  intro s t hs hst ht he
  have hts := R.tstar_pos
  have hlt : |R.r * R.g t| < |R.g s| := (R.abs_r_g_le t).trans_lt (R.abs_g_lt_before hst ht)
  have := nsq_Sig_lt (w₀ := w₀) h0.ne' (by nlinarith) hlt
    (R.abs_g_le hs (by linarith)) (VtR c (R.r * R.g t)) (VaR R.r w₀ c n₁ (R.g s))
  simp only [Race.runT, Race.runA] at he
  rw [he] at this
  exact lt_irrefl _ this

include h0 h1 in
theorem reg_follow_after : ∀ s t, R.tstar ≤ s → s < t → t ≤ 2 * R.tstar → AR t ≠ TT s := by
  intro s t hs hst ht he
  have hts := R.tstar_pos
  have hlt : |R.r * R.g s| < |R.g t| := (R.abs_r_g_le s).trans_lt (R.abs_g_lt_after hs hst)
  have := nsq_Sig_lt (w₀ := w₀) h0.ne' (by nlinarith) hlt
    (R.abs_g_le (by linarith) ht) (VtR c (R.r * R.g s)) (VaR R.r w₀ c n₁ (R.g t))
  simp only [Race.runT, Race.runA] at he
  rw [← he] at this
  exact lt_irrefl _ this

theorem reg_compare_zero (t : ℝ) : R.r * R.g t - R.g t = 0 ↔ t = R.tstar := by
  constructor
  · intro h
    have h2 : (R.r - 1) * R.g t = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h' | h'
    · have := R.r_lt_one; linarith
    · exact (R.g_eq_zero_iff t).mp h'
  · rintro rfl
    simp [R.g_tstar]

include h0 h1 hc in
theorem reg_side_T_right (t : ℝ) (ht : c ≤ R.r * R.g t) :
    Front (TT t) (Xf w₀ (R.r * R.g t) (VtR c (R.r * R.g t))) := by
  obtain ⟨e, k, hk, hX⟩ := (Sig_isNeckSurface h0 h1).right (R.r * R.g t) (VtR c (R.r * R.g t))
    (hc.trans ht)
  simp only [Front, Race.runT, e, hX]
  exact side_right (by linarith) hk _

include h0 h1 hc in
theorem reg_side_T_left (t : ℝ) (ht : R.r * R.g t ≤ -c) :
    Back (TT t) (Xf w₀ (R.r * R.g t) (VtR c (R.r * R.g t))) := by
  obtain ⟨e, k, hk, hX⟩ := (Sig_isNeckSurface h0 h1).left (R.r * R.g t) (VtR c (R.r * R.g t))
    (by linarith)
  simp only [Back, Race.runT, e, hX]
  exact side_left (by linarith) hk _

include h0 h1 hc in
theorem reg_side_A_right (t : ℝ) (ht : c ≤ R.g t) :
    Back (AR t) (-Xf w₀ (R.g t) (VaR R.r w₀ c n₁ (R.g t))) := by
  obtain ⟨e, k, hk, hX⟩ := (Sig_isNeckSurface h0 h1).right (R.g t) (VaR R.r w₀ c n₁ (R.g t))
    (hc.trans ht)
  simp only [Back, Race.runA, e, hX, side_neg]
  have := side_right (w := R.g t) (by linarith) hk (VaR R.r w₀ c n₁ (R.g t))
  linarith

include h0 h1 hc in
theorem reg_side_A_left (t : ℝ) (ht : R.g t ≤ -c) :
    Front (AR t) (-Xf w₀ (R.g t) (VaR R.r w₀ c n₁ (R.g t))) := by
  obtain ⟨e, k, hk, hX⟩ := (Sig_isNeckSurface h0 h1).left (R.g t) (VaR R.r w₀ c n₁ (R.g t))
    (by linarith)
  simp only [Front, Race.runA, e, hX, side_neg]
  have := side_left (w := R.g t) (by linarith) hk (π - VaR R.r w₀ c n₁ (R.g t))
  linarith

include h0 hc in
theorem reg_agree_T (t : ℝ) (ht : c ≤ |R.r * R.g t|) : TT t = R.idealT t := by
  simp only [Race.runT, Race.idealT]
  rcases le_abs.mp ht with h | h
  · exact T_right h0 hc h
  · exact T_left h0 hc (by linarith)

include h0 hc in
theorem reg_agree_A (t : ℝ) (ht : c ≤ |R.g t|) : AR t = R.idealA t := by
  simp only [Race.runA, Race.idealA]
  rcases le_abs.mp ht with h | h
  · exact A_right h0 hc h n₁
  · exact A_left h0 hc (by linarith) n₁

include h0 hc in
theorem reg_step_before (k : ℕ) (hp : c ≤ R.r ^ (k + 1)) : AR (R.tn (k + 1)) = TT (R.tn k) := by
  have e1 : R.r * R.g (R.tn k) = R.r ^ (k + 1) := by
    rw [R.g_tn, pow_succ']
  simp only [Race.runA, Race.runT, R.g_tn (k + 1), e1]
  rw [A_right h0 hc hp n₁, T_right h0 hc hp,
    G_theta_pow R.r_pos R.r_lt_one (k := k + 1) (abs_of_pos (pow_pos R.r_pos _))]

include h0 hc in
theorem reg_step_after (k : ℕ) (hp : c ≤ R.r ^ (k + 1)) : TT (R.tn' k) = AR (R.tn' (k + 1)) := by
  have e1 : R.r * R.g (R.tn' k) = -R.r ^ (k + 1) := by
    rw [R.g_tn', pow_succ']; ring
  simp only [Race.runA, Race.runT, R.g_tn' (k + 1), e1]
  have hp' : -R.r ^ (k + 1) ≤ -c := by linarith
  rw [A_left h0 hc hp' n₁, T_left h0 hc hp',
    G_theta_pow R.r_pos R.r_lt_one (k := k + 1) (by rw [abs_neg, abs_of_pos (pow_pos R.r_pos _)])]

end Proof

/-- **定理 B**。 -/
theorem regular_passage (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (n₁ : ℕ)
    (hc : w₀ ≤ R.r ^ n₁) :
    RegularPassage R w₀ (R.r ^ n₁) n₁ (Sig w₀) (Xf w₀) (VtR (R.r ^ n₁))
      (VaR R.r w₀ (R.r ^ n₁) n₁) where
  surface := Sig_isNeckSurface h0 h1
  smooth_T := reg_smooth_T R h0
  smooth_A := reg_smooth_A R h0 n₁
  reversal := fun n hn w₁ w₂ v₁ v₂ h₁ h₂ =>
    (Sig_isNeckSurface h0 h1).reversal h0 hn h₁ h₂ v₁ v₂
  side_T_right := reg_side_T_right R h0 h1 hc
  side_T_left := reg_side_T_left R h0 h1 hc
  side_A_right := reg_side_A_right R h0 h1 hc n₁
  side_A_left := reg_side_A_left R h0 h1 hc n₁
  agree_T := reg_agree_T R h0 hc
  agree_A := reg_agree_A R h0 hc n₁
  step_before := fun k hk => reg_step_before R h0 hc n₁ k
    (pow_le_pow_of_le_one R.r_pos.le R.r_lt_one.le hk)
  step_after := fun k hk => reg_step_after R h0 hc n₁ k
    (pow_le_pow_of_le_one R.r_pos.le R.r_lt_one.le hk)
  nearer := reg_nearer R h0 h1 n₁
  antipodal := ⟨AA w₀ 0, BB w₀ 0, BB_pos h0 h1 0, reg_Ts R h0 hc, reg_As R h0 hc n₁⟩
  no_collision := reg_no_collision R h0 h1 hc n₁
  min_dist := reg_min R h0 h1 hc n₁
  thick := reg_thick R h0 h1 hc n₁
  compare_before := fun t ht => by
    have := R.g_pos_of_lt ht
    nlinarith [R.r_lt_one]
  compare_after := fun t ht => by
    have := R.g_neg_of_gt ht
    nlinarith [R.r_lt_one]
  compare_zero := reg_compare_zero R
  compare_not_collision := ⟨by simp [R.g_tstar], reg_TAs R h0 h1 hc n₁⟩
  approach_T := reg_approach_T R h0 h1
  approach_A := reg_approach_A R h0 h1 n₁
  recede_T := reg_recede_T R h0 h1
  recede_A := reg_recede_A R h0 h1 n₁
  follow_before := reg_follow_before R h0 h1 n₁
  follow_after := reg_follow_after R h0 h1 n₁

/-! ### 理想形への収束（「或いは近似的に」） -/

theorem tendsto_wp_of_nsq {α : Type*} {l : Filter α} {x : α → V3}
    (h : Tendsto (fun a => nsq (x a)) l (𝓝 0)) : Tendsto x l (𝓝 wp) := by
  have hs : Tendsto (fun a => √(nsq (x a))) l (𝓝 0) := by
    simpa using h.sqrt
  have c1 : Tendsto (fun a => (x a).1) l (𝓝 0) := by
    refine squeeze_zero_norm (fun a => ?_) hs
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    simp only [nsq, dot]
    nlinarith [mul_self_nonneg (x a).2.1, mul_self_nonneg (x a).2.2]
  have c2 : Tendsto (fun a => (x a).2.1) l (𝓝 0) := by
    refine squeeze_zero_norm (fun a => ?_) hs
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    simp only [nsq, dot]
    nlinarith [mul_self_nonneg (x a).1, mul_self_nonneg (x a).2.2]
  have c3 : Tendsto (fun a => (x a).2.2) l (𝓝 0) := by
    refine squeeze_zero_norm (fun a => ?_) hs
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    simp only [nsq, dot]
    nlinarith [mul_self_nonneg (x a).1, mul_self_nonneg (x a).2.1]
  exact c1.prodMk_nhds (c2.prodMk_nhds c3)

theorem nsq_nonneg (q : V3) : 0 ≤ nsq q := by
  simp only [nsq, dot]
  nlinarith [mul_self_nonneg q.1, mul_self_nonneg q.2.1, mul_self_nonneg q.2.2]

/-- **B から A へ（亀）**：首を細くすると、正則形の亀は各時刻で理想形の亀に収束する。 -/
theorem regular_tendsto_T (R : Race) (t : ℝ) :
    Tendsto (fun n : ℕ => R.runT (Sig (R.r ^ n)) (VtR (R.r ^ n)) t) atTop (𝓝 (R.idealT t)) := by
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  by_cases ht : t = R.tstar
  · have e : R.idealT t = wp := by
      subst ht
      simp [Race.idealT, R.g_tstar, G_zero]
    rw [e]
    apply tendsto_wp_of_nsq
    have hsq : Tendsto (fun n : ℕ => (R.r ^ n) ^ 2) atTop (𝓝 0) := by
      simpa using hpow.pow 2
    refine squeeze_zero (fun n => nsq_nonneg _) (fun n => ?_) hsq
    subst ht
    simp only [Race.runT, R.g_tstar, mul_zero]
    exact (nsq_Sig_neck (pow_pos hr0 n) (by simpa using (pow_pos hr0 n).le) _).le
  · have hpos : 0 < |R.r * R.g t| := abs_pos.mpr (mul_ne_zero hr0.ne' (R.g_ne_zero ht))
    have hev : ∀ᶠ n : ℕ in atTop, R.r ^ n < |R.r * R.g t| := hpow.eventually (gt_mem_nhds hpos)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    exact (reg_agree_T R (pow_pos hr0 n) le_rfl t hn.le).symm

/-- **B から A へ（アキレス）**。 -/
theorem regular_tendsto_A (R : Race) (t : ℝ) :
    Tendsto (fun n : ℕ => R.runA (Sig (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n) t) atTop
      (𝓝 (R.idealA t)) := by
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1
  by_cases ht : t = R.tstar
  · have e : R.idealA t = wp := by
      subst ht
      simp [Race.idealA, R.g_tstar, G_zero]
    rw [e]
    apply tendsto_wp_of_nsq
    have hsq : Tendsto (fun n : ℕ => (R.r ^ n) ^ 2) atTop (𝓝 0) := by
      simpa using hpow.pow 2
    refine squeeze_zero (fun n => nsq_nonneg _) (fun n => ?_) hsq
    subst ht
    simp only [Race.runA, R.g_tstar]
    exact (nsq_Sig_neck (pow_pos hr0 n) (by simpa using (pow_pos hr0 n).le) _).le
  · have hpos : 0 < |R.g t| := abs_pos.mpr (R.g_ne_zero ht)
    have hev : ∀ᶠ n : ℕ in atTop, R.r ^ n < |R.g t| := hpow.eventually (gt_mem_nhds hpos)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    exact (reg_agree_A R (pow_pos hr0 n) le_rfl n t hn.le).symm

end Zeno.Model
