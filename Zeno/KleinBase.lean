/-
# Zeno.KleinBase : 首の裏返しの基底 B と、基底の上の走者

h 原理に渡す基底の写像 B(s, w, v) を明示的に定義し、その性質 (B1)〜(B8) を証明する。
- 深い首 |w| ≤ w₀/2 では回転形 B_rot = sigmaOf A_λ B_λ Θ_λ：半径が静的な Σ と同一（`nsq_Brot`）、
  中央円は rot2(λπ) で回る（`Brot_zero`）。
- 首の端 4w₀/5 < |w| ≤ 1 では B = Σ = Ŝ、首の外では B = Ŝ。
- λ = 0 で B = Ŝ、λ = 1 で B = −Ŝ∘φ、φ(w, v) = (−w, π − v)。

窓 [t₁, t₂]（t∗ が中心）と時刻の対応 sched、再径数化 λ(s) を定義し、
基底の上の走者 baseT、baseA について、半径の恒等式、非衝突、追従、t∗ での位置と回転の対応、
コンパクト性による最小距離を証明する。これらは F に依らず、基底と静的な走者だけで決まる。
-/
import Zeno.KleinRun

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### 再径数化 λ -/

/-- λ(s) = s₀(2s − ½)：s ≤ ¼ で 0、s ≥ ¾ で 1、λ(½) = ½。 -/
def lam (s : ℝ) : ℝ := s₀ (2 * s - 1 / 2)

theorem lam_of_le {s : ℝ} (hs : s ≤ 1 / 4) : lam s = 0 :=
  smoothTransition.zero_of_nonpos (by linarith)

theorem lam_of_ge {s : ℝ} (hs : 3 / 4 ≤ s) : lam s = 1 :=
  smoothTransition.one_of_one_le (by linarith)

theorem lam_half : lam (1 / 2) = 1 / 2 := by
  have e : 2 * (1 / 2 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [lam, e, s0_half]

theorem lam_nonneg (s : ℝ) : 0 ≤ lam s := smoothTransition.nonneg _

theorem lam_le_one (s : ℝ) : lam s ≤ 1 := smoothTransition.le_one _

theorem contDiff_lam : ContDiff ℝ ∞ lam := by
  unfold lam
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

/-! ### 基底の写像 -/

/-- μ_λ(w) = (1 − 2λ) κ(w)。 -/
def mu (w₀ l w : ℝ) : ℝ := (1 - 2 * l) * kap w₀ w

/-- A_λ = aa(ρ) cos μ_λ − bb(ρ) sin μ_λ。 -/
def Al (w₀ l w : ℝ) : ℝ := aa (rho w₀ w) * cos (mu w₀ l w) - bb (rho w₀ w) * sin (mu w₀ l w)

/-- B_λ = aa(ρ) sin μ_λ + bb(ρ) cos μ_λ。 -/
def Bl (w₀ l w : ℝ) : ℝ := aa (rho w₀ w) * sin (mu w₀ l w) + bb (rho w₀ w) * cos (mu w₀ l w)

/-- Θ_λ(w) = (1 − λ) ψ(w) + λ (ψ(−w) + π)。 -/
def Thl (w₀ l w : ℝ) : ℝ := (1 - l) * psi w₀ w + l * (psi w₀ (-w) + π)

/-- 回転形の基底 B_rot。 -/
def Brot (w₀ l w v : ℝ) : V3 := sigmaOf (Al w₀ l) (Bl w₀ l) (Thl w₀ l) w v

/-- 直線の基底 B_line = (1 − λ) Σ + λ (−Σ∘φ)。 -/
def Bline (w₀ l w v : ℝ) : V3 := (1 - l) • Sig w₀ w v + l • (-(Sig w₀ (-w) (π - v)))

/-- 切り落とし χ(w) = cut(w₀²)(w²)：|w| ≤ w₀/2 で 1、|w| ≥ w₀/√2 で 0。 -/
def chi (w₀ w : ℝ) : ℝ := cut (w₀ ^ 2) (w ^ 2)

/-- 首の基底 B_neck = (1 − χ) B_line + χ B_rot。 -/
def Bneck (w₀ l w v : ℝ) : V3 := (1 - chi w₀ w) • Bline w₀ l w v + chi w₀ w • Brot w₀ l w v

/-- 基底の族 B(s, w, v)：首 |w| ≤ 1 では B_neck(λ(s))、外では Ŝ。 -/
def Bfam (w₀ s w v : ℝ) : V3 := if |w| ≤ 1 then Bneck w₀ (lam s) w v else Shat w₀ w v

section Base

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

/-! #### 補助：rot2 の加法性、ρ と κ の偶奇 -/

theorem rot2_add (a b : ℝ) (q : V3) : rot2 (a + b) q = rot2 a (rot2 b q) := by
  simp only [rot2, cos_add, sin_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem rot2_add_pi (θ : ℝ) (q : V3) : rot2 (θ + π) q = -(rot2 θ (q.1, -q.2.1, q.2.2)) := by
  simp only [rot2, cos_add_pi, sin_add_pi]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring

theorem rho_neg (w₀ w : ℝ) : rho w₀ (-w) = rho w₀ w := by
  simp [rho]

theorem kap_neg (w₀ w : ℝ) : kap w₀ (-w) = -kap w₀ w := by
  simp only [kap, neg_sq]; ring

theorem kap_zero' (w₀ : ℝ) : kap w₀ 0 = 0 := by simp [kap]

theorem AA_zero (w₀ : ℝ) : AA w₀ 0 = aa (rho w₀ 0) := by simp [AA, kap_zero']

theorem BB_zero (w₀ : ℝ) : BB w₀ 0 = bb (rho w₀ 0) := by simp [BB, kap_zero']

/-! #### (B1)：端点 -/

theorem mu_zero (w₀ w : ℝ) : mu w₀ 0 w = kap w₀ w := by simp [mu]

theorem mu_one (w₀ w : ℝ) : mu w₀ 1 w = -kap w₀ w := by simp [mu]; ring

theorem Al_zero (w₀ w : ℝ) : Al w₀ 0 w = AA w₀ w := by simp [Al, AA, mu_zero]

theorem Bl_zero (w₀ w : ℝ) : Bl w₀ 0 w = BB w₀ w := by simp [Bl, BB, mu_zero]

theorem Thl_zero (w₀ w : ℝ) : Thl w₀ 0 w = psi w₀ w := by simp [Thl]

theorem Al_one (w₀ w : ℝ) : Al w₀ 1 w = AA w₀ (-w) := by
  simp only [Al, AA, mu_one, rho_neg, kap_neg, cos_neg, sin_neg]

theorem Bl_one (w₀ w : ℝ) : Bl w₀ 1 w = BB w₀ (-w) := by
  simp only [Bl, BB, mu_one, rho_neg, kap_neg, cos_neg, sin_neg]

theorem Thl_one (w₀ w : ℝ) : Thl w₀ 1 w = psi w₀ (-w) + π := by simp [Thl]

/-- (B1) λ = 0：B_rot = Σ。 -/
theorem Brot_lam_zero (w₀ w v : ℝ) : Brot w₀ 0 w v = Sig w₀ w v := by
  simp only [Brot, Sig, sigmaOf, Al_zero, Bl_zero, Thl_zero]

/-- (B1) λ = 1：B_rot = −Σ∘φ。 -/
theorem Brot_lam_one (w₀ w v : ℝ) : Brot w₀ 1 w v = -(Sig w₀ (-w) (π - v)) := by
  simp only [Brot, Sig, sigmaOf, Al_one, Bl_one, Thl_one, rot2_add_pi, cos_pi_sub, sin_pi_sub]
  congr 2
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  simp only; ring

theorem Bline_lam_zero (w₀ w v : ℝ) : Bline w₀ 0 w v = Sig w₀ w v := by
  simp [Bline]

theorem Bline_lam_one (w₀ w v : ℝ) : Bline w₀ 1 w v = -(Sig w₀ (-w) (π - v)) := by
  simp [Bline]

theorem convex_same (c : ℝ) (x : V3) : (1 - c) • x + c • x = x := by
  rw [sub_smul, one_smul, sub_add_cancel]

theorem Bneck_lam_zero (w₀ w v : ℝ) : Bneck w₀ 0 w v = Sig w₀ w v := by
  simp only [Bneck, Bline_lam_zero, Brot_lam_zero, convex_same]

theorem Bneck_lam_one (w₀ w v : ℝ) : Bneck w₀ 1 w v = -(Sig w₀ (-w) (π - v)) := by
  simp only [Bneck, Bline_lam_one, Brot_lam_one, convex_same]

/-! #### (B2)：首の端と外では B = Ŝ -/

include h0 in
theorem chi_of_ge {w : ℝ} (hw : w₀ ^ 2 / 2 ≤ w ^ 2) : chi w₀ w = 0 :=
  cut_of_ge (by positivity) hw

include h0 in
theorem chi_of_le {w : ℝ} (hw : w ^ 2 ≤ w₀ ^ 2 / 4) : chi w₀ w = 1 :=
  cut_of_le (by positivity) hw

theorem chi_nonneg (w₀ w : ℝ) : 0 ≤ chi w₀ w := cut_nonneg _ _

theorem chi_le_one (w₀ w : ℝ) : chi w₀ w ≤ 1 := cut_le_one _ _

include h0 h1 in
/-- 首の端 4w₀/5 < |w| ≤ 1 では、すべての λ で B_line = Σ。 -/
theorem Bline_eq_Sig {w : ℝ} (hw : w₀ * (4 / 5) < |w|) (hw1 : |w| ≤ 1) (l v : ℝ) :
    Bline w₀ l w v = Sig w₀ w v := by
  have h := Shat_E_fixed h0 h1 hw hw1 v
  have hwn : |-w| ≤ 1 := by rwa [abs_neg]
  rw [Shat_neck h0 h1 hw1, Shat_neck h0 h1 hwn] at h
  simp only [Bline]
  rw [h, convex_same]

include h0 h1 in
theorem Bneck_eq_Sig {w : ℝ} (hw : w₀ * (4 / 5) < |w|) (hw1 : |w| ≤ 1) (l v : ℝ) :
    Bneck w₀ l w v = Sig w₀ w v := by
  have hsq : w₀ ^ 2 / 2 ≤ w ^ 2 := by
    rw [← sq_abs w]
    nlinarith [abs_nonneg w]
  simp only [Bneck, chi_of_ge h0 hsq, Bline_eq_Sig h0 h1 hw hw1]
  simp

include h0 h1 in
/-- (B2)：|w| > 4w₀/5 で B = Ŝ（すべての s）。 -/
theorem Bfam_eq_Shat {w : ℝ} (hw : w₀ * (4 / 5) < |w|) (s v : ℝ) :
    Bfam w₀ s w v = Shat w₀ w v := by
  simp only [Bfam]
  split_ifs with hw1
  · rw [Bneck_eq_Sig h0 h1 hw hw1, Shat_neck h0 h1 hw1]
  · rfl

/-! #### (B3)：径の恒等式 -/

include h0 in
theorem Al_sq_add_Bl_sq (l w : ℝ) : Al w₀ l w ^ 2 + Bl w₀ l w ^ 2 = Rad (hh w₀ (w ^ 2)) := by
  rw [← rho_sq h0.ne', ← aa_sq_add']
  simp only [Al, Bl]
  linear_combination (aa (rho w₀ w) ^ 2 + bb (rho w₀ w) ^ 2) * sin_sq_add_cos_sq (mu w₀ l w)

include h0 in
/-- **(B3) 径の恒等式**：nsq B_rot = nsq Σ = Rad(hh(w²))、すべての λ、w、v で。 -/
theorem nsq_Brot (l w v : ℝ) : nsq (Brot w₀ l w v) = Rad (hh w₀ (w ^ 2)) := by
  rw [Brot, nsq_sigmaOf, Al_sq_add_Bl_sq h0]

/-! #### (B4)：首では球の中 -/

/-- 二次形式 nsq の凸性の恒等式。 -/
theorem nsq_convex_comb (t : ℝ) (a b : V3) :
    nsq ((1 - t) • a + t • b) = (1 - t) * nsq a + t * nsq b - t * (1 - t) * nsq (a - b) := by
  simp only [nsq, dot, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  ring

theorem nsq_convex_lt {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {a b : V3} {m : ℝ}
    (ha : nsq a < m) (hb : nsq b < m) : nsq ((1 - t) • a + t • b) < m := by
  rw [nsq_convex_comb]
  have h1 := nsq_nonneg (a - b)
  have h2 : 0 ≤ t * (1 - t) := mul_nonneg ht0 (by linarith)
  have h3 : 0 ≤ t * (1 - t) * nsq (a - b) := mul_nonneg h2 h1
  have hpos : 0 < (1 - t) * (m - nsq a) + t * (m - nsq b) := by
    rcases lt_or_eq_of_le ht1 with hlt | heq
    · have := mul_pos (by linarith : (0 : ℝ) < 1 - t) (by linarith : 0 < m - nsq a)
      have := mul_nonneg ht0 (by linarith : (0 : ℝ) ≤ m - nsq b)
      linarith
    · rw [heq]; linarith
  nlinarith

include h0 in
theorem nsq_Bline_lt {w : ℝ} (hw : |w| ≤ w₀) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (v : ℝ) :
    nsq (Bline w₀ l w v) < w₀ ^ 2 := by
  have h1 := nsq_Sig_neck h0 hw v
  have h2 : nsq (-(Sig w₀ (-w) (π - v))) < w₀ ^ 2 := by
    rw [nsq_neg]; exact nsq_Sig_neck h0 (by rwa [abs_neg]) _
  exact nsq_convex_lt hl0 hl1 h1 h2

include h0 in
/-- **(B4)**：|w| ≤ w₀ で |B_neck| < w₀。 -/
theorem nsq_Bneck_lt {w : ℝ} (hw : |w| ≤ w₀) {l : ℝ} (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (v : ℝ) :
    nsq (Bneck w₀ l w v) < w₀ ^ 2 := by
  have h1 := nsq_Bline_lt h0 hw hl0 hl1 v
  have h2 : nsq (Brot w₀ l w v) < w₀ ^ 2 := by
    rw [nsq_Brot h0, ← nsq_Sig h0.ne' w v]; exact nsq_Sig_neck h0 hw v
  exact nsq_convex_lt (chi_nonneg _ _) (chi_le_one _ _) h1 h2

include h0 in
theorem nsq_Bfam_lt {w : ℝ} (hw : |w| ≤ w₀) (hw1 : w₀ ≤ 1) (s v : ℝ) :
    nsq (Bfam w₀ s w v) < w₀ ^ 2 := by
  simp only [Bfam, hw.trans hw1, ↓reduceIte]
  exact nsq_Bneck_lt h0 hw (lam_nonneg _) (lam_le_one _) v

/-! #### (B5)：中央円の回転 -/

theorem mu_zero_w (w₀ l : ℝ) : mu w₀ l 0 = 0 := by simp [mu, kap_zero']

include h0 in
theorem Thl_zero_w (l : ℝ) : Thl w₀ l 0 = π + l * π := by
  have := psi_of_le h0 (w := 0) (by positivity)
  simp only [Thl, neg_zero, this]; ring

include h0 in
/-- **(B5)**：B_rot(λ, 0, v) = rot2(λπ) Σ(0, v)。 -/
theorem Brot_zero (l v : ℝ) : Brot w₀ l 0 v = rot2 (l * π) (Sig w₀ 0 v) := by
  have hψ : psi w₀ 0 = π := psi_of_le h0 (by positivity)
  simp only [Brot, Sig, sigmaOf, Al, Bl, mu_zero_w, Thl_zero_w h0, cos_zero, sin_zero, mul_one,
    mul_zero, sub_zero, zero_add, hψ, AA_zero, BB_zero]
  rw [add_comm π, rot2_add]

/-! #### (B6)：滑らかさ -/

include h0 in
theorem contDiff_Al : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Al w₀ q.1 q.2.1) := by
  have hρ := contDiff_rho h0.ne'
  have hκ := contDiff_kap w₀
  have haa := contDiff_aa
  have hbb := contDiff_bb
  simp only [Al, mu]
  fun_prop

include h0 in
theorem contDiff_Bl : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Bl w₀ q.1 q.2.1) := by
  have hρ := contDiff_rho h0.ne'
  have hκ := contDiff_kap w₀
  have haa := contDiff_aa
  have hbb := contDiff_bb
  simp only [Bl, mu]
  fun_prop

theorem contDiff_Thl (w₀ : ℝ) : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Thl w₀ q.1 q.2.1) := by
  have hψ := contDiff_psi w₀
  simp only [Thl]
  fun_prop

include h0 in
theorem contDiff_Brot : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Brot w₀ q.1 q.2.1 q.2.2) := by
  have hA := contDiff_Al h0
  have hB := contDiff_Bl h0
  have hΘ := contDiff_Thl w₀
  have hc : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => cos (Thl w₀ q.1 q.2.1)) := Real.contDiff_cos.comp hΘ
  have hs : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => sin (Thl w₀ q.1 q.2.1)) := Real.contDiff_sin.comp hΘ
  have hcv : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => cos q.2.2) := Real.contDiff_cos.comp contDiff_snd.snd
  have hsv : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => sin q.2.2) := Real.contDiff_sin.comp contDiff_snd.snd
  simp only [Brot, sigmaOf, rot2]
  exact ((hA.mul hc).add ((hB.mul hsv).mul hs)).prodMk
    ((hB.mul hcv).prodMk ((hA.mul hs).neg.add ((hB.mul hsv).mul hc)))

include h0 in
theorem contDiff_Bline : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Bline w₀ q.1 q.2.1 q.2.2) := by
  have hS := contDiff_Sig h0.ne'
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Sig w₀ q.2.1 q.2.2) := by
    have e : (fun q : ℝ × ℝ × ℝ => Sig w₀ q.2.1 q.2.2) =
        (fun p : ℝ × ℝ => Sig w₀ p.1 p.2) ∘ (fun q : ℝ × ℝ × ℝ => (q.2.1, q.2.2)) := rfl
    rw [e]
    exact hS.comp (by fun_prop)
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Sig w₀ (-q.2.1) (π - q.2.2)) := by
    have e : (fun q : ℝ × ℝ × ℝ => Sig w₀ (-q.2.1) (π - q.2.2)) =
        (fun p : ℝ × ℝ => Sig w₀ p.1 p.2) ∘ (fun q : ℝ × ℝ × ℝ => (-q.2.1, π - q.2.2)) := rfl
    rw [e]
    exact hS.comp (by fun_prop)
  simp only [Bline]
  fun_prop

theorem contDiff_chi (w₀ : ℝ) : ContDiff ℝ ∞ (chi w₀) :=
  (contDiff_cut _).comp (contDiff_id.pow 2)

include h0 in
theorem contDiff_Bneck : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Bneck w₀ q.1 q.2.1 q.2.2) := by
  have hc : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => chi w₀ q.2.1) := by
    have e : (fun q : ℝ × ℝ × ℝ => chi w₀ q.2.1) = chi w₀ ∘ (fun q : ℝ × ℝ × ℝ => q.2.1) := rfl
    rw [e]
    exact (contDiff_chi w₀).comp (by fun_prop)
  have hL := contDiff_Bline h0
  have hR := contDiff_Brot h0
  simp only [Bneck]
  fun_prop

include h0 in
theorem continuous_Bneck : Continuous (fun q : ℝ × ℝ × ℝ => Bneck w₀ q.1 q.2.1 q.2.2) :=
  (contDiff_Bneck h0).continuous

include h0 h1 in
/-- **(B6)**：B は (s, w, v) について滑らか。 -/
theorem contDiff_Bfam : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Bfam w₀ q.1 q.2.1 q.2.2) := by
  refine contDiff_iff_contDiffAt.mpr fun q => ?_
  by_cases hq : |q.2.1| < 1
  · have hopen : IsOpen {p : ℝ × ℝ × ℝ | |p.2.1| < 1} :=
      isOpen_lt (continuous_abs.comp continuous_snd.fst) continuous_const
    have he : (fun p : ℝ × ℝ × ℝ => Bfam w₀ p.1 p.2.1 p.2.2) =ᶠ[𝓝 q]
        fun p => Bneck w₀ (lam p.1) p.2.1 p.2.2 := by
      filter_upwards [hopen.mem_nhds hq] with p hp
      simp [Bfam, le_of_lt hp]
    refine ContDiffAt.congr_of_eventuallyEq ?_ he
    exact (contDiff_Bneck h0).contDiffAt.comp q
      ((contDiff_lam.comp contDiff_fst).prodMk (contDiff_snd.fst.prodMk contDiff_snd.snd)).contDiffAt
  · push Not at hq
    have hgt : w₀ * (4 / 5) < |q.2.1| := by nlinarith
    have hopen : IsOpen {p : ℝ × ℝ × ℝ | w₀ * (4 / 5) < |p.2.1|} :=
      isOpen_lt continuous_const (continuous_abs.comp continuous_snd.fst)
    have he : (fun p : ℝ × ℝ × ℝ => Bfam w₀ p.1 p.2.1 p.2.2) =ᶠ[𝓝 q]
        fun p => Shat w₀ p.2.1 p.2.2 := by
      filter_upwards [hopen.mem_nhds hgt] with p hp
      exact Bfam_eq_Shat h0 h1 hp p.1 p.2.2
    refine ContDiffAt.congr_of_eventuallyEq ?_ he
    exact (contDiff_Shat h0 h1).contDiffAt.comp q (contDiff_snd.fst.prodMk contDiff_snd.snd).contDiffAt

/-! #### (B7)：深い首では回転形 -/

include h0 in
theorem Bneck_of_deep {w : ℝ} (hw : |w| ≤ w₀ / 4) (l v : ℝ) : Bneck w₀ l w v = Brot w₀ l w v := by
  have hsq : w ^ 2 ≤ w₀ ^ 2 / 4 := by
    rw [← sq_abs w]
    nlinarith [abs_nonneg w]
  simp [Bneck, chi_of_le h0 hsq]

/-! #### (B8)：λ = ½、w = 0 では ∂w B_rot = 0（はめ込みではない） -/

theorem mu_half (w₀ w : ℝ) : mu w₀ (1 / 2) w = 0 := by simp [mu]

theorem Al_half (w₀ w : ℝ) : Al w₀ (1 / 2) w = aa (rho w₀ w) := by rw [Al, mu_half]; simp

theorem Bl_half (w₀ w : ℝ) : Bl w₀ (1 / 2) w = bb (rho w₀ w) := by rw [Bl, mu_half]; simp

include h0 in
theorem Thl_half_of_deep {w : ℝ} (hw : |w| ≤ w₀ / 4) : Thl w₀ (1 / 2) w = 3 * π / 2 := by
  have := abs_le.mp hw
  rw [Thl, psi_of_le h0 (by linarith), psi_of_le h0 (by linarith)]
  ring

include h0 in
/-- **(B8)**：λ = ½ で w = 0 の w 方向の偏微分は 0。基底ははめ込みではなくてよい。 -/
theorem Brot_half_deriv_zero (v : ℝ) : HasDerivAt (fun w => Brot w₀ (1 / 2) w v) 0 0 := by
  have hA : HasDerivAt (Al w₀ (1 / 2)) 0 0 := by
    have e : Al w₀ (1 / 2) = fun w => aa (rho w₀ w) := funext (Al_half w₀)
    rw [e]
    have h := (hasDerivAt_aa (rho w₀ 0)).comp 0 (hasDerivAt_rho h0.ne' 0)
    have e2 : da (rho w₀ 0) * (dh w₀ (0 ^ 2) * 0 / rho w₀ 0) = 0 := by ring
    rw [e2] at h
    exact h
  have hB : HasDerivAt (Bl w₀ (1 / 2)) 0 0 := by
    have e : Bl w₀ (1 / 2) = fun w => bb (rho w₀ w) := funext (Bl_half w₀)
    rw [e]
    have h := (hasDerivAt_bb (rho w₀ 0)).comp 0 (hasDerivAt_rho h0.ne' 0)
    have e2 : db (rho w₀ 0) * (dh w₀ (0 ^ 2) * 0 / rho w₀ 0) = 0 := by ring
    rw [e2] at h
    exact h
  have hψ : HasDerivAt (Thl w₀ (1 / 2)) 0 0 := by
    have hopen : IsOpen {w : ℝ | |w| < w₀ / 4} := isOpen_lt continuous_abs continuous_const
    have e : Thl w₀ (1 / 2) =ᶠ[𝓝 0] fun _ => 3 * π / 2 := by
      filter_upwards [hopen.mem_nhds (by simp; positivity)] with w hw
      exact Thl_half_of_deep h0 (le_of_lt hw)
    exact (hasDerivAt_const (0 : ℝ) (3 * π / 2)).congr_of_eventuallyEq e
  have h := hasDerivAt_sigma_w hA hB hψ v
  refine h.congr_deriv ?_
  simp only [sigW, rot2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

/-! ### 窓とスケジュール -/

/-- 窓の始まり t₁ = t∗(1 − w₀/4)。 -/
def t1 (R : Race) (w₀ : ℝ) : ℝ := R.tstar * (1 - w₀ / 4)

/-- 窓の終わり t₂ = t∗(1 + w₀/4)。 -/
def t2 (R : Race) (w₀ : ℝ) : ℝ := R.tstar * (1 + w₀ / 4)

/-- 時刻の対応 sched(t) = (t − t₁)/(t₂ − t₁)。 -/
def sched (R : Race) (w₀ t : ℝ) : ℝ := (t - t1 R w₀) / (t2 R w₀ - t1 R w₀)

variable (R : Race)

theorem t2_sub_t1 : t2 R w₀ - t1 R w₀ = R.tstar * w₀ / 2 := by
  simp only [t1, t2]; ring

include h0 in
theorem t2_sub_t1_pos : 0 < t2 R w₀ - t1 R w₀ := by
  rw [t2_sub_t1]; have := R.tstar_pos; positivity

include h0 in
theorem sched_tstar : sched R w₀ R.tstar = 1 / 2 := by
  have hpos := t2_sub_t1_pos h0 R
  rw [sched, div_eq_iff hpos.ne', t2_sub_t1]
  simp only [t1]
  ring

include h0 in
theorem sched_le_zero {t : ℝ} (ht : t ≤ t1 R w₀) : sched R w₀ t ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (by linarith) (t2_sub_t1_pos h0 R).le

include h0 in
theorem sched_ge_one {t : ℝ} (ht : t2 R w₀ ≤ t) : 1 ≤ sched R w₀ t := by
  rw [sched, le_div_iff₀ (t2_sub_t1_pos h0 R)]; linarith

include h0 in
theorem lam_sched_of_le {t : ℝ} (ht : t ≤ t1 R w₀) : lam (sched R w₀ t) = 0 :=
  lam_of_le (by linarith [sched_le_zero h0 R ht])

include h0 in
theorem lam_sched_of_ge {t : ℝ} (ht : t2 R w₀ ≤ t) : lam (sched R w₀ t) = 1 :=
  lam_of_ge (by linarith [sched_ge_one h0 R ht])

include h0 in
theorem sched_pos {t : ℝ} (ht : t1 R w₀ < t) : 0 < sched R w₀ t :=
  div_pos (by linarith) (t2_sub_t1_pos h0 R)

include h0 in
theorem sched_lt_one {t : ℝ} (ht : t < t2 R w₀) : sched R w₀ t < 1 := by
  rw [sched, div_lt_one (t2_sub_t1_pos h0 R)]; linarith

/-- 窓の中では走者は深い首 |w| ≤ w₀/4 にいる。 -/
theorem abs_g_le_of_window {t : ℝ} (ht1 : t1 R w₀ ≤ t) (ht2 : t ≤ t2 R w₀) : |R.g t| ≤ w₀ / 4 := by
  have hts := R.tstar_pos
  rw [R.g_eq, abs_le]
  simp only [t1, t2] at ht1 ht2
  have e1 : (1 - w₀ / 4) ≤ t / R.tstar := by rw [le_div_iff₀ hts]; linarith
  have e2 : t / R.tstar ≤ 1 + w₀ / 4 := by rw [div_le_iff₀ hts]; linarith
  constructor <;> linarith

theorem t1_pos (R : Race) {w₀ : ℝ} (h1 : w₀ < 1) : 0 < t1 R w₀ := by
  have := R.tstar_pos
  simp only [t1]; nlinarith

theorem t2_lt (R : Race) {w₀ : ℝ} (h1 : w₀ < 1) : t2 R w₀ < 2 * R.tstar := by
  have := R.tstar_pos
  simp only [t2]; nlinarith

theorem t1_lt_tstar (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) : t1 R w₀ < R.tstar := by
  have := R.tstar_pos
  simp only [t1]; nlinarith

theorem tstar_lt_t2 (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) : R.tstar < t2 R w₀ := by
  have := R.tstar_pos
  simp only [t2]; nlinarith

/-! ### 基底の上の走者 -/

/-- 基底の上の亀。 -/
def baseT (R : Race) (w₀ c : ℝ) (t : ℝ) : V3 :=
  Bfam w₀ (sched R w₀ t) (R.r * R.g t) (VtR c (R.r * R.g t))

/-- 基底の上のアキレス。 -/
def baseA (R : Race) (w₀ c : ℝ) (n₁ : ℕ) (t : ℝ) : V3 :=
  Bfam w₀ (sched R w₀ t) (R.g t) (VaR R.r w₀ c n₁ (R.g t))

include h0 in
/-- **径の恒等式**：競走の時間で |w| ≤ |g(t)| なら nsq B(sched t, w, v) = nsq Σ(w, 0)。
窓の外では λ ∈ {0, 1}、窓の中では走者は深い首にいて B = B_rot である。 -/
theorem nsq_Bfam_run {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) {w : ℝ} (hw : |w| ≤ |R.g t|) (v : ℝ) :
    nsq (Bfam w₀ (sched R w₀ t) w v) = nsq (Sig w₀ w 0) := by
  have hw1 : |w| ≤ 1 := hw.trans (R.abs_g_le ht.1 ht.2)
  simp only [Bfam, hw1, ↓reduceIte]
  rw [nsq_Sig h0.ne']
  by_cases hA : t ≤ t1 R w₀
  · rw [lam_sched_of_le h0 R hA, Bneck_lam_zero, nsq_Sig h0.ne']
  · by_cases hB : t2 R w₀ ≤ t
    · rw [lam_sched_of_ge h0 R hB, Bneck_lam_one, nsq_neg, nsq_Sig h0.ne', neg_sq]
    · push Not at hA hB
      have hdeep : |w| ≤ w₀ / 4 := hw.trans (abs_g_le_of_window R hA.le hB.le)
      rw [Bneck_of_deep h0 hdeep, nsq_Brot h0]

include h0 in
theorem nsq_baseT {c : ℝ} {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    nsq (baseT R w₀ c t) = nsq (Sig w₀ (R.r * R.g t) 0) :=
  nsq_Bfam_run h0 R ht (R.abs_r_g_le t) _

include h0 in
theorem nsq_baseA {c : ℝ} {n₁ : ℕ} {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    nsq (baseA R w₀ c n₁ t) = nsq (Sig w₀ (R.g t) 0) :=
  nsq_Bfam_run h0 R ht le_rfl _

include h0 h1 in
/-- 基底の上の同時刻の非衝突（t ≠ t∗）：亀はつねに ℘ に近い。 -/
theorem base_nearer {c : ℝ} {n₁ : ℕ} {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) (hne : t ≠ R.tstar) :
    nsq (baseT R w₀ c t) < nsq (baseA R w₀ c n₁ t) := by
  rw [nsq_baseT h0 R ht, nsq_baseA h0 R ht]
  exact nsq_Sig_lt h0.ne' (by nlinarith) (R.abs_r_g_lt hne) (R.abs_g_le ht.1 ht.2) _ _

include h0 h1 in
theorem base_follow_before' {c : ℝ} {n₁ : ℕ} {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ R.tstar) :
    nsq (baseT R w₀ c t) < nsq (baseA R w₀ c n₁ s) := by
  have hts := R.tstar_pos
  rw [nsq_baseT h0 R ⟨by linarith, by linarith⟩, nsq_baseA h0 R ⟨hs, by linarith⟩]
  exact nsq_Sig_lt h0.ne' (by nlinarith) ((R.abs_r_g_le t).trans_lt (R.abs_g_lt_before hst ht))
    (R.abs_g_le hs (by linarith)) _ _

include h0 h1 in
theorem base_follow_after' {c : ℝ} {n₁ : ℕ} {s t : ℝ} (hs : R.tstar ≤ s) (hst : s < t)
    (ht : t ≤ 2 * R.tstar) : nsq (baseT R w₀ c s) < nsq (baseA R w₀ c n₁ t) := by
  have hts := R.tstar_pos
  rw [nsq_baseT h0 R ⟨by linarith, by linarith⟩, nsq_baseA h0 R ⟨by linarith, ht⟩]
  exact nsq_Sig_lt h0.ne' (by nlinarith) ((R.abs_r_g_le s).trans_lt (R.abs_g_lt_after hs hst))
    (R.abs_g_le (by linarith) ht) _ _

include h0 in
/-- **t∗ での基底の位置**：baseT = (bb₀, 0, aa₀)、baseA = (−bb₀, 0, aa₀)。 -/
theorem base_tstar {c : ℝ} (hc : 0 < c) (n₁ : ℕ) :
    baseT R w₀ c R.tstar = (BB w₀ 0, 0, AA w₀ 0) ∧
      baseA R w₀ c n₁ R.tstar = (-(BB w₀ 0), 0, AA w₀ 0) := by
  have hg := R.g_tstar
  have hdeep : |(0 : ℝ)| ≤ w₀ / 4 := by simp; positivity
  have hpi : (1 / 2 : ℝ) * π = π / 2 := by ring
  constructor
  · simp only [baseT, hg, mul_zero, VtR_zero hc, Bfam, abs_zero, zero_le_one, ↓reduceIte,
      sched_tstar h0, lam_half, Bneck_of_deep h0 hdeep, Brot_zero h0, Sig_zero h0, hpi, rot2,
      cos_pi_div_two, sin_pi_div_two, cos_neg, sin_neg]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp
  · simp only [baseA, hg, VaR_zero hc, Bfam, abs_zero, zero_le_one, ↓reduceIte,
      sched_tstar h0, lam_half, Bneck_of_deep h0 hdeep, Brot_zero h0, Sig_zero h0, hpi, rot2,
      cos_pi_div_two, sin_pi_div_two, cos_add_nat_mul_two_pi, sin_add_nat_mul_two_pi]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

include h0 h1 in
/-- **回転の対応**：t∗ で基底の位置は静的な位置を rot2(π/2) で回したものである。 -/
theorem base_rotation {c : ℝ} (hc : w₀ ≤ c) (n₁ : ℕ) :
    baseT R w₀ c R.tstar = rot2 (π / 2) (R.runT (Shat w₀) (VtR c) R.tstar) ∧
      baseA R w₀ c n₁ R.tstar = rot2 (π / 2) (R.runA (Shat w₀) (VaR R.r w₀ c n₁) R.tstar) := by
  have hcp : 0 < c := by linarith
  obtain ⟨eT, eA⟩ := base_tstar h0 R hcp n₁
  rw [eT, eA, runT_Shat_eq R h0 h1 _ R.tstar_mem, runA_Shat_eq R h0 h1 _ R.tstar_mem,
    reg_Ts R h0 hc, reg_As R h0 hc n₁]
  simp only [rot2, cos_pi_div_two, sin_pi_div_two]
  constructor <;> refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp

include h0 h1 in
theorem base_ne_tstar {c : ℝ} (hc : 0 < c) (n₁ : ℕ) :
    baseT R w₀ c R.tstar ≠ baseA R w₀ c n₁ R.tstar := by
  obtain ⟨eT, eA⟩ := base_tstar h0 R hc n₁
  rw [eT, eA]
  intro h
  have := congrArg Prod.fst h
  simp only at this
  have := BB_pos h0 h1 0
  linarith

include h0 h1 in
theorem base_no_collision {c : ℝ} (hc : 0 < c) (n₁ : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    baseT R w₀ c t ≠ baseA R w₀ c n₁ t := by
  by_cases hts : t = R.tstar
  · rw [hts]; exact base_ne_tstar h0 h1 R hc n₁
  · intro h
    have := base_nearer h0 h1 R (c := c) (n₁ := n₁) ht hts
    rw [h] at this
    exact lt_irrefl _ this

/-! ### 連続性と最小距離 -/

theorem baseT_eq_on {c : ℝ} {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    baseT R w₀ c t = Bneck w₀ (lam (sched R w₀ t)) (R.r * R.g t) (VtR c (R.r * R.g t)) := by
  simp only [baseT, Bfam, R.abs_r_g_le_one ht, ↓reduceIte]

theorem baseA_eq_on {c : ℝ} {n₁ : ℕ} {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    baseA R w₀ c n₁ t = Bneck w₀ (lam (sched R w₀ t)) (R.g t) (VaR R.r w₀ c n₁ (R.g t)) := by
  simp only [baseA, Bfam, R.abs_g_le ht.1 ht.2, ↓reduceIte]

theorem continuous_sched (R : Race) (w₀ : ℝ) : Continuous (sched R w₀) := by
  unfold sched; fun_prop

include h0 in
theorem continuousOn_baseT (c : ℝ) : ContinuousOn (baseT R w₀ c) (Icc 0 (2 * R.tstar)) := by
  have hc : Continuous fun t => Bneck w₀ (lam (sched R w₀ t)) (R.r * R.g t) (VtR c (R.r * R.g t)) := by
    have hrg : Continuous fun t => R.r * R.g t := continuous_const.mul R.continuous_g
    have hV : Continuous fun t => VtR c (R.r * R.g t) := (contDiff_VtR c).continuous.comp hrg
    have hl : Continuous fun t => lam (sched R w₀ t) :=
      contDiff_lam.continuous.comp (continuous_sched R w₀)
    have e : (fun t => Bneck w₀ (lam (sched R w₀ t)) (R.r * R.g t) (VtR c (R.r * R.g t))) =
        (fun q : ℝ × ℝ × ℝ => Bneck w₀ q.1 q.2.1 q.2.2) ∘
          (fun t => ((lam (sched R w₀ t), (R.r * R.g t, VtR c (R.r * R.g t))) : ℝ × ℝ × ℝ)) := rfl
    rw [e]
    exact (continuous_Bneck h0).comp (hl.prodMk (hrg.prodMk hV))
  exact hc.continuousOn.congr fun t ht => baseT_eq_on R ht

include h0 in
theorem continuousOn_baseA (c : ℝ) (n₁ : ℕ) :
    ContinuousOn (baseA R w₀ c n₁) (Icc 0 (2 * R.tstar)) := by
  have hc : Continuous fun t => Bneck w₀ (lam (sched R w₀ t)) (R.g t) (VaR R.r w₀ c n₁ (R.g t)) := by
    have hg := R.continuous_g
    have hV : Continuous fun t => VaR R.r w₀ c n₁ (R.g t) :=
      (contDiff_VaR R.r h0.ne' c n₁).continuous.comp hg
    have hl : Continuous fun t => lam (sched R w₀ t) :=
      contDiff_lam.continuous.comp (continuous_sched R w₀)
    have e : (fun t => Bneck w₀ (lam (sched R w₀ t)) (R.g t) (VaR R.r w₀ c n₁ (R.g t))) =
        (fun q : ℝ × ℝ × ℝ => Bneck w₀ q.1 q.2.1 q.2.2) ∘
          (fun t => ((lam (sched R w₀ t), (R.g t, VaR R.r w₀ c n₁ (R.g t))) : ℝ × ℝ × ℝ)) := rfl
    rw [e]
    exact (continuous_Bneck h0).comp (hl.prodMk (hg.prodMk hV))
  exact hc.continuousOn.congr fun t ht => baseA_eq_on R ht

theorem continuous_nsq : Continuous nsq := by
  unfold nsq; exact continuous_dot.comp (continuous_id.prodMk continuous_id)

include h0 h1 in
/-- 同時刻の最小距離 m₁ > 0。 -/
theorem base_min {c : ℝ} (hc : 0 < c) (n₁ : ℕ) :
    ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), d ≤ nsq (baseT R w₀ c t - baseA R w₀ c n₁ t) := by
  have hcont : ContinuousOn (fun t => nsq (baseT R w₀ c t - baseA R w₀ c n₁ t)) (Icc 0 (2 * R.tstar)) := by
    have e : (fun t => nsq (baseT R w₀ c t - baseA R w₀ c n₁ t)) =
        nsq ∘ (fun t => baseT R w₀ c t - baseA R w₀ c n₁ t) := rfl
    rw [e]
    exact continuous_nsq.comp_continuousOn ((continuousOn_baseT h0 R c).sub (continuousOn_baseA h0 R c n₁))
  have hne' : (Icc 0 (2 * R.tstar)).Nonempty := ⟨0, le_rfl, by have := R.tstar_pos; positivity⟩
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne' hcont
  exact ⟨_, nsq_pos_of_ne (sub_ne_zero.mpr (base_no_collision h0 h1 R hc n₁ ht₀)),
    fun t ht => isMinOn_iff.mp hmin t ht⟩

/-- 三角形 {(s, t) : a ≤ s ≤ t ≤ b} はコンパクトである。 -/
theorem isCompact_triangle (a b : ℝ) :
    IsCompact {p : ℝ × ℝ | a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b} := by
  refine ((isCompact_Icc (a := a) (b := b)).prod (isCompact_Icc (a := a) (b := b))).of_isClosed_subset
    ?_ ?_
  · exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_snd).inter (isClosed_le continuous_snd continuous_const))
  · rintro ⟨s, t⟩ ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2.trans h3⟩, ⟨h1.trans h2, h3⟩⟩

include h0 h1 in
/-- 追従の最小距離 m_b > 0（t∗ まで）：亀の位置はアキレスの過去の位置から離れている。 -/
theorem base_follow_min_before {c : ℝ} (hc : 0 < c) (n₁ : ℕ) :
    ∃ d > 0, ∀ s t, 0 ≤ s → s ≤ t → t ≤ R.tstar → d ≤ nsq (baseT R w₀ c t - baseA R w₀ c n₁ s) := by
  have hts := R.tstar_pos
  have hK : IsCompact {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R.tstar} :=
    isCompact_triangle 0 R.tstar
  have hmapT : MapsTo (fun p : ℝ × ℝ => p.2) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R.tstar}
      (Icc 0 (2 * R.tstar)) :=
    fun p hp => ⟨hp.1.trans hp.2.1, by linarith [hp.2.2]⟩
  have hmapA : MapsTo (fun p : ℝ × ℝ => p.1) {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R.tstar}
      (Icc 0 (2 * R.tstar)) :=
    fun p hp => ⟨hp.1, by linarith [hp.2.1, hp.2.2]⟩
  have hT : ContinuousOn (fun p : ℝ × ℝ => baseT R w₀ c p.2)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R.tstar} := by
    have e : (fun p : ℝ × ℝ => baseT R w₀ c p.2) = baseT R w₀ c ∘ Prod.snd := rfl
    rw [e]; exact (continuousOn_baseT h0 R c).comp continuous_snd.continuousOn hmapT
  have hA : ContinuousOn (fun p : ℝ × ℝ => baseA R w₀ c n₁ p.1)
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R.tstar} := by
    have e : (fun p : ℝ × ℝ => baseA R w₀ c n₁ p.1) = baseA R w₀ c n₁ ∘ Prod.fst := rfl
    rw [e]; exact (continuousOn_baseA h0 R c n₁).comp continuous_fst.continuousOn hmapA
  have hcont : ContinuousOn (fun p : ℝ × ℝ => nsq (baseT R w₀ c p.2 - baseA R w₀ c n₁ p.1))
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R.tstar} := by
    have e : (fun p : ℝ × ℝ => nsq (baseT R w₀ c p.2 - baseA R w₀ c n₁ p.1)) =
        nsq ∘ (fun p : ℝ × ℝ => baseT R w₀ c p.2 - baseA R w₀ c n₁ p.1) := rfl
    rw [e]; exact continuous_nsq.comp_continuousOn (hT.sub hA)
  have hne' : ({p : ℝ × ℝ | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ R.tstar} : Set (ℝ × ℝ)).Nonempty :=
    ⟨(0, 0), le_rfl, le_rfl, hts.le⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne' hcont
  refine ⟨nsq (baseT R w₀ c p₀.2 - baseA R w₀ c n₁ p₀.1), ?_, fun s t hs hst ht => ?_⟩
  · apply nsq_pos_of_ne
    apply sub_ne_zero.mpr
    obtain ⟨hp1, hp2, hp3⟩ := hp₀
    rcases lt_or_eq_of_le hp2 with hlt | heq
    · intro h
      have := base_follow_before' h0 h1 R (c := c) (n₁ := n₁) hp1 hlt hp3
      rw [h] at this
      exact lt_irrefl _ this
    · rw [← heq]
      exact base_no_collision h0 h1 R hc n₁ ⟨hp1, by linarith⟩
  · have := isMinOn_iff.mp hmin (s, t) ⟨hs, hst, ht⟩
    exact this

include h0 h1 in
/-- 追従の最小距離 m_a > 0（t∗ 以後）。 -/
theorem base_follow_min_after {c : ℝ} (hc : 0 < c) (n₁ : ℕ) :
    ∃ d > 0, ∀ s t, R.tstar ≤ s → s ≤ t → t ≤ 2 * R.tstar →
      d ≤ nsq (baseA R w₀ c n₁ t - baseT R w₀ c s) := by
  have hts := R.tstar_pos
  have hK : IsCompact {p : ℝ × ℝ | R.tstar ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 2 * R.tstar} :=
    isCompact_triangle R.tstar (2 * R.tstar)
  have hmapT : MapsTo (fun p : ℝ × ℝ => p.1)
      {p : ℝ × ℝ | R.tstar ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 2 * R.tstar} (Icc 0 (2 * R.tstar)) :=
    fun p hp => ⟨by linarith [hp.1], by linarith [hp.2.1, hp.2.2]⟩
  have hmapA : MapsTo (fun p : ℝ × ℝ => p.2)
      {p : ℝ × ℝ | R.tstar ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 2 * R.tstar} (Icc 0 (2 * R.tstar)) :=
    fun p hp => ⟨by linarith [hp.1, hp.2.1], hp.2.2⟩
  have hT : ContinuousOn (fun p : ℝ × ℝ => baseT R w₀ c p.1)
      {p : ℝ × ℝ | R.tstar ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 2 * R.tstar} := by
    have e : (fun p : ℝ × ℝ => baseT R w₀ c p.1) = baseT R w₀ c ∘ Prod.fst := rfl
    rw [e]; exact (continuousOn_baseT h0 R c).comp continuous_fst.continuousOn hmapT
  have hA : ContinuousOn (fun p : ℝ × ℝ => baseA R w₀ c n₁ p.2)
      {p : ℝ × ℝ | R.tstar ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 2 * R.tstar} := by
    have e : (fun p : ℝ × ℝ => baseA R w₀ c n₁ p.2) = baseA R w₀ c n₁ ∘ Prod.snd := rfl
    rw [e]; exact (continuousOn_baseA h0 R c n₁).comp continuous_snd.continuousOn hmapA
  have hcont : ContinuousOn (fun p : ℝ × ℝ => nsq (baseA R w₀ c n₁ p.2 - baseT R w₀ c p.1))
      {p : ℝ × ℝ | R.tstar ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 2 * R.tstar} := by
    have e : (fun p : ℝ × ℝ => nsq (baseA R w₀ c n₁ p.2 - baseT R w₀ c p.1)) =
        nsq ∘ (fun p : ℝ × ℝ => baseA R w₀ c n₁ p.2 - baseT R w₀ c p.1) := rfl
    rw [e]; exact continuous_nsq.comp_continuousOn (hA.sub hT)
  have hne' : ({p : ℝ × ℝ | R.tstar ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 2 * R.tstar} : Set (ℝ × ℝ)).Nonempty :=
    ⟨(R.tstar, R.tstar), le_rfl, le_rfl, by linarith⟩
  obtain ⟨p₀, hp₀, hmin⟩ := hK.exists_isMinOn hne' hcont
  refine ⟨nsq (baseA R w₀ c n₁ p₀.2 - baseT R w₀ c p₀.1), ?_, fun s t hs hst ht => ?_⟩
  · apply nsq_pos_of_ne
    apply sub_ne_zero.mpr
    obtain ⟨hp1, hp2, hp3⟩ := hp₀
    rcases lt_or_eq_of_le hp2 with hlt | heq
    · intro h
      have := base_follow_after' h0 h1 R (c := c) (n₁ := n₁) hp1 hlt hp3
      rw [h] at this
      exact lt_irrefl _ this
    · rw [← heq]
      exact (base_no_collision h0 h1 R hc n₁ ⟨by linarith, by linarith⟩).symm
  · have := isMinOn_iff.mp hmin (s, t) ⟨hs, hst, ht⟩
    exact this

end Base

end Zeno.Model
