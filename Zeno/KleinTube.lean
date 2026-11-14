/-
# Zeno.KleinTube : 外側の管 Tube（回転面）

Tube(w, v) = (R cos θ, R sin θ cos v, R sin θ sin v)、θ = θ(w)、R = R(θ(w))。
q₁ 軸のまわりの回転面で、子午線は極座標のグラフ r = R(θ) である。
w ∈ [1, wₐ] で Tube = G、w ∈ [4 − wₐ, 3] で Tube(w, v) = G(w − 4, v + π)。
一致は区間の上の関数の一致なので、全階の微分も一致する。

1 ≤ w ≤ 3 で管ははめ込みであり、その半径は首の最大半径 |G(w₀, 0)| より大きい。
-/
import Zeno.KleinProfile
import Zeno.Tube

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

/-- 管の断面の第 1 成分 A(w) = R(θ(w)) cos θ(w)。 -/
def tubeA (w₀ w : ℝ) : ℝ := RP w₀ (thT w₀ w) * cos (thT w₀ w)

/-- 管の断面の第 2 成分 B(w) = R(θ(w)) sin θ(w) > 0。 -/
def tubeB (w₀ w : ℝ) : ℝ := RP w₀ (thT w₀ w) * sin (thT w₀ w)

/-- 管。 -/
def Tube (w₀ w v : ℝ) : V3 := sigmaOf (tubeA w₀) (tubeB w₀) (fun _ => 0) w v

/-- 管の法線場 ∂ᵥ × ∂w。 -/
def XTube (w₀ w v : ℝ) : V3 :=
  cross (sigV 0 (tubeB w₀ w) v)
    (sigW 0 (tubeA w₀ w) (tubeB w₀ w) (deriv (tubeA w₀) w) (deriv (tubeB w₀) w) 0 v)

section Tube

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
theorem thT_abs_le {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) : |thT w₀ w - π / 2| ≤ π / 4 := by
  obtain ⟨ha, hb⟩ := thT_mem h0 h1 hw1 hw3
  rw [abs_le]; constructor <;> linarith

include h0 h1 in
theorem sin_thT_pos {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) : 0 < sin (thT w₀ w) := by
  obtain ⟨ha, hb⟩ := thT_mem h0 h1 hw1 hw3
  exact sin_pos_of_pos_of_lt_pi (by linarith [pi_pos]) (by linarith [pi_pos])

include h0 h1 in
theorem RP_thT_pos {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) : 0 < RP w₀ (thT w₀ w) :=
  RP_pos h0 h1 (thT_abs_le h0 h1 hw1 hw3)

include h0 h1 in
theorem tubeB_pos {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) : 0 < tubeB w₀ w :=
  mul_pos (RP_thT_pos h0 h1 hw1 hw3) (sin_thT_pos h0 h1 hw1 hw3)

include h0 h1 in
theorem contDiffAt_RP_thT {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) :
    ContDiffAt ℝ ∞ (fun w => RP w₀ (thT w₀ w)) w :=
  (contDiffAt_RP h0 h1 (thT_abs_le h0 h1 hw1 hw3)).comp w (contDiff_thT w₀).contDiffAt

include h0 h1 in
theorem contDiffAt_tubeA {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) : ContDiffAt ℝ ∞ (tubeA w₀) w :=
  (contDiffAt_RP_thT h0 h1 hw1 hw3).mul
    (Real.contDiff_cos.contDiffAt.comp w (contDiff_thT w₀).contDiffAt)

include h0 h1 in
theorem contDiffAt_tubeB {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) : ContDiffAt ℝ ∞ (tubeB w₀) w :=
  (contDiffAt_RP_thT h0 h1 hw1 hw3).mul
    (Real.contDiff_sin.contDiffAt.comp w (contDiff_thT w₀).contDiffAt)

include h0 h1 in
theorem contDiffOn_tubeA : ContDiffOn ℝ ∞ (tubeA w₀) (Ioo 1 3) :=
  fun _ hw => (contDiffAt_tubeA h0 h1 hw.1.le hw.2.le).contDiffWithinAt

include h0 h1 in
theorem contDiffOn_tubeB : ContDiffOn ℝ ∞ (tubeB w₀) (Ioo 1 3) :=
  fun _ hw => (contDiffAt_tubeB h0 h1 hw.1.le hw.2.le).contDiffWithinAt

include h0 h1 in
theorem hasDerivAt_tubeA {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) :
    HasDerivAt (tubeA w₀)
      (deriv (fun w => RP w₀ (thT w₀ w)) w * cos (thT w₀ w) -
        RP w₀ (thT w₀ w) * sin (thT w₀ w) * deriv (thT w₀) w) w := by
  have hR : HasDerivAt (fun w => RP w₀ (thT w₀ w)) (deriv (fun w => RP w₀ (thT w₀ w)) w) w :=
    ((contDiffAt_RP_thT h0 h1 hw1 hw3).differentiableAt (by simp)).hasDerivAt
  have hθ : HasDerivAt (thT w₀) (deriv (thT w₀) w) w :=
    ((contDiff_thT w₀).differentiable (by simp) w).hasDerivAt
  have h := hR.mul hθ.cos
  refine h.congr_deriv ?_
  ring

include h0 h1 in
theorem hasDerivAt_tubeB {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) :
    HasDerivAt (tubeB w₀)
      (deriv (fun w => RP w₀ (thT w₀ w)) w * sin (thT w₀ w) +
        RP w₀ (thT w₀ w) * cos (thT w₀ w) * deriv (thT w₀) w) w := by
  have hR : HasDerivAt (fun w => RP w₀ (thT w₀ w)) (deriv (fun w => RP w₀ (thT w₀ w)) w) w :=
    ((contDiffAt_RP_thT h0 h1 hw1 hw3).differentiableAt (by simp)).hasDerivAt
  have hθ : HasDerivAt (thT w₀) (deriv (thT w₀) w) w :=
    ((contDiff_thT w₀).differentiable (by simp) w).hasDerivAt
  have h := hR.mul hθ.sin
  refine h.congr_deriv ?_
  ring

include h0 h1 in
/-- 管の断面曲線は正則である：(A′, B′) ≠ 0。 -/
theorem tube_profile_ne' {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) :
    ¬ (deriv (tubeA w₀) w = 0 ∧ deriv (tubeB w₀) w = 0) := by
  rintro ⟨hA, hB⟩
  rw [(hasDerivAt_tubeA h0 h1 hw1 hw3).deriv] at hA
  rw [(hasDerivAt_tubeB h0 h1 hw1 hw3).deriv] at hB
  have hR := RP_thT_pos h0 h1 hw1 hw3
  have hd := deriv_thT_pos h0 h1 (by linarith : (0 : ℝ) < w) (by linarith : w < 4)
  have key : RP w₀ (thT w₀ w) * deriv (thT w₀) w = 0 := by
    have := sin_sq_add_cos_sq (thT w₀ w)
    linear_combination (-(sin (thT w₀ w))) * hA + (cos (thT w₀ w)) * hB -
      RP w₀ (thT w₀ w) * deriv (thT w₀) w * this
  exact (mul_pos hR hd).ne' key

include h0 h1 in
theorem XTube_ne {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) (v : ℝ) : XTube w₀ w v ≠ wp :=
  neck_lemma (tubeB_pos h0 h1 hw1 hw3).ne' (tube_profile_ne' h0 h1 hw1 hw3)
    (fun hd => absurd rfl hd) v

theorem Tube_periodic (w₀ w v : ℝ) : Tube w₀ w (v + 2 * π) = Tube w₀ w v := by
  simp [Tube, sigmaOf]

theorem hasDerivAt_Tube_v (w₀ w v : ℝ) :
    HasDerivAt (fun v => Tube w₀ w v) (sigV 0 (tubeB w₀ w) v) v :=
  hasDerivAt_sigma_v (tubeA w₀) (tubeB w₀) (fun _ => 0) w v

include h0 h1 in
theorem hasDerivAt_Tube_w {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    HasDerivAt (fun w => Tube w₀ w v)
      (sigW 0 (tubeA w₀ w) (tubeB w₀ w) (deriv (tubeA w₀) w) (deriv (tubeB w₀) w) 0 v) w :=
  hasDerivAt_sigma_w (ψ := fun _ => 0)
    ((contDiffAt_tubeA h0 h1 hw1 hw3).differentiableAt (by simp)).hasDerivAt
    ((contDiffAt_tubeB h0 h1 hw1 hw3).differentiableAt (by simp)).hasDerivAt
    (hasDerivAt_const w 0) v

include h0 h1 in
theorem contDiffAt_Tube {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Tube w₀ p.1 p.2) (w, v) := by
  have hA : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => tubeA w₀ p.1) (w, v) :=
    (contDiffAt_tubeA h0 h1 hw1 hw3).comp (w, v) contDiffAt_fst
  have hB : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => tubeB w₀ p.1) (w, v) :=
    (contDiffAt_tubeB h0 h1 hw1 hw3).comp (w, v) contDiffAt_fst
  have hc : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => cos p.2) (w, v) :=
    Real.contDiff_cos.contDiffAt.comp (w, v) contDiffAt_snd
  have hs : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => sin p.2) (w, v) :=
    Real.contDiff_sin.contDiffAt.comp (w, v) contDiffAt_snd
  simp only [Tube, sigmaOf, rot2_zero]
  exact hA.prodMk ((hB.mul hc).prodMk (hB.mul hs))

include h0 h1 in
theorem Tube_immersion {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => Tube w₀ p.1 p.2) (w, v)) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => Tube w₀ p.1 p.2) (w, v) :=
    (contDiffAt_Tube h0 h1 hw1 hw3 v).differentiableAt (by simp)
  exact injective_fderiv_of_cross hd (hasDerivAt_Tube_w h0 h1 hw1 hw3 v) (hasDerivAt_Tube_v w₀ w v)
    (XTube_ne h0 h1 hw1 hw3 v)

include h0 h1 in
/-- 管の法線は、はめ込みの法線の定義に一致する。 -/
theorem XTube_eq {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    XTube w₀ w v =
      cross (deriv (fun v => Tube w₀ w v) v) (deriv (fun w => Tube w₀ w v) w) := by
  rw [(hasDerivAt_Tube_v w₀ w v).deriv, (hasDerivAt_Tube_w h0 h1 hw1 hw3 v).deriv]
  rfl

/-- 回転面の法線を、断面の値と速度と角の関数として書いたもの。 -/
def normalOfSig (q : (ℝ × ℝ × ℝ × ℝ) × ℝ) : V3 :=
  cross (sigV 0 q.1.2.1 q.2) (sigW 0 q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 0 q.2)

theorem continuous_normalOfSig : Continuous normalOfSig := by
  unfold normalOfSig sigV sigW rot2 cross
  fun_prop

theorem XTube_eq_normalOfSig (w₀ w v : ℝ) :
    XTube w₀ w v =
      normalOfSig ((tubeA w₀ w, tubeB w₀ w, deriv (tubeA w₀) w, deriv (tubeB w₀) w), v) := rfl

include h0 h1 in
theorem continuousOn_XTube :
    ContinuousOn (fun p : ℝ × ℝ => XTube w₀ p.1 p.2) (Ioo 1 3 ×ˢ univ) := by
  have hA := (contDiffOn_tubeA h0 h1).continuousOn
  have hB := (contDiffOn_tubeB h0 h1).continuousOn
  have hdA : ContinuousOn (deriv (tubeA w₀)) (Ioo 1 3) :=
    (contDiffOn_tubeA h0 h1).continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  have hdB : ContinuousOn (deriv (tubeB w₀)) (Ioo 1 3) :=
    (contDiffOn_tubeB h0 h1).continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)
  have hfst : ContinuousOn (fun p : ℝ × ℝ => p.1) (Ioo 1 3 ×ˢ univ) := continuous_fst.continuousOn
  have hmap : MapsTo (fun p : ℝ × ℝ => p.1) (Ioo 1 3 ×ˢ univ) (Ioo 1 3) := fun p hp => hp.1
  have htup : ContinuousOn (fun p : ℝ × ℝ =>
      (((tubeA w₀ p.1, tubeB w₀ p.1, deriv (tubeA w₀) p.1, deriv (tubeB w₀) p.1), p.2) :
        (ℝ × ℝ × ℝ × ℝ) × ℝ)) (Ioo 1 3 ×ˢ univ) :=
    ((hA.comp hfst hmap).prodMk ((hB.comp hfst hmap).prodMk
      ((hdA.comp hfst hmap).prodMk (hdB.comp hfst hmap)))).prodMk continuous_snd.continuousOn
  simp only [XTube_eq_normalOfSig]
  exact continuous_normalOfSig.comp_continuousOn htup

/-! ### 口での一致 -/

include h0 h1 in
theorem tubeA_of_right {w : ℝ} (hw1 : 1 ≤ w) (hwa : w ≤ wa w₀) : tubeA w₀ w = aa w := by
  simp only [tubeA, thT_of_le h0 h1 hwa, RP_fl_eq_rG h0 h1 hw1 hwa, rG_mul_cos]

include h0 h1 in
theorem tubeB_of_right {w : ℝ} (hw1 : 1 ≤ w) (hwa : w ≤ wa w₀) : tubeB w₀ w = bb w := by
  simp only [tubeB, thT_of_le h0 h1 hwa, RP_fl_eq_rG h0 h1 hw1 hwa, rG_mul_sin]

include h0 h1 in
/-- 右の口：w ∈ [1, wₐ] で Tube = G。 -/
theorem Tube_right {w : ℝ} (hw1 : 1 ≤ w) (hwa : w ≤ wa w₀) (v : ℝ) : Tube w₀ w v = G w v := by
  simp only [Tube, sigmaOf, rot2_zero, tubeA_of_right h0 h1 hw1 hwa, tubeB_of_right h0 h1 hw1 hwa]
  rw [G_eq_aa_bb]

include h0 h1 in
theorem tubeA_of_left {w : ℝ} (hwa : 4 - wa w₀ ≤ w) (hw3 : w ≤ 3) : tubeA w₀ w = aa (w - 4) := by
  have h4 : 1 ≤ 4 - w := by linarith
  have h5 : 4 - w ≤ wa w₀ := by linarith
  simp only [tubeA, thT_of_ge h0 h1 hwa, RP_symm, cos_pi_sub, RP_fl_eq_rG h0 h1 h4 h5]
  have e : w - 4 = -(4 - w) := by ring
  rw [e, aa_neg, ← rG_mul_cos]
  ring

include h0 h1 in
theorem tubeB_of_left {w : ℝ} (hwa : 4 - wa w₀ ≤ w) (hw3 : w ≤ 3) : tubeB w₀ w = bb (4 - w) := by
  have h4 : 1 ≤ 4 - w := by linarith
  have h5 : 4 - w ≤ wa w₀ := by linarith
  simp only [tubeB, thT_of_ge h0 h1 hwa, RP_symm, sin_pi_sub, RP_fl_eq_rG h0 h1 h4 h5, rG_mul_sin]

include h0 h1 in
/-- 左の口：w ∈ [4 − wₐ, 3] で Tube(w, v) = G(w − 4, v + π)。 -/
theorem Tube_left {w : ℝ} (hwa : 4 - wa w₀ ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    Tube w₀ w v = G (w - 4) (v + π) := by
  simp only [Tube, sigmaOf, rot2_zero, tubeA_of_left h0 h1 hwa hw3, tubeB_of_left h0 h1 hwa hw3]
  rw [G_add_pi]
  have e : -(w - 4) = 4 - w := by ring
  rw [e]

/-! ### 半径 -/

include h0 h1 in
theorem nsq_Tube {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    nsq (Tube w₀ w v) = sigP w₀ (thT w₀ w) / 2 := by
  rw [Tube, nsq_sigmaOf]
  simp only [tubeA, tubeB]
  rw [← RP_sq h0 h1 (thT_abs_le h0 h1 hw1 hw3)]
  linear_combination (RP w₀ (thT w₀ w) ^ 2) * sin_sq_add_cos_sq (thT w₀ w)

/-- sin 2θ₀ = 2w₀²/(1 + w₀⁴) = 2 Rad(w₀²)。 -/
theorem sin_two_th0 (w₀ : ℝ) : sin (2 * th0 w₀) = 2 * Rad (w₀ ^ 2) := by
  have hm : √(1 + w₀ ^ 4) * √(1 + w₀ ^ 4) = 1 + w₀ ^ 4 := Real.mul_self_sqrt (by positivity)
  have e : (w₀ ^ 2) ^ 2 = w₀ ^ 4 := by ring
  simp only [th0, sin_two_mul, sin_arctan, cos_arctan, e, Rad]
  rw [mul_assoc, div_mul_div_comm, hm, mul_one]

include h0 h1 in
/-- 管の半径は首の最大半径 |G(w₀, 0)|² = Rad(w₀²) より大きい。 -/
theorem nsq_Tube_gt {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    Rad (w₀ ^ 2) < nsq (Tube w₀ w v) := by
  rw [nsq_Tube h0 h1 hw1 hw3]
  have h2 := sigP_ge h0 h1 (thT_abs_le h0 h1 hw1 hw3)
  have h3 : sin (2 * th0 w₀) < sin (2 * u1 w₀) := by
    apply sin_lt_sin_of_lt_of_le_pi_div_two
    · linarith [th0_pos h0, pi_pos]
    · linarith [u1_lt h0 h1]
    · linarith [th0_lt_u1 h0 h1]
  rw [sin_two_th0] at h3
  linarith

end Tube

end Zeno.Model
