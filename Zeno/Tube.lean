/-
# Zeno.Tube : 定理 B8（反例世界）

同じ二つのホーンを、半回転なしの軸対称な管でもつなげる。左の端は G(w, v + π) で、
像は定理 B の左の端と同じ集合だが、助変数の向きが逆である。
この面も正則である。そして表裏は反転しない。

したがって「正則につなぐ」ことから反転は出ない。反転を決めるのは接続の類である。
反例世界があることで、定理 B の反転は結論として空虚でも自動的でもない。
-/
import Zeno.Regular

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

/-- 軸対称な面の半径 -/
def Btube (w₀ w : ℝ) : ℝ := bb (rho w₀ w)

/-- 半回転のない管 Σ′。 -/
def Tub (w₀ w v : ℝ) : V3 := sigmaOf aa (Btube w₀) (fun _ => 0) w v

/-- 管の法線場。 -/
def XT (w₀ w v : ℝ) : V3 :=
  cross (sigV 0 (Btube w₀ w) v)
    (sigW 0 (aa w) (Btube w₀ w) (deriv aa w) (deriv (Btube w₀) w) 0 v)

theorem Btube_pos {w₀ : ℝ} (h : w₀ ≠ 0) (w : ℝ) : 0 < Btube w₀ w := by
  have hr := rho_pos h w
  simp only [Btube, bb_eq]
  exact mul_pos (pow_pos hr 2) (aa_pos hr)

theorem contDiff_Btube {w₀ : ℝ} (h : w₀ ≠ 0) : ContDiff ℝ ∞ (Btube w₀) :=
  contDiff_bb.comp (contDiff_rho h)

theorem hasDerivAt_Btube {w₀ : ℝ} (h : w₀ ≠ 0) (w : ℝ) :
    HasDerivAt (Btube w₀) (db (rho w₀ w) * drho w₀ w) w :=
  (hasDerivAt_bb (rho w₀ w)).comp w (hasDerivAt_rho h w)

theorem contDiff_Tub {w₀ : ℝ} (h : w₀ ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => Tub w₀ p.1 p.2) := by
  have hA := contDiff_aa
  have hB := contDiff_Btube h
  simp only [Tub, sigmaOf, rot2]
  fun_prop

theorem hasDerivAt_Tub_v (w₀ w v : ℝ) :
    HasDerivAt (fun v => Tub w₀ w v) (sigV 0 (Btube w₀ w) v) v :=
  hasDerivAt_sigma_v aa (Btube w₀) (fun _ => 0) w v

theorem hasDerivAt_Tub_w {w₀ : ℝ} (h : w₀ ≠ 0) (w v : ℝ) :
    HasDerivAt (fun w => Tub w₀ w v)
      (sigW 0 (aa w) (Btube w₀ w) (deriv aa w) (deriv (Btube w₀) w) 0 v) w :=
  hasDerivAt_sigma_w (ψ := fun _ => 0) (contDiff_aa.differentiable (by simp) w).hasDerivAt
    ((contDiff_Btube h).differentiable (by simp) w).hasDerivAt (hasDerivAt_const w 0) v

theorem continuous_XT {w₀ : ℝ} (h : w₀ ≠ 0) :
    Continuous (fun p : ℝ × ℝ => XT w₀ p.1 p.2) := by
  have hA := contDiff_aa.continuous
  have hB := (contDiff_Btube h).continuous
  have hdA : Continuous (deriv aa) := contDiff_aa.continuous_deriv (by simp)
  have hdB : Continuous (deriv (Btube w₀)) := (contDiff_Btube h).continuous_deriv (by simp)
  simp only [XT, sigV, sigW, rot2, cross]
  fun_prop

/-- 管の断面曲線も正則である。 -/
theorem tube_profile_ne {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (w : ℝ) :
    ¬ (deriv aa w = 0 ∧ deriv (Btube w₀) w = 0) := by
  rintro ⟨hA, hB⟩
  have hne := h0.ne'
  rw [(hasDerivAt_aa w).deriv] at hA
  rw [(hasDerivAt_Btube hne w).deriv] at hB
  have hD : D w ^ 2 ≠ 0 := pow_ne_zero 2 (D_ne w)
  have e1 : 1 - 3 * w ^ 4 = 0 := by
    simp only [da] at hA
    rcases div_eq_zero_iff.mp hA with h | h
    · exact h
    · exact absurd h hD
  have hw0 : w ≠ 0 := by
    rintro rfl
    norm_num at e1
  have hw2 : w ^ 2 < 1 := by nlinarith [sq_nonneg (w ^ 2), sq_nonneg w]
  have hr := rho_sq_lt_one hne (by nlinarith) hw2
  have hrp := rho_pos hne w
  have hd : drho w₀ w ≠ 0 := by
    simp only [drho]
    exact div_ne_zero (mul_ne_zero (dh_pos hne _).ne' hw0) hrp.ne'
  have hb := (mul_eq_zero.mp hB).resolve_right hd
  have hD2 : D (rho w₀ w) ^ 2 ≠ 0 := pow_ne_zero 2 (D_ne _)
  have e2 : rho w₀ w ^ 2 * (3 - rho w₀ w ^ 4) = 0 := by
    simp only [db] at hb
    rcases div_eq_zero_iff.mp hb with h | h
    · exact h
    · exact absurd h hD2
  rcases mul_eq_zero.mp e2 with h | h
  · exact (pow_pos hrp 2).ne' h
  · nlinarith [pow_pos hrp 2, pow_pos hrp 4]

theorem XT_ne {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (w v : ℝ) : XT w₀ w v ≠ wp :=
  neck_lemma (Btube_pos h0.ne' w).ne' (tube_profile_ne h0 h1 w) (fun hd => absurd rfl hd) v

theorem Tub_periodic (w₀ w v : ℝ) : Tub w₀ w (v + 2 * π) = Tub w₀ w v := by
  simp [Tub, sigmaOf]

theorem Tub_immersion {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => Tub w₀ p.1 p.2) p) := by
  have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => Tub w₀ p.1 p.2) p :=
    (contDiff_Tub h0.ne').differentiable (by simp) p
  obtain ⟨w, v⟩ := p
  exact injective_fderiv_of_cross hd (hasDerivAt_Tub_w h0.ne' w v) (hasDerivAt_Tub_v w₀ w v)
    (XT_ne h0 h1 w v)

theorem Tub_right {w₀ w : ℝ} (h0 : 0 < w₀) (hw : w₀ * (4 / 5) < w) (v : ℝ) :
    Tub w₀ w v = G w v := by
  have hs := (sq_of_right h0 hw).le
  have hpos : 0 < w := by
    have : 0 < w₀ * (4 / 5) := by positivity
    linarith
  simp only [Tub, sigmaOf, rot2_zero, Btube, rho_of h0.ne' hs, abs_of_pos hpos]
  rw [G_eq_aa_bb]

theorem G_add_pi (w v : ℝ) : G w (v + π) = (aa w, bb (-w) * cos v, bb (-w) * sin v) := by
  rw [G_eq_aa_bb, cos_add_pi, sin_add_pi, bb_neg]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem Tub_left {w₀ w : ℝ} (h0 : 0 < w₀) (hw : w < -(w₀ * (4 / 5))) (v : ℝ) :
    Tub w₀ w v = G w (v + π) := by
  have hs := (sq_of_left h0 hw).le
  have hneg : w < 0 := by
    have : 0 < w₀ * (4 / 5) := by positivity
    linarith
  simp only [Tub, sigmaOf, rot2_zero, Btube, rho_of h0.ne' hs, abs_of_neg hneg]
  rw [G_add_pi]

/-- 半回転のない管の面の性質。 -/
structure IsTubeSurface (w₀ : ℝ) (S X : ℝ → ℝ → V3) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p.1 p.2)
  periodic : ∀ w v, S w (v + 2 * π) = S w v
  normal : ∀ w v, X w v = cross (deriv (fun v => S w v) v) (deriv (fun w => S w v) w)
  normal_cont : Continuous (fun p : ℝ × ℝ => X p.1 p.2)
  normal_ne : ∀ w v, X w v ≠ wp
  immersion : ∀ p, Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => S p.1 p.2) p)
  right : ∀ w v, w₀ < w → S w v = G w v
  left : ∀ w v, w < -w₀ → S w v = G w (v + π)

theorem Tub_isTubeSurface {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) :
    IsTubeSurface w₀ (Tub w₀) (XT w₀) where
  smooth := contDiff_Tub h0.ne'
  periodic := Tub_periodic w₀
  normal := fun w v => by
    rw [(hasDerivAt_Tub_v w₀ w v).deriv, (hasDerivAt_Tub_w h0.ne' w v).deriv]
    rfl
  normal_cont := continuous_XT h0.ne'
  normal_ne := XT_ne h0 h1
  immersion := Tub_immersion h0 h1
  right := fun w v hw => Tub_right h0 (by nlinarith) v
  left := fun w v hw => Tub_left h0 (by nlinarith) v

theorem IsTubeSurface.isNormalField {w₀ : ℝ} {S X : ℝ → ℝ → V3} (h : IsTubeSurface w₀ S X) :
    IsNormalField S (fun p => X p.1 p.2) where
  cont := h.normal_cont
  ne := fun p => h.normal_ne p.1 p.2
  perp := fun p => by
    simp only [h.normal p.1 p.2]
    exact ⟨dot_cross_left _ _, dot_cross_right _ _⟩

/-- **B8（反例世界）**：左の端が G(w, v + π) である正則な面では、どの連続な法線場でも
両岸のラベルは同じである。面の個別の形にはよらない。 -/
theorem tube_no_reversal {w₀ : ℝ} (h0 : 0 < w₀) {S X : ℝ → ℝ → V3} (h : IsTubeSurface w₀ S X)
    {n : ℝ × ℝ → V3} (hn : IsNormalField S n) {w₁ w₂ : ℝ} (h₁ : w₀ < w₁) (h₂ : w₂ < -w₀)
    (v₁ v₂ : ℝ) : 0 < side (S w₁ v₁) (n (w₁, v₁)) * side (S w₂ v₂) (n (w₂, v₂)) := by
  obtain ⟨c, -, hsm, hs⟩ := normal_rigid h.normal_cont h.normal_ne h.normal hn
  have hh := (side_mul_of_rigid (α := ℝ × ℝ) (n := n) (N₀ := fun p => X p.1 p.2) (c := c) hsm hs
    (q₁ := S w₁ v₁) (q₂ := S w₂ v₂) (p₁ := (w₁, v₁)) (p₂ := (w₂, v₂))).2
  refine hh (mul_pos ?_ ?_)
  · -- 右岸
    have hpos : 0 < w₁ := by linarith
    have e1 : (fun v => S w₁ v) = fun v => G w₁ v := funext fun v => h.right w₁ v h₁
    have e2 : (fun w => S w v₁) =ᶠ[𝓝 w₁] fun w => G w v₁ := by
      filter_upwards [Ioi_mem_nhds h₁] with y hy using h.right y v₁ hy
    have hX : X w₁ v₁ = cross (Tv w₁ v₁) (Tw w₁ v₁) := by
      rw [h.normal, e1, e2.deriv_eq, (hasDerivAt_G_v w₁ v₁).deriv, (hasDerivAt_G_w w₁ v₁).deriv]
    simp only [h.right w₁ v₁ h₁, hX, cross_Tv_Tw_smul']
    refine side_right hpos ?_ v₁
    have := D_pos w₁
    positivity
  · -- 左岸
    have hneg : w₂ < 0 := by linarith
    have e1 : (fun v => S w₂ v) = fun v => G w₂ (v + π) := funext fun v => h.left w₂ v h₂
    have e2 : (fun w => S w v₂) =ᶠ[𝓝 w₂] fun w => G w (v₂ + π) := by
      filter_upwards [Iio_mem_nhds h₂] with y hy using h.left y v₂ hy
    have hv : HasDerivAt (fun v => G w₂ (v + π)) (Tv w₂ (v₂ + π)) v₂ := by
      have h3 : HasDerivAt (fun v => v + π) 1 v₂ := by
        simpa using (hasDerivAt_id' v₂).add_const π
      have h4 := (hasDerivAt_G_v w₂ (v₂ + π)).scomp v₂ h3
      rw [one_smul] at h4
      exact h4
    have hX : X w₂ v₂ = cross (Tv w₂ (v₂ + π)) (Tw w₂ (v₂ + π)) := by
      rw [h.normal, e1, e2.deriv_eq, hv.deriv, (hasDerivAt_G_w w₂ (v₂ + π)).deriv]
    simp only [h.left w₂ v₂ h₂, hX, cross_Tv_Tw_smul', side_smul, side_G_N]
    have hD := D_pos w₂
    have h3 : w₂ ^ 3 < 0 := Odd.pow_neg (by decide) hneg
    have h5 : w₂ ^ 5 < 0 := Odd.pow_neg (by decide) hneg
    have e : w₂ ^ 3 / D w₂ ^ 3 * (2 * w₂ ^ 5 / D w₂) =
        2 * (-w₂ ^ 3) * (-w₂ ^ 5) / D w₂ ^ 4 := by
      field_simp
    rw [e]
    have : 0 < -w₂ ^ 3 := by linarith
    have : 0 < -w₂ ^ 5 := by linarith
    positivity

/-- 首の中まで点対称にすると、面は ℘ を通る。定理 B の Σ はこれを避けるので、首の中で対称性が破れる。 -/
theorem symmetric_neck_passes_wp {S : ℝ → ℝ → V3} (h : ∀ w v, S (-w) (π - v) = -S w v) :
    S 0 (π / 2) = wp := by
  have h0 := h 0 (π / 2)
  have e : π - π / 2 = π / 2 := by ring
  rw [neg_zero, e] at h0
  have h1 : (2 : ℝ) • S 0 (π / 2) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h0]
    simp
  rcases smul_eq_zero.mp h1 with h2 | h2
  · norm_num at h2
  · exact h2

/-- 軸対称な形では定理 B の左の端を実現できない。半回転は省けない。 -/
theorem no_equivariant_neck {w : ℝ} (hw : w ≠ 0) :
    ¬ ∃ A B : ℝ, ∀ v, ((A, B * cos v, B * sin v) : V3) = G w (π - v) := by
  rintro ⟨A, B, h⟩
  have h1 := h 0
  have h2 := h (π / 2)
  rw [G_eq_aa_bb] at h1 h2
  have e1 : B * cos 0 = bb w * cos (π - 0) := congrArg (fun z : V3 => z.2.1) h1
  have e2 : B * sin (π / 2) = bb w * sin (π - π / 2) := congrArg (fun z : V3 => z.2.2) h2
  simp only [cos_zero, sub_zero, cos_pi, mul_one, mul_neg] at e1
  have e3 : π - π / 2 = π / 2 := by ring
  rw [e3] at e2
  simp only [sin_pi_div_two, mul_one] at e2
  have hb : bb w = 0 := by linarith
  have hD := D_ne w
  simp only [bb] at hb
  rcases div_eq_zero_iff.mp hb with h3 | h3
  · exact hw (pow_eq_zero_iff (by norm_num) |>.mp h3)
  · exact hD h3

end Zeno.Model
