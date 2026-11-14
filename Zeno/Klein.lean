/-
# Zeno.Klein : クラインの壺型閉包の源曲面 Ŝ（構成 K）

被覆平面 ℝ² の上の Γ 不変な写像として、閉じた曲面 M = ℝ²/Γ の像を作る。
Γ = ⟨T, Ω⟩、T(w, v) = (w, v + 2π)、Ω(w, v) = (w + 4, −v)。
帯 [−1, 3] の上では、首 Σ（|w| ≤ 1）、外側の管 Tube、そして左の首 Σ(w − 4, −v) を貼る。
右の口 w ∈ [1, wₐ] と左の口 w ∈ [4 − wₐ, 3] で、管はホーン G に正確に一致する。

M をただ一つの Lean の型として作らず、Ŝ(w + 4, −v) = Ŝ(w, v) を満たす写像として形式化する。
法線 X̂ = ∂ᵥŜ × ∂wŜ は X̂(w + 4, −v) = −X̂(w, v) を満たす（K-d）。
Γ と両立する連続で消えない法線場はない（K-e、M2）。
-/
import Zeno.KleinTube

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

/-! ### はめ込みの法線と、局所的な良さ -/

/-- はめ込みの法線 ∂ᵥ × ∂w（第 3.1 版の規約、`IsNeckSurface.normal` と同じ順序）。 -/
def normalOf (F : ℝ → ℝ → V3) (w v : ℝ) : V3 :=
  cross (deriv (fun v => F w v) v) (deriv (fun w => F w v) w)

theorem cross_smul_left (c : ℝ) (a b : V3) : cross (c • a) b = c • cross a b := by
  simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- 一点での良さ：滑らか、法線が消えない、法線が連続。 -/
structure GoodAt (F : ℝ → ℝ → V3) (q : ℝ × ℝ) : Prop where
  smooth : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) q
  ne : normalOf F q.1 q.2 ≠ wp
  cont : ContinuousAt (fun p : ℝ × ℝ => normalOf F p.1 p.2) q

theorem differentiableAt_partial_v {F : ℝ → ℝ → V3} {w v : ℝ}
    (h : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, v)) :
    DifferentiableAt ℝ (fun v => F w v) v := by
  have hl : DifferentiableAt ℝ (fun x : ℝ => ((w, x) : ℝ × ℝ)) v :=
    (differentiableAt_const w).prodMk differentiableAt_id
  exact h.comp v hl

theorem differentiableAt_partial_w {F : ℝ → ℝ → V3} {w v : ℝ}
    (h : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, v)) :
    DifferentiableAt ℝ (fun w => F w v) w := by
  have hl : DifferentiableAt ℝ (fun x : ℝ => ((x, v) : ℝ × ℝ)) w :=
    differentiableAt_id.prodMk (differentiableAt_const v)
  exact h.comp w hl

theorem GoodAt.differentiableAt {F : ℝ → ℝ → V3} {q : ℝ × ℝ} (h : GoodAt F q) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) q :=
  h.smooth.differentiableAt (by simp)

/-- 良い点でははめ込みである。 -/
theorem GoodAt.immersion {F : ℝ → ℝ → V3} {q : ℝ × ℝ} (h : GoodAt F q) :
    Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) q) := by
  obtain ⟨w, v⟩ := q
  have hd := h.differentiableAt
  exact injective_fderiv_of_cross hd (differentiableAt_partial_w hd).hasDerivAt
    (differentiableAt_partial_v hd).hasDerivAt h.ne

/-- 近傍で一致する二つの写像は同じ法線をもつ。 -/
theorem normalOf_congr {F F' : ℝ → ℝ → V3} {q : ℝ × ℝ}
    (h : (fun p : ℝ × ℝ => F' p.1 p.2) =ᶠ[𝓝 q] fun p => F p.1 p.2) :
    normalOf F' q.1 q.2 = normalOf F q.1 q.2 := by
  obtain ⟨w, v⟩ := q
  have hv : (fun v => F' w v) =ᶠ[𝓝 v] fun v => F w v := by
    have ht : Tendsto (fun x : ℝ => ((w, x) : ℝ × ℝ)) (𝓝 v) (𝓝 (w, v)) :=
      (continuous_const.prodMk continuous_id).tendsto v
    exact h.comp_tendsto ht
  have hw : (fun w => F' w v) =ᶠ[𝓝 w] fun w => F w v := by
    have ht : Tendsto (fun x : ℝ => ((x, v) : ℝ × ℝ)) (𝓝 w) (𝓝 (w, v)) :=
      (continuous_id.prodMk continuous_const).tendsto w
    exact h.comp_tendsto ht
  simp only [normalOf, hv.deriv_eq, hw.deriv_eq]

theorem normalOf_eventuallyEq {F F' : ℝ → ℝ → V3} {q : ℝ × ℝ}
    (h : (fun p : ℝ × ℝ => F' p.1 p.2) =ᶠ[𝓝 q] fun p => F p.1 p.2) :
    (fun p : ℝ × ℝ => normalOf F' p.1 p.2) =ᶠ[𝓝 q] fun p => normalOf F p.1 p.2 := by
  filter_upwards [h.eventually_nhds] with p hp
  exact normalOf_congr hp

theorem GoodAt.congr {F F' : ℝ → ℝ → V3} {q : ℝ × ℝ} (hF : GoodAt F q)
    (h : (fun p : ℝ × ℝ => F' p.1 p.2) =ᶠ[𝓝 q] fun p => F p.1 p.2) : GoodAt F' q where
  smooth := hF.smooth.congr_of_eventuallyEq h
  ne := by rw [normalOf_congr h]; exact hF.ne
  cont := hF.cont.congr (normalOf_eventuallyEq h).symm

/-! ### アフィンな助変数の付け替え (w, v) ↦ (w + c, s v)、s = ±1 -/

theorem deriv_affine_v {F : ℝ → ℝ → V3} {c s w v : ℝ}
    (hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w + c, s * v)) :
    deriv (fun v => F (w + c) (s * v)) v = s • deriv (fun v => F (w + c) v) (s * v) := by
  have h1 := (differentiableAt_partial_v hd).hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => s * x) s v := by
    simpa using (hasDerivAt_id v).const_mul s
  have h3 := h1.scomp v h2
  exact h3.deriv

theorem deriv_affine_w {F : ℝ → ℝ → V3} {c s w v : ℝ}
    (hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w + c, s * v)) :
    deriv (fun w => F (w + c) (s * v)) w = deriv (fun w => F w (s * v)) (w + c) := by
  have h1 := (differentiableAt_partial_w hd).hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => x + c) 1 w := (hasDerivAt_id w).add_const c
  have h3 := h1.scomp w h2
  rw [one_smul] at h3
  exact h3.deriv

theorem normalOf_affine {F : ℝ → ℝ → V3} {c s w v : ℝ}
    (hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w + c, s * v)) :
    normalOf (fun w v => F (w + c) (s * v)) w v = s • normalOf F (w + c) (s * v) := by
  simp only [normalOf]
  rw [deriv_affine_v hd, deriv_affine_w hd, cross_smul_left]

theorem contDiffAt_affine {F : ℝ → ℝ → V3} {c s : ℝ} {q : ℝ × ℝ}
    (h : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => F p.1 p.2) (q.1 + c, s * q.2)) :
    ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => F (p.1 + c) (s * p.2)) q := by
  have hl : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => ((p.1 + c, s * p.2) : ℝ × ℝ)) q := by fun_prop
  exact h.comp q hl

theorem GoodAt.affine {F : ℝ → ℝ → V3} {c s : ℝ} (hs : s = 1 ∨ s = -1) {q : ℝ × ℝ}
    (h : GoodAt F (q.1 + c, s * q.2)) : GoodAt (fun w v => F (w + c) (s * v)) q where
  smooth := contDiffAt_affine h.smooth
  ne := by
    rw [normalOf_affine h.differentiableAt]
    intro he
    have hs0 : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
    rcases smul_eq_zero.mp (show s • normalOf F (q.1 + c) (s * q.2) = 0 from he) with h' | h'
    · exact hs0 h'
    · exact h.ne h'
  cont := by
    have hl : Continuous (fun p : ℝ × ℝ => ((p.1 + c, s * p.2) : ℝ × ℝ)) := by fun_prop
    have h1 : ContinuousAt (fun p : ℝ × ℝ => normalOf F (p.1 + c) (s * p.2)) q :=
      ContinuousAt.comp (f := fun p : ℝ × ℝ => ((p.1 + c, s * p.2) : ℝ × ℝ))
        (g := fun p : ℝ × ℝ => normalOf F p.1 p.2) h.cont hl.continuousAt
    have h2 : ContinuousAt (fun p : ℝ × ℝ => s • normalOf F (p.1 + c) (s * p.2)) q :=
      h1.const_smul s
    refine h2.congr ?_
    have hopen : ∀ᶠ p in 𝓝 q, DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (p.1 + c, s * p.2) := by
      have h1' : ContDiffAt ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2) (q.1 + c, s * q.2) :=
        h.smooth.of_le (by simp)
      have := h1'.eventually (by simp)
      have ht : Tendsto (fun p : ℝ × ℝ => ((p.1 + c, s * p.2) : ℝ × ℝ)) (𝓝 q)
          (𝓝 (q.1 + c, s * q.2)) := hl.tendsto q
      filter_upwards [ht.eventually this] with p hp
      exact hp.differentiableAt (by simp)
    filter_upwards [hopen] with p hp
    exact (normalOf_affine hp).symm

/-! ### 良い写像の実例：Σ と管 -/

section Examples

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
theorem normalOf_Sig (w v : ℝ) : normalOf (Sig w₀) w v = Xf w₀ w v :=
  ((Sig_isNeckSurface h0 h1).normal w v).symm

include h0 h1 in
theorem goodAt_Sig (q : ℝ × ℝ) : GoodAt (Sig w₀) q where
  smooth := (contDiff_Sig h0.ne').contDiffAt
  ne := by rw [normalOf_Sig h0 h1]; exact Xf_ne h0 h1 _ _
  cont := by
    have e : (fun p : ℝ × ℝ => normalOf (Sig w₀) p.1 p.2) = fun p => Xf w₀ p.1 p.2 :=
      funext fun p => normalOf_Sig h0 h1 p.1 p.2
    rw [e]; exact (continuous_Xf h0.ne').continuousAt

include h0 h1 in
theorem normalOf_Tube {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    normalOf (Tube w₀) w v = XTube w₀ w v :=
  (XTube_eq h0 h1 hw1 hw3 v).symm

include h0 h1 in
theorem goodAt_Tube {w v : ℝ} (hw1 : 1 < w) (hw3 : w < 3) : GoodAt (Tube w₀) (w, v) where
  smooth := contDiffAt_Tube h0 h1 hw1.le hw3.le v
  ne := by rw [normalOf_Tube h0 h1 hw1.le hw3.le]; exact XTube_ne h0 h1 hw1.le hw3.le v
  cont := by
    have hU : IsOpen (Ioo (1 : ℝ) 3 ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
    have hq : (w, v) ∈ Ioo (1 : ℝ) 3 ×ˢ (univ : Set ℝ) := ⟨⟨hw1, hw3⟩, trivial⟩
    have hc := (continuousOn_XTube h0 h1).continuousAt (hU.mem_nhds hq)
    refine hc.congr ?_
    filter_upwards [hU.mem_nhds hq] with p hp
    exact (normalOf_Tube h0 h1 hp.1.1.le hp.1.2.le p.2).symm

end Examples

/-! ### 帯の上の面 Strip -/

/-- 右の境目 c₁ = (1 + wₐ)/2 ∈ (1, wₐ)。 -/
def c1 (w₀ : ℝ) : ℝ := (1 + wa w₀) / 2

/-- 左の境目 c₂ = (7 − wₐ)/2 ∈ (4 − wₐ, 3)。 -/
def c2 (w₀ : ℝ) : ℝ := (7 - wa w₀) / 2

/-- 帯 [−1, 3] の上の面：首 Σ、管、左の首 Σ(w − 4, −v)。 -/
def Strip (w₀ w v : ℝ) : V3 :=
  if w ≤ c1 w₀ then Sig w₀ w v else if w ≤ c2 w₀ then Tube w₀ w v else Sig w₀ (w - 4) (-v)

section Strip

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
theorem c1_gt_one : 1 < c1 w₀ := by have := wa_gt_one h0 h1; simp only [c1]; linarith

include h0 h1 in
theorem c1_lt_wa : c1 w₀ < wa w₀ := by have := wa_gt_one h0 h1; simp only [c1]; linarith

include h0 h1 in
theorem c2_gt : 4 - wa w₀ < c2 w₀ := by have := wa_gt_one h0 h1; simp only [c2]; linarith

include h0 h1 in
theorem c2_lt_three : c2 w₀ < 3 := by have := wa_gt_one h0 h1; simp only [c2]; linarith

include h0 h1 in
theorem wa_lt_c2 : wa w₀ < c2 w₀ := by have := wa_lt_two h0 h1; simp only [c2]; linarith

include h0 h1 in
theorem c1_lt_four_sub_wa : c1 w₀ < 4 - wa w₀ := by
  have := wa_lt_two h0 h1; simp only [c1]; linarith

include h0 h1 in
theorem Sig_eq_G_of_ge_one {w : ℝ} (hw : 1 ≤ w) (v : ℝ) : Sig w₀ w v = G w v :=
  Sig_right h0 (by nlinarith) v

include h0 h1 in
theorem Sig_eq_G_of_le_neg_one {w : ℝ} (hw : w ≤ -1) (v : ℝ) : Sig w₀ w v = G w (π - v) := by
  have : w₀ * (4 / 5) < 1 := by nlinarith
  exact Sig_left h0 (by linarith) v

include h0 h1 in
/-- w < wₐ で Strip = Σ。 -/
theorem Strip_eq_Sig_of {w : ℝ} (hw : w < wa w₀) (v : ℝ) : Strip w₀ w v = Sig w₀ w v := by
  simp only [Strip]
  split_ifs with hc1 hc2
  · rfl
  · push Not at hc1
    have h1' : 1 ≤ w := by linarith [c1_gt_one h0 h1]
    rw [Tube_right h0 h1 h1' hw.le, Sig_eq_G_of_ge_one h0 h1 h1']
  · exfalso
    push Not at hc2
    linarith [wa_lt_c2 h0 h1]

include h0 h1 in
/-- 1 < w < 3 で Strip = Tube。 -/
theorem Strip_eq_Tube_of {w : ℝ} (hw1 : 1 < w) (hw3 : w < 3) (v : ℝ) :
    Strip w₀ w v = Tube w₀ w v := by
  simp only [Strip]
  split_ifs with hc1 hc2
  · rw [Sig_eq_G_of_ge_one h0 h1 hw1.le, Tube_right h0 h1 hw1.le (by linarith [c1_lt_wa h0 h1])]
  · rfl
  · push Not at hc2
    rw [Sig_eq_G_of_le_neg_one h0 h1 (by linarith), Tube_left h0 h1 (by linarith [c2_gt h0 h1]) hw3.le]
    congr 1; ring

include h0 h1 in
/-- 4 − wₐ < w で Strip(w, v) = Σ(w − 4, −v)。 -/
theorem Strip_eq_SigL_of {w : ℝ} (hwa : 4 - wa w₀ < w) (v : ℝ) :
    Strip w₀ w v = Sig w₀ (w - 4) (-v) := by
  simp only [Strip]
  split_ifs with hc1 hc2
  · exfalso; linarith [c1_lt_four_sub_wa h0 h1]
  · rw [Tube_left h0 h1 hwa.le (by linarith [c2_lt_three h0 h1]),
      Sig_eq_G_of_le_neg_one h0 h1 (by linarith [c2_lt_three h0 h1])]
    congr 1; ring
  · rfl

include h0 h1 in
/-- 4 − wₐ ≤ w ≤ 3 で Strip(w, v) = G(w − 4, v + π)。 -/
theorem Strip_eq_GL_of {w : ℝ} (hwa : 4 - wa w₀ ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    Strip w₀ w v = G (w - 4) (v + π) := by
  simp only [Strip]
  split_ifs with hc1 hc2
  · exfalso; linarith [c1_lt_four_sub_wa h0 h1]
  · exact Tube_left h0 h1 hwa hw3 v
  · rw [Sig_eq_G_of_le_neg_one h0 h1 (by linarith)]
    congr 1; ring

include h0 h1 in
/-- 1 ≤ w ≤ wₐ で Strip = G。 -/
theorem Strip_eq_G_of {w : ℝ} (hw1 : 1 ≤ w) (hwa : w ≤ wa w₀) (v : ℝ) : Strip w₀ w v = G w v := by
  simp only [Strip]
  split_ifs with hc1 hc2
  · exact Sig_eq_G_of_ge_one h0 h1 hw1 v
  · exact Tube_right h0 h1 hw1 hwa v
  · exfalso; push Not at hc2; linarith [wa_lt_c2 h0 h1]

theorem Strip_periodic (w₀ w v : ℝ) : Strip w₀ w (v + 2 * π) = Strip w₀ w v := by
  simp only [Strip]
  split_ifs
  · exact Sig_periodic _ _ _
  · exact Tube_periodic _ _ _
  · have h := Sig_periodic w₀ (w - 4) (-v - 2 * π)
    have e1 : -v - 2 * π + 2 * π = -v := by ring
    have e2 : -(v + 2 * π) = -v - 2 * π := by ring
    rw [e1] at h
    rw [e2, h]

theorem Strip_periodic' (w₀ w v : ℝ) : Strip w₀ w (v - 2 * π) = Strip w₀ w v := by
  have h := Strip_periodic w₀ w (v - 2 * π)
  have e : v - 2 * π + 2 * π = v := by ring
  rw [e] at h
  exact h.symm

include h0 h1 in
/-- Strip はどの点でも良い（滑らか、はめ込み、法線が連続）。 -/
theorem goodAt_Strip (q : ℝ × ℝ) : GoodAt (Strip w₀) q := by
  obtain ⟨w, v⟩ := q
  by_cases hA : w < wa w₀
  · refine (goodAt_Sig h0 h1 (w, v)).congr ?_
    have hopen : IsOpen {p : ℝ × ℝ | p.1 < wa w₀} := isOpen_lt continuous_fst continuous_const
    filter_upwards [hopen.mem_nhds hA] with p hp
    exact Strip_eq_Sig_of h0 h1 hp p.2
  · push Not at hA
    by_cases hB : w < 3
    · have hw1 : 1 < w := by linarith [wa_gt_one h0 h1]
      refine (goodAt_Tube h0 h1 hw1 hB).congr ?_
      have hopen : IsOpen {p : ℝ × ℝ | 1 < p.1 ∧ p.1 < 3} :=
        (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
      filter_upwards [hopen.mem_nhds ⟨hw1, hB⟩] with p hp
      exact Strip_eq_Tube_of h0 h1 hp.1 hp.2 p.2
    · push Not at hB
      have hg : GoodAt (fun w v => Sig w₀ (w + -4) (-1 * v)) (w, v) :=
        (goodAt_Sig h0 h1 (w + -4, -1 * v)).affine (Or.inr rfl)
      refine hg.congr ?_
      have hopen : IsOpen {p : ℝ × ℝ | 4 - wa w₀ < p.1} := isOpen_lt continuous_const continuous_fst
      have hmem : (w, v) ∈ {p : ℝ × ℝ | 4 - wa w₀ < p.1} := by
        show 4 - wa w₀ < w
        linarith [wa_gt_one h0 h1]
      filter_upwards [hopen.mem_nhds hmem] with p hp
      rw [Strip_eq_SigL_of h0 h1 hp]
      simp only [sub_eq_add_neg, neg_one_mul]

include h0 h1 in
theorem Strip_ne_wp {w : ℝ} (hw : w < 3) (v : ℝ) : Strip w₀ w v ≠ wp := by
  by_cases hA : w < wa w₀
  · rw [Strip_eq_Sig_of h0 h1 hA]; exact Sig_ne_wp h0.ne' _ _
  · push Not at hA
    have hw1 : 1 < w := by linarith [wa_gt_one h0 h1]
    rw [Strip_eq_Tube_of h0 h1 hw1 hw]
    intro he
    have h := nsq_Tube_gt h0 h1 hw1.le hw.le v
    rw [he] at h
    have h2 : 0 < Rad (w₀ ^ 2) := Rad_pos (by positivity)
    simp [nsq, dot, wp] at h
    linarith

end Strip

/-! ### 源曲面 Ŝ：帯を Γ で延ばす -/

/-- 符号 (−1)^k。 -/
def sgn (k : ℤ) : ℝ := if Even k then 1 else -1

theorem sgn_eq (k : ℤ) : sgn k = 1 ∨ sgn k = -1 := by
  unfold sgn; split_ifs <;> simp

theorem sgn_succ (k : ℤ) : sgn (k + 1) = -sgn k := by
  unfold sgn
  by_cases h : Even k
  · simp [h]
  · simp [h]

theorem sgn_mul_self (k : ℤ) : sgn k * sgn k = 1 := by
  rcases sgn_eq k with h | h <;> rw [h] <;> norm_num

theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

theorem sgn_one : sgn 1 = -1 := by
  have := sgn_succ 0
  rw [zero_add, sgn_zero] at this
  exact this

/-- 帯の番号 k(w) = ⌊(w + 1)/4⌋。 -/
def kk (w : ℝ) : ℤ := ⌊(w + 1) / 4⌋

theorem kk_eq_iff {w : ℝ} {k : ℤ} : kk w = k ↔ 4 * (k : ℝ) - 1 ≤ w ∧ w < 4 * k + 3 := by
  simp only [kk, Int.floor_eq_iff]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

theorem kk_add_four (w : ℝ) : kk (w + 4) = kk w + 1 := by
  simp only [kk]
  have e : (w + 4 + 1) / 4 = (w + 1) / 4 + 1 := by ring
  rw [e, Int.floor_add_one]

theorem kk_of_mem {w : ℝ} (h1 : -1 ≤ w) (h2 : w < 3) : kk w = 0 :=
  kk_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩

theorem kk_three : kk 3 = 1 :=
  kk_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩

/-- **源曲面 Ŝ**：Ŝ(w, v) = Strip(w − 4k, (−1)^k v)、k = ⌊(w + 1)/4⌋。 -/
def Shat (w₀ w v : ℝ) : V3 := Strip w₀ (w - 4 * (kk w : ℝ)) (sgn (kk w) * v)

/-- Ŝ の法線場 X̂ = ∂ᵥŜ × ∂wŜ。 -/
def Xhat (w₀ : ℝ) : ℝ → ℝ → V3 := normalOf (Shat w₀)

section Shat

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

/-- K-c：降下 Ŝ(w + 4, −v) = Ŝ(w, v)。 -/
theorem Shat_glide (w₀ w v : ℝ) : Shat w₀ (w + 4) (-v) = Shat w₀ w v := by
  simp only [Shat, kk_add_four, sgn_succ]
  congr 1
  · push_cast; ring
  · ring

theorem Shat_periodic (w₀ w v : ℝ) : Shat w₀ w (v + 2 * π) = Shat w₀ w v := by
  simp only [Shat]
  rcases sgn_eq (kk w) with h | h
  · rw [h, one_mul, one_mul, Strip_periodic]
  · rw [h, neg_one_mul, neg_one_mul]
    have e : -(v + 2 * π) = -v - 2 * π := by ring
    rw [e, Strip_periodic']

include h0 h1 in
/-- 帯 (4k − wₐ, 4k + 3) の上で Ŝ は Strip∘（アフィン写像）に一致する。 -/
theorem Shat_eq_strip_of {k : ℤ} {w : ℝ} (hw1 : 4 * (k : ℝ) - wa w₀ < w) (hw2 : w < 4 * k + 3)
    (v : ℝ) : Shat w₀ w v = Strip w₀ (w + -(4 * (k : ℝ))) (sgn k * v) := by
  by_cases hk : 4 * (k : ℝ) - 1 ≤ w
  · have e : kk w = k := kk_eq_iff.mpr ⟨hk, hw2⟩
    simp only [Shat, e, sub_eq_add_neg]
  · push Not at hk
    have e : kk w = k - 1 := by
      rw [kk_eq_iff]
      push_cast
      constructor <;> linarith [wa_lt_two h0 h1]
    simp only [Shat, e]
    have hs : sgn (k - 1) = -sgn k := by
      have := sgn_succ (k - 1)
      rw [sub_add_cancel] at this
      rw [this]; ring
    rw [hs]
    have hgt : 4 - wa w₀ < w - 4 * ((k - 1 : ℤ) : ℝ) := by push_cast; linarith
    rw [Strip_eq_SigL_of h0 h1 hgt, Strip_eq_Sig_of h0 h1 (by linarith [wa_gt_one h0 h1])]
    congr 1
    · push_cast; ring
    · ring

include h0 h1 in
theorem Shat_eventually (q : ℝ × ℝ) :
    (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) =ᶠ[𝓝 q]
      fun p => Strip w₀ (p.1 + -(4 * (kk q.1 : ℝ))) (sgn (kk q.1) * p.2) := by
  set k := kk q.1 with hk
  have hq := kk_eq_iff.mp hk.symm
  have hopen : IsOpen {p : ℝ × ℝ | 4 * (k : ℝ) - wa w₀ < p.1 ∧ p.1 < 4 * k + 3} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hmem : q ∈ {p : ℝ × ℝ | 4 * (k : ℝ) - wa w₀ < p.1 ∧ p.1 < 4 * k + 3} :=
    ⟨by linarith [hq.1, wa_gt_one h0 h1], hq.2⟩
  filter_upwards [hopen.mem_nhds hmem] with p hp
  exact Shat_eq_strip_of h0 h1 hp.1 hp.2 p.2

include h0 h1 in
theorem goodAt_Shat (q : ℝ × ℝ) : GoodAt (Shat w₀) q := by
  have hg : GoodAt (fun w v => Strip w₀ (w + -(4 * (kk q.1 : ℝ))) (sgn (kk q.1) * v)) q :=
    (goodAt_Strip h0 h1 _).affine (sgn_eq _)
  exact hg.congr (Shat_eventually h0 h1 q)

include h0 h1 in
theorem contDiff_Shat : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) :=
  contDiff_iff_contDiffAt.mpr fun q => (goodAt_Shat h0 h1 q).smooth

include h0 h1 in
theorem Shat_immersion (q : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) q) :=
  (goodAt_Shat h0 h1 q).immersion

include h0 h1 in
theorem Xhat_ne (w v : ℝ) : Xhat w₀ w v ≠ wp := (goodAt_Shat h0 h1 (w, v)).ne

include h0 h1 in
theorem continuous_Xhat : Continuous (fun p : ℝ × ℝ => Xhat w₀ p.1 p.2) :=
  continuous_iff_continuousAt.mpr fun q => (goodAt_Shat h0 h1 q).cont

include h0 h1 in
/-- 首：|w| ≤ 1 で Ŝ = Σ（実際には −wₐ < w < wₐ で成り立つ）。 -/
theorem Shat_eq_Sig_of {w : ℝ} (hw1 : -(wa w₀) < w) (hw2 : w < wa w₀) (v : ℝ) :
    Shat w₀ w v = Sig w₀ w v := by
  rw [Shat_eq_strip_of h0 h1 (k := 0) (by push_cast; linarith) (by push_cast; linarith [wa_lt_two h0 h1])]
  simp only [Int.cast_zero, mul_zero, neg_zero, add_zero, sgn_zero, one_mul]
  exact Strip_eq_Sig_of h0 h1 hw2 v

include h0 h1 in
theorem Shat_neck {w : ℝ} (hw : |w| ≤ 1) (v : ℝ) : Shat w₀ w v = Sig w₀ w v := by
  have := abs_le.mp hw
  have := wa_gt_one h0 h1
  exact Shat_eq_Sig_of h0 h1 (by linarith) (by linarith) v

include h0 h1 in
theorem Shat_mouth_right {w : ℝ} (hw1 : 1 ≤ w) (hwa : w ≤ wa w₀) (v : ℝ) : Shat w₀ w v = G w v := by
  have e : kk w = 0 := kk_of_mem (by linarith) (by linarith [wa_lt_two h0 h1])
  simp only [Shat, e, Int.cast_zero, mul_zero, sub_zero, sgn_zero, one_mul]
  exact Strip_eq_G_of h0 h1 hw1 hwa v

include h0 h1 in
theorem Shat_mouth_left {w : ℝ} (hwa : 4 - wa w₀ ≤ w) (hw3 : w ≤ 3) (v : ℝ) :
    Shat w₀ w v = G (w - 4) (π + v) := by
  rcases lt_or_eq_of_le hw3 with hlt | heq
  · have e : kk w = 0 := kk_of_mem (by linarith [wa_lt_two h0 h1]) hlt
    simp only [Shat, e, Int.cast_zero, mul_zero, sub_zero, sgn_zero, one_mul]
    rw [Strip_eq_GL_of h0 h1 hwa hlt.le]
    congr 1; ring
  · subst heq
    simp only [Shat, kk_three, Int.cast_one, mul_one, sgn_one, neg_one_mul]
    rw [Strip_eq_Sig_of h0 h1 (by norm_num; linarith [wa_gt_one h0 h1]),
      Sig_eq_G_of_le_neg_one h0 h1 (by norm_num)]
    congr 1; ring

include h0 h1 in
theorem Shat_tube {w : ℝ} (hw1 : 1 ≤ w) (hw3 : w ≤ 3) (v : ℝ) : Shat w₀ w v = Tube w₀ w v := by
  rcases lt_or_eq_of_le hw3 with hlt | heq
  · have e : kk w = 0 := kk_of_mem (by linarith) hlt
    simp only [Shat, e, Int.cast_zero, mul_zero, sub_zero, sgn_zero, one_mul]
    rcases lt_or_eq_of_le hw1 with hgt | heq1
    · exact Strip_eq_Tube_of h0 h1 hgt hlt v
    · subst heq1
      rw [Strip_eq_G_of h0 h1 le_rfl (wa_gt_one h0 h1).le, Tube_right h0 h1 le_rfl (wa_gt_one h0 h1).le]
  · subst heq
    rw [Shat_mouth_left h0 h1 (by linarith [wa_gt_one h0 h1]) le_rfl,
      Tube_left h0 h1 (by linarith [wa_gt_one h0 h1]) le_rfl]
    congr 1; ring

include h0 h1 in
theorem Shat_ne_wp (w v : ℝ) : Shat w₀ w v ≠ wp := by
  have hq := kk_eq_iff.mp (rfl : kk w = kk w)
  simp only [Shat]
  apply Strip_ne_wp h0 h1
  linarith [hq.2]

end Shat

/-! ### 構造体 `IsKleinSurface`（K-a〜K-e の K-a、K-b、K-c と口の条件） -/

/-- **構成 K の性質**。走者も Side も含まない。 -/
structure IsKleinSurface (w₀ : ℝ) (S X : ℝ → ℝ → V3) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p.1 p.2)
  periodic : ∀ w v, S w (v + 2 * π) = S w v
  glide : ∀ w v, S (w + 4) (-v) = S w v
  normal : ∀ w v, X w v = cross (deriv (fun v => S w v) v) (deriv (fun w => S w v) w)
  normal_cont : Continuous (fun p : ℝ × ℝ => X p.1 p.2)
  normal_ne : ∀ w v, X w v ≠ wp
  immersion : ∀ p, Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => S p.1 p.2) p)
  neck : ∀ w v, |w| ≤ 1 → S w v = Sig w₀ w v
  mouth_right : ∀ w v, 1 ≤ w → w ≤ wa w₀ → S w v = G w v
  mouth_left : ∀ w v, 4 - wa w₀ ≤ w → w ≤ 3 → S w v = G (w - 4) (π + v)
  tube : ∀ w v, 1 ≤ w → w ≤ 3 → S w v = Tube w₀ w v
  avoids : ∀ w v, S w v ≠ wp

/-- **Ŝ は構成 K の面である**。 -/
theorem Shat_isKlein {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) :
    IsKleinSurface w₀ (Shat w₀) (Xhat w₀) where
  smooth := contDiff_Shat h0 h1
  periodic := Shat_periodic w₀
  glide := Shat_glide w₀
  normal := fun _ _ => rfl
  normal_cont := continuous_Xhat h0 h1
  normal_ne := Xhat_ne h0 h1
  immersion := Shat_immersion h0 h1
  neck := fun _ v hw => Shat_neck h0 h1 hw v
  mouth_right := fun _ v hw1 hwa => Shat_mouth_right h0 h1 hw1 hwa v
  mouth_left := fun _ v hwa hw3 => Shat_mouth_left h0 h1 hwa hw3 v
  tube := fun _ v hw1 hw3 => Shat_tube h0 h1 hw1 hw3 v
  avoids := Shat_ne_wp h0 h1

/-! ### K-d：法線の降下 X̂(w + 4, −v) = −X̂(w, v) -/

section Normal

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
theorem differentiableAt_Shat (q : ℝ × ℝ) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) q :=
  (goodAt_Shat h0 h1 q).differentiableAt

include h0 h1 in
/-- **K-d**。 -/
theorem Xhat_glide (w v : ℝ) : Xhat w₀ (w + 4) (-v) = -Xhat w₀ w v := by
  have e : (fun w v => Shat w₀ (w + 4) (-1 * v)) = Shat w₀ := by
    funext w v
    rw [neg_one_mul, Shat_glide]
  have h := normalOf_affine (F := Shat w₀) (c := 4) (s := -1) (w := w) (v := v)
    (differentiableAt_Shat h0 h1 _)
  rw [e] at h
  simp only [Xhat, neg_one_mul] at h ⊢
  rw [h, neg_one_smul]
  simp

theorem normalOf_shift_v {F : ℝ → ℝ → V3} {w v a : ℝ}
    (hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (w, v + a)) :
    normalOf (fun w v => F w (v + a)) w v = normalOf F w (v + a) := by
  simp only [normalOf]
  congr 1
  have h1 := (differentiableAt_partial_v hd).hasDerivAt
  have h2 : HasDerivAt (fun x : ℝ => x + a) 1 v := (hasDerivAt_id v).add_const a
  have h3 := h1.scomp v h2
  rw [one_smul] at h3
  exact h3.deriv

include h0 h1 in
theorem Xhat_periodic (w v : ℝ) : Xhat w₀ w (v + 2 * π) = Xhat w₀ w v := by
  have e : (fun w v => Shat w₀ w (v + 2 * π)) = Shat w₀ := by
    funext w v
    rw [Shat_periodic]
  have h := normalOf_shift_v (F := Shat w₀) (w := w) (v := v) (a := 2 * π)
    (differentiableAt_Shat h0 h1 _)
  rw [e] at h
  simp only [Xhat]
  exact h.symm

include h0 h1 in
/-- 首の近傍 −wₐ < w < wₐ で X̂ = Xf。 -/
theorem Xhat_eq_Xf {w : ℝ} (hw1 : -(wa w₀) < w) (hw2 : w < wa w₀) (v : ℝ) :
    Xhat w₀ w v = Xf w₀ w v := by
  have hopen : IsOpen {p : ℝ × ℝ | -(wa w₀) < p.1 ∧ p.1 < wa w₀} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have he : (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) =ᶠ[𝓝 (w, v)] fun p => Sig w₀ p.1 p.2 := by
    filter_upwards [hopen.mem_nhds ⟨hw1, hw2⟩] with p hp
    exact Shat_eq_Sig_of h0 h1 hp.1 hp.2 p.2
  have := normalOf_congr (q := (w, v)) he
  simp only at this
  rw [Xhat, this, normalOf_Sig h0 h1]

include h0 h1 in
/-- **補題 Shat_E_fixed**：4w₀/5 < |w| ≤ 1 で −Ŝ(φ(w, v)) = Ŝ(w, v)、φ(w, v) = (−w, π − v)。 -/
theorem Shat_E_fixed {w : ℝ} (hw : w₀ * (4 / 5) < |w|) (hw1 : |w| ≤ 1) (v : ℝ) :
    -(Shat w₀ (-w) (π - v)) = Shat w₀ w v := by
  have hwn : |-w| ≤ 1 := by rwa [abs_neg]
  rw [Shat_neck h0 h1 hw1, Shat_neck h0 h1 hwn]
  rcases lt_or_ge 0 w with hpos | hneg
  · rw [abs_of_pos hpos] at hw
    rw [Sig_right h0 (w := w) hw, Sig_left h0 (w := -w) (by linarith), G_odd, neg_neg]
    congr 1
    ring
  · rw [abs_of_nonpos hneg] at hw
    rw [Sig_left h0 (w := w) (by linarith), Sig_right h0 (w := -w) (by linarith), G_odd, neg_neg]

end Normal

/-! ### K-e：Γ と両立する法線場はない（一般形）、閉路に沿った側の反転、(P1) -/

/-- **K-e（一般形）**。連続で消えない法線場 X が X(w + 4, −v) = −X(w, v) を満たせば、
X に平行で Γ と両立する連続で消えない法線場はない。Ŝ の式を使わない。 -/
theorem no_equivariant_normal {X : ℝ → ℝ → V3} (hX : Continuous (fun p : ℝ × ℝ => X p.1 p.2))
    (hne : ∀ w v, X w v ≠ wp) (hglide : ∀ w v, X (w + 4) (-v) = -X w v) :
    ¬ ∃ n : ℝ × ℝ → V3, Continuous n ∧ (∀ p, n p ≠ wp) ∧
      (∀ p, cross (n p) (X p.1 p.2) = wp) ∧
      (∀ w v, n (w + 4, -v) = n (w, v)) ∧ (∀ w v, n (w, v + 2 * π) = n (w, v)) := by
  rintro ⟨n, hn, hn0, hpar, hΩ, -⟩
  obtain ⟨c, -, hsm, hsign⟩ :=
    rigid_normal hX (fun p => hne p.1 p.2) hn hn0 dense_univ fun p _ => hpar p
  have h1 := hΩ 0 0
  have h2 := hglide 0 0
  simp only [zero_add, neg_zero] at h1 h2
  have e1 := hsm (4, 0)
  have e2 := hsm (0, 0)
  simp only at e1 e2
  rw [h1, h2, e2, smul_neg] at e1
  have e3 : (c (0, 0) + c (4, 0)) • X 0 0 = 0 := by
    rw [add_smul, e1]; simp
  rcases smul_eq_zero.mp e3 with h | h
  · rcases hsign with hp | hp
    · have := hp (0, 0); have := hp (4, 0); linarith
    · have := hp (0, 0); have := hp (4, 0); linarith
  · exact hne 0 0 h

/-- **閉路に沿った側の反転**。γ(b) = Ω⁻¹(γ(a))（すなわち γ(b) = ((γ a).1 − 4, −(γ a).2)）のとき、
X(γ) に平行な連続で消えない法線は、終点で始点の負の倍になる。 -/
theorem side_reverses_along_glide_loop {X : ℝ → ℝ → V3}
    (hX : Continuous (fun p : ℝ × ℝ => X p.1 p.2)) (hne : ∀ w v, X w v ≠ wp)
    (hglide : ∀ w v, X (w + 4) (-v) = -X w v)
    {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ) {a b : ℝ} (hend : γ b = ((γ a).1 - 4, -(γ a).2))
    {n : ℝ → V3} (hn : Continuous n) (hn0 : ∀ s, n s ≠ wp)
    (hperp : ∀ s, cross (n s) (X (γ s).1 (γ s).2) = wp) :
    ∃ κ : ℝ, 0 < κ ∧ n b = -(κ • n a) := by
  have hY : Continuous fun s => X (γ s).1 (γ s).2 := hX.comp hγ
  obtain ⟨c, -, hsm, hsign⟩ :=
    rigid_normal hY (fun s => hne _ _) hn hn0 dense_univ fun s _ => hperp s
  have hflip : X (γ b).1 (γ b).2 = -X (γ a).1 (γ a).2 := by
    have h := hglide ((γ a).1 - 4) (-(γ a).2)
    simp only [sub_add_cancel, neg_neg] at h
    rw [hend]
    simp only
    rw [h, neg_neg]
  have hpos : 0 < c b / c a := by
    rcases hsign with hp | hp
    · exact div_pos (hp b) (hp a)
    · exact div_pos_of_neg_of_neg (hp b) (hp a)
  have hca : c a ≠ 0 := by
    rcases hsign with hp | hp
    · exact (hp a).ne'
    · exact (hp a).ne
  refine ⟨c b / c a, hpos, ?_⟩
  rw [hsm b, hsm a, hflip, smul_neg, smul_smul, div_mul_cancel₀ _ hca]

/-- **(P1) 正則ホモトピーは内在的な側を変えない**。連続で消えない法線 Y に平行な連続で消えない
n について、⟨n, Y⟩ は定符号である。 -/
theorem intrinsic_side_const {Y n : ℝ → V3} (hY : Continuous Y) (hY0 : ∀ t, Y t ≠ wp)
    (hn : Continuous n) (hn0 : ∀ t, n t ≠ wp) (hpar : ∀ t, cross (n t) (Y t) = wp) :
    (∀ t, 0 < dot (n t) (Y t)) ∨ (∀ t, dot (n t) (Y t) < 0) := by
  obtain ⟨c, -, hsm, hsign⟩ := rigid_normal hY hY0 hn hn0 dense_univ fun t _ => hpar t
  have hYY : ∀ t, 0 < dot (Y t) (Y t) := fun t => nsq_pos_of_ne (hY0 t)
  rcases hsign with hp | hp
  · left
    intro t
    rw [hsm t]
    have : dot (c t • Y t) (Y t) = c t * dot (Y t) (Y t) := by
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this]
    exact mul_pos (hp t) (hYY t)
  · right
    intro t
    rw [hsm t]
    have : dot (c t • Y t) (Y t) = c t * dot (Y t) (Y t) := by
      simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
    rw [this]
    exact mul_neg_of_neg_of_pos (hp t) (hYY t)

end Zeno.Model
