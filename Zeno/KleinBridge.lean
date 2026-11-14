/-
# Zeno.KleinBridge : 定理 K2（橋：二つの貼り合わせ）

同じ管 Tube の左の口の式 G(w − 4, v + π) は、二つの左岸の式に等しい。
- Σ の左岸（`Sig_left`）：貼り合わせは Ω(w, v) = (w + 4, −v)。これが Ŝ であり、一側（K-d、K-e）かつ M1。
- 𝒯 の左岸（`Tub_left`）：貼り合わせは τ(w, v) = (w + 4, v)。これが Ŝ_T であり、二側かつ M1 は不成立。

「一側」「二側」は、Γ（または Γ′ = ⟨T, τ⟩）と両立する連続で消えない法線場の非存在・存在として定義する。
-/
import Zeno.Klein

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

/-- 𝒯 閉包の帯：半回転のない管 Tub、外側の管 Tube、左の Tub(w − 4, v)。 -/
def StripT (w₀ w v : ℝ) : V3 :=
  if w ≤ c1 w₀ then Tub w₀ w v else if w ≤ c2 w₀ then Tube w₀ w v else Tub w₀ (w - 4) v

/-- 𝒯 閉包の面 Ŝ_T(w, v) = StripT(w − 4k, v)。 -/
def ShatT (w₀ w v : ℝ) : V3 := StripT w₀ (w - 4 * (kk w : ℝ)) v

/-- Ŝ_T の法線場。 -/
def XhatT (w₀ : ℝ) : ℝ → ℝ → V3 := normalOf (ShatT w₀)

section Bridge

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
theorem normalOf_Tub (w v : ℝ) : normalOf (Tub w₀) w v = XT w₀ w v :=
  ((Tub_isTubeSurface h0 h1).normal w v).symm

include h0 h1 in
theorem goodAt_Tub (q : ℝ × ℝ) : GoodAt (Tub w₀) q where
  smooth := (contDiff_Tub h0.ne').contDiffAt
  ne := by rw [normalOf_Tub h0 h1]; exact XT_ne h0 h1 _ _
  cont := by
    have e : (fun p : ℝ × ℝ => normalOf (Tub w₀) p.1 p.2) = fun p => XT w₀ p.1 p.2 :=
      funext fun p => normalOf_Tub h0 h1 p.1 p.2
    rw [e]; exact (continuous_XT h0.ne').continuousAt

include h0 h1 in
theorem Tub_eq_G_of_ge_one {w : ℝ} (hw : 1 ≤ w) (v : ℝ) : Tub w₀ w v = G w v :=
  Tub_right h0 (by nlinarith) v

include h0 h1 in
theorem Tub_eq_G_of_le_neg_one {w : ℝ} (hw : w ≤ -1) (v : ℝ) : Tub w₀ w v = G w (v + π) := by
  have : w₀ * (4 / 5) < 1 := by nlinarith
  exact Tub_left h0 (by linarith) v

include h0 h1 in
theorem StripT_eq_Tub_of {w : ℝ} (hw : w < wa w₀) (v : ℝ) : StripT w₀ w v = Tub w₀ w v := by
  simp only [StripT]
  split_ifs with hc1 hc2
  · rfl
  · push Not at hc1
    have h1' : 1 ≤ w := by linarith [c1_gt_one h0 h1]
    rw [Tube_right h0 h1 h1' hw.le, Tub_eq_G_of_ge_one h0 h1 h1']
  · exfalso; push Not at hc2; linarith [wa_lt_c2 h0 h1]

include h0 h1 in
theorem StripT_eq_Tube_of {w : ℝ} (hw1 : 1 < w) (hw3 : w < 3) (v : ℝ) :
    StripT w₀ w v = Tube w₀ w v := by
  simp only [StripT]
  split_ifs with hc1 hc2
  · rw [Tub_eq_G_of_ge_one h0 h1 hw1.le, Tube_right h0 h1 hw1.le (by linarith [c1_lt_wa h0 h1])]
  · rfl
  · push Not at hc2
    rw [Tub_eq_G_of_le_neg_one h0 h1 (by linarith),
      Tube_left h0 h1 (by linarith [c2_gt h0 h1]) hw3.le]

include h0 h1 in
theorem StripT_eq_TubL_of {w : ℝ} (hwa : 4 - wa w₀ < w) (v : ℝ) :
    StripT w₀ w v = Tub w₀ (w - 4) v := by
  simp only [StripT]
  split_ifs with hc1 hc2
  · exfalso; linarith [c1_lt_four_sub_wa h0 h1]
  · rw [Tube_left h0 h1 hwa.le (by linarith [c2_lt_three h0 h1]),
      Tub_eq_G_of_le_neg_one h0 h1 (by linarith [c2_lt_three h0 h1])]
  · rfl

theorem StripT_periodic (w₀ w v : ℝ) : StripT w₀ w (v + 2 * π) = StripT w₀ w v := by
  simp only [StripT]
  split_ifs
  · exact Tub_periodic _ _ _
  · exact Tube_periodic _ _ _
  · exact Tub_periodic _ _ _

include h0 h1 in
theorem goodAt_StripT (q : ℝ × ℝ) : GoodAt (StripT w₀) q := by
  obtain ⟨w, v⟩ := q
  by_cases hA : w < wa w₀
  · refine (goodAt_Tub h0 h1 (w, v)).congr ?_
    have hopen : IsOpen {p : ℝ × ℝ | p.1 < wa w₀} := isOpen_lt continuous_fst continuous_const
    filter_upwards [hopen.mem_nhds hA] with p hp
    exact StripT_eq_Tub_of h0 h1 hp p.2
  · push Not at hA
    by_cases hB : w < 3
    · have hw1 : 1 < w := by linarith [wa_gt_one h0 h1]
      refine (goodAt_Tube h0 h1 hw1 hB).congr ?_
      have hopen : IsOpen {p : ℝ × ℝ | 1 < p.1 ∧ p.1 < 3} :=
        (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
      filter_upwards [hopen.mem_nhds ⟨hw1, hB⟩] with p hp
      exact StripT_eq_Tube_of h0 h1 hp.1 hp.2 p.2
    · push Not at hB
      have hg : GoodAt (fun w v => Tub w₀ (w + -4) (1 * v)) (w, v) :=
        (goodAt_Tub h0 h1 (w + -4, 1 * v)).affine (Or.inl rfl)
      refine hg.congr ?_
      have hopen : IsOpen {p : ℝ × ℝ | 4 - wa w₀ < p.1} := isOpen_lt continuous_const continuous_fst
      have hmem : (w, v) ∈ {p : ℝ × ℝ | 4 - wa w₀ < p.1} := by
        show 4 - wa w₀ < w
        linarith [wa_gt_one h0 h1]
      filter_upwards [hopen.mem_nhds hmem] with p hp
      rw [StripT_eq_TubL_of h0 h1 hp]
      simp only [sub_eq_add_neg, one_mul]

theorem ShatT_translation (w₀ w v : ℝ) : ShatT w₀ (w + 4) v = ShatT w₀ w v := by
  simp only [ShatT, kk_add_four]
  congr 1
  push_cast; ring

theorem ShatT_periodic (w₀ w v : ℝ) : ShatT w₀ w (v + 2 * π) = ShatT w₀ w v := by
  simp only [ShatT, StripT_periodic]

include h0 h1 in
theorem ShatT_eq_strip_of {k : ℤ} {w : ℝ} (hw1 : 4 * (k : ℝ) - wa w₀ < w) (hw2 : w < 4 * k + 3)
    (v : ℝ) : ShatT w₀ w v = StripT w₀ (w + -(4 * (k : ℝ))) (1 * v) := by
  rw [one_mul]
  by_cases hk : 4 * (k : ℝ) - 1 ≤ w
  · have e : kk w = k := kk_eq_iff.mpr ⟨hk, hw2⟩
    simp only [ShatT, e, sub_eq_add_neg]
  · push Not at hk
    have e : kk w = k - 1 := by
      rw [kk_eq_iff]
      push_cast
      constructor <;> linarith [wa_lt_two h0 h1]
    simp only [ShatT, e]
    have hgt : 4 - wa w₀ < w - 4 * ((k - 1 : ℤ) : ℝ) := by push_cast; linarith
    rw [StripT_eq_TubL_of h0 h1 hgt, StripT_eq_Tub_of h0 h1 (by linarith [wa_gt_one h0 h1])]
    congr 1
    push_cast; ring

include h0 h1 in
theorem ShatT_eventually (q : ℝ × ℝ) :
    (fun p : ℝ × ℝ => ShatT w₀ p.1 p.2) =ᶠ[𝓝 q]
      fun p => StripT w₀ (p.1 + -(4 * (kk q.1 : ℝ))) (1 * p.2) := by
  set k := kk q.1 with hk
  have hq := kk_eq_iff.mp hk.symm
  have hopen : IsOpen {p : ℝ × ℝ | 4 * (k : ℝ) - wa w₀ < p.1 ∧ p.1 < 4 * k + 3} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hmem : q ∈ {p : ℝ × ℝ | 4 * (k : ℝ) - wa w₀ < p.1 ∧ p.1 < 4 * k + 3} :=
    ⟨by linarith [hq.1, wa_gt_one h0 h1], hq.2⟩
  filter_upwards [hopen.mem_nhds hmem] with p hp
  exact ShatT_eq_strip_of h0 h1 hp.1 hp.2 p.2

include h0 h1 in
theorem goodAt_ShatT (q : ℝ × ℝ) : GoodAt (ShatT w₀) q := by
  have hg : GoodAt (fun w v => StripT w₀ (w + -(4 * (kk q.1 : ℝ))) (1 * v)) q :=
    (goodAt_StripT h0 h1 _).affine (Or.inl rfl)
  exact hg.congr (ShatT_eventually h0 h1 q)

include h0 h1 in
theorem contDiff_ShatT : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ShatT w₀ p.1 p.2) :=
  contDiff_iff_contDiffAt.mpr fun q => (goodAt_ShatT h0 h1 q).smooth

include h0 h1 in
theorem ShatT_immersion (q : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => ShatT w₀ p.1 p.2) q) :=
  (goodAt_ShatT h0 h1 q).immersion

include h0 h1 in
theorem XhatT_ne (w v : ℝ) : XhatT w₀ w v ≠ wp := (goodAt_ShatT h0 h1 (w, v)).ne

include h0 h1 in
theorem continuous_XhatT : Continuous (fun p : ℝ × ℝ => XhatT w₀ p.1 p.2) :=
  continuous_iff_continuousAt.mpr fun q => (goodAt_ShatT h0 h1 q).cont

include h0 h1 in
/-- τ での法線の不変性 X̂_T(w + 4, v) = X̂_T(w, v)（符号は出ない）。 -/
theorem XhatT_translation (w v : ℝ) : XhatT w₀ (w + 4) v = XhatT w₀ w v := by
  have e : (fun w v => ShatT w₀ (w + 4) (1 * v)) = ShatT w₀ := by
    funext w v
    rw [one_mul, ShatT_translation]
  have h := normalOf_affine (F := ShatT w₀) (c := 4) (s := 1) (w := w) (v := v)
    ((goodAt_ShatT h0 h1 _).differentiableAt)
  rw [e] at h
  simp only [XhatT, one_mul, one_smul] at h ⊢
  exact h.symm

include h0 h1 in
theorem XhatT_periodic (w v : ℝ) : XhatT w₀ w (v + 2 * π) = XhatT w₀ w v := by
  have e : (fun w v => ShatT w₀ w (v + 2 * π)) = ShatT w₀ := by
    funext w v
    rw [ShatT_periodic]
  have h := normalOf_shift_v (F := ShatT w₀) (w := w) (v := v) (a := 2 * π)
    ((goodAt_ShatT h0 h1 _).differentiableAt)
  rw [e] at h
  simp only [XhatT]
  exact h.symm

theorem cross_self (a : V3) : cross a a = wp := by
  simp only [cross, wp]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

include h0 h1 in
/-- **K2（𝒯 閉包の二側性）**：Γ′ = ⟨T, τ⟩ と両立する連続で消えない法線場がある（X̂_T 自身）。 -/
theorem ShatT_two_sided : ∃ n : ℝ × ℝ → V3, Continuous n ∧ (∀ p, n p ≠ wp) ∧
    (∀ p, cross (n p) (XhatT w₀ p.1 p.2) = wp) ∧
    (∀ w v, n (w + 4, v) = n (w, v)) ∧ (∀ w v, n (w, v + 2 * π) = n (w, v)) :=
  ⟨fun p => XhatT w₀ p.1 p.2, continuous_XhatT h0 h1, fun p => XhatT_ne h0 h1 p.1 p.2,
    fun _ => cross_self _, fun w v => XhatT_translation h0 h1 w v,
    fun w v => XhatT_periodic h0 h1 w v⟩

include h0 h1 in
theorem ShatT_eq_Tub_of {w : ℝ} (hw1 : -(wa w₀) < w) (hw2 : w < wa w₀) (v : ℝ) :
    ShatT w₀ w v = Tub w₀ w v := by
  rw [ShatT_eq_strip_of h0 h1 (k := 0) (by push_cast; linarith)
    (by push_cast; linarith [wa_lt_two h0 h1])]
  simp only [Int.cast_zero, mul_zero, neg_zero, add_zero, one_mul]
  exact StripT_eq_Tub_of h0 h1 hw2 v

include h0 h1 in
theorem XhatT_eq_XT {w : ℝ} (hw1 : -(wa w₀) < w) (hw2 : w < wa w₀) (v : ℝ) :
    XhatT w₀ w v = XT w₀ w v := by
  have hopen : IsOpen {p : ℝ × ℝ | -(wa w₀) < p.1 ∧ p.1 < wa w₀} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have he : (fun p : ℝ × ℝ => ShatT w₀ p.1 p.2) =ᶠ[𝓝 (w, v)] fun p => Tub w₀ p.1 p.2 := by
    filter_upwards [hopen.mem_nhds ⟨hw1, hw2⟩] with p hp
    exact ShatT_eq_Tub_of h0 h1 hp.1 hp.2 p.2
  have := normalOf_congr (q := (w, v)) he
  simp only at this
  rw [XhatT, this, normalOf_Tub h0 h1]

include h0 h1 in
/-- **K2（𝒯 閉包で M1 は不成立）**：どの連続な法線場でも両岸のラベルは同じである。
`tube_no_reversal` を Tub の法線場 XT に適用し、剛性で n に移す。 -/
theorem ShatT_no_reversal {n : ℝ × ℝ → V3} (hn : IsNormalField (ShatT w₀) n) {w₁ w₂ : ℝ}
    (h₁ : w₀ < w₁) (h₁' : w₁ ≤ 1) (h₂ : -1 ≤ w₂) (h₂' : w₂ < -w₀) (v₁ v₂ : ℝ) :
    0 < side (ShatT w₀ w₁ v₁) (n (w₁, v₁)) * side (ShatT w₀ w₂ v₂) (n (w₂, v₂)) := by
  have hwa := wa_gt_one h0 h1
  obtain ⟨c', -, hsm, hs⟩ := normal_rigid (continuous_XhatT h0 h1) (XhatT_ne h0 h1)
    (fun _ _ => rfl) hn
  have hh := (side_mul_of_rigid (α := ℝ × ℝ) (n := n) (N₀ := fun p => XhatT w₀ p.1 p.2) (c := c')
    hsm hs (q₁ := ShatT w₀ w₁ v₁) (q₂ := ShatT w₀ w₂ v₂) (p₁ := (w₁, v₁)) (p₂ := (w₂, v₂))).2
  refine hh ?_
  simp only
  rw [ShatT_eq_Tub_of h0 h1 (by linarith) (by linarith), ShatT_eq_Tub_of h0 h1 (by linarith) (by linarith),
    XhatT_eq_XT h0 h1 (by linarith) (by linarith), XhatT_eq_XT h0 h1 (by linarith) (by linarith)]
  exact tube_no_reversal h0 (Tub_isTubeSurface h0 h1) (Tub_isTubeSurface h0 h1).isNormalField
    h₁ h₂' v₁ v₂

end Bridge

end Zeno.Model
