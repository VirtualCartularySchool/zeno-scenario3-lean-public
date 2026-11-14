/-
# Zeno.Charts : 命題 D（反転を選ぶもの）

同じ助変数 (w, v) のホーン H(1/w, v) は、w = 0 を越えて二通りに解析的につながる。
共形チャート（反転 ι、S³ の無限遠点）では連続な法線の Φ ラベルが右岸と左岸で逆になる。
射影チャート（π、ℝP³ の無限遠点）では同じラベルのままである。
したがってホーンの対と助変数だけでは表裏の法則は決まらない。
シナリオ3（L1025）とシナリオ2（L1024）の違いはこの選択である。
-/
import Zeno.Ideal

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology

/-- 射影チャート π(p) = (1/p₁, p₂/p₁, p₃/p₁)。 -/
def proj (p : V3) : V3 := (1 / p.1, p.2.1 / p.1, p.2.2 / p.1)

/-- 射影チャートの像 P(w, v) = (w, w²eⁱᵛ)。 -/
def Pch (w v : ℝ) : V3 := (w, w ^ 2 * cos v, w ^ 2 * sin v)

/-- ∂P/∂w -/
def PTw (w v : ℝ) : V3 := (1, 2 * w * cos v, 2 * w * sin v)

/-- ∂P/∂v -/
def PTv (w v : ℝ) : V3 := (0, -(w ^ 2 * sin v), w ^ 2 * cos v)

/-- 射影チャートの連続な法線 Nₚ = (−2w, eⁱᵛ)。 -/
def Np (w v : ℝ) : V3 := (-(2 * w), cos v, sin v)

/-- ホーンの外側の関数：正がホーンの外側。 -/
def hornOuter (p : V3) : ℝ := p.1 ^ 2 * (p.2.1 ^ 2 + p.2.2 ^ 2) - 1

/-- 射影チャートの基準 Ψ(q) = |ζ|² − q₁⁴。 -/
def Psi (q : V3) : ℝ := q.2.1 ^ 2 + q.2.2 ^ 2 - q.1 ^ 4

/-- Ψ の勾配 -/
def gradPsi (q : V3) : V3 := (-(4 * q.1 ^ 3), 2 * q.2.1, 2 * q.2.2)

/-- 射影チャートのラベル。 -/
def sideP (q n : V3) : ℝ := dot (gradPsi q) n

theorem inv3_H {w : ℝ} (hw : w ≠ 0) (v : ℝ) : inv3 (H (1 / w) v) = G w v := by
  have hc := sin_sq_add_cos_sq v
  have hn : nsq (H (1 / w) v) = D w / w ^ 2 := by
    simp only [nsq, dot, H, D]
    field_simp
    linear_combination (w ^ 4) * hc
  have hD := D_ne w
  unfold inv3
  rw [hn]
  simp only [H, G]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> · simp only; field_simp

theorem proj_H {w : ℝ} (hw : w ≠ 0) (v : ℝ) : proj (H (1 / w) v) = Pch w v := by
  simp only [proj, H, Pch]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> · simp only; field_simp

/-- 二つの基準は、どちらもホーンの外側を読む。 -/
theorem Phi_inv3 {p : V3} (hp : nsq p ≠ 0) : Phi (inv3 p) = hornOuter p / nsq p ^ 4 := by
  have e : nsq (inv3 p) = 1 / nsq p := by
    simp only [nsq, dot, inv3] at hp ⊢
    field_simp
  unfold Phi
  rw [e]
  simp only [inv3, hornOuter]
  field_simp

theorem Psi_proj {p : V3} (hp : p.1 ≠ 0) : Psi (proj p) = hornOuter p / p.1 ^ 4 := by
  simp only [Psi, proj, hornOuter]
  field_simp

theorem hasDerivAt_Pch_w (w v : ℝ) : HasDerivAt (fun w => Pch w v) (PTw w v) w := by
  have h2 : HasDerivAt (fun w : ℝ => w ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
  exact (hasDerivAt_id' w).prodMk ((h2.mul_const (cos v)).prodMk (h2.mul_const (sin v)))

theorem hasDerivAt_Pch_v (w v : ℝ) : HasDerivAt (fun v => Pch w v) (PTv w v) v := by
  have h1 : HasDerivAt (fun v : ℝ => w ^ 2 * cos v) (-(w ^ 2 * sin v)) v := by
    have := (hasDerivAt_cos v).const_mul (w ^ 2)
    simpa using this
  exact (hasDerivAt_const v w).prodMk (h1.prodMk ((hasDerivAt_sin v).const_mul (w ^ 2)))

theorem cross_PTv_PTw (w v : ℝ) : cross (PTv w v) (PTw w v) = (w ^ 2) • Np w v := by
  have hc := sin_sq_add_cos_sq v
  simp only [cross, PTv, PTw, Np]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.smul_fst, smul_eq_mul]
    linear_combination (-(2 * w ^ 3)) * hc
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  · simp only [Prod.smul_snd, smul_eq_mul]; ring

theorem Np_ne_zero (w v : ℝ) : Np w v ≠ wp := by
  intro h
  have h1 : cos v = 0 := congrArg (fun z : V3 => z.2.1) h
  have h2 : sin v = 0 := congrArg (fun z : V3 => z.2.2) h
  have hc := sin_sq_add_cos_sq v
  rw [h1, h2] at hc
  norm_num at hc

theorem sideP_Pch (w v : ℝ) : sideP (Pch w v) (Np w v) = 2 * w ^ 2 * (1 + 4 * w ^ 2) := by
  have hc := sin_sq_add_cos_sq v
  simp only [sideP, dot, gradPsi, Pch, Np]
  linear_combination (2 * w ^ 2) * hc

/-- 射影チャートの余向き。 -/
structure IsCoorientationP (n : ℝ × ℝ → V3) : Prop where
  cont : Continuous n
  ne : ∀ p, n p ≠ wp
  perp : ∀ p, p.1 ≠ 0 → dot (n p) (PTv p.1 p.2) = 0 ∧ dot (n p) (PTw p.1 p.2) = 0

theorem continuous_Np : Continuous fun p : ℝ × ℝ => Np p.1 p.2 := by
  unfold Np; fun_prop

theorem side_mul_P_of_rigid {α : Type*} {n N₀ : α → V3} {c : α → ℝ}
    (hsm : ∀ p, n p = c p • N₀ p) (hc : (∀ p, 0 < c p) ∨ (∀ p, c p < 0))
    {q₁ q₂ : V3} {p₁ p₂ : α} (h : 0 < sideP q₁ (N₀ p₁) * sideP q₂ (N₀ p₂)) :
    0 < sideP q₁ (n p₁) * sideP q₂ (n p₂) := by
  have e : sideP q₁ (n p₁) * sideP q₂ (n p₂) =
      (c p₁ * c p₂) * (sideP q₁ (N₀ p₁) * sideP q₂ (N₀ p₂)) := by
    rw [hsm p₁, hsm p₂]
    simp only [sideP, dot_smul_right]
    ring
  have hpos : 0 < c p₁ * c p₂ := by
    rcases hc with h | h
    · exact mul_pos (h _) (h _)
    · exact mul_pos_of_neg_of_neg (h _) (h _)
  rw [e]
  exact mul_pos hpos h

/-- 射影チャートでは、どの連続な余向きでもラベルは両岸で同じである。 -/
theorem projective_no_reversal {n : ℝ × ℝ → V3} (hn : IsCoorientationP n) {w₁ w₂ : ℝ} (h₁ : w₁ ≠ 0)
    (h₂ : w₂ ≠ 0) (v₁ v₂ : ℝ) :
    0 < sideP (Pch w₁ v₁) (n (w₁, v₁)) * sideP (Pch w₂ v₂) (n (w₂, v₂)) := by
  obtain ⟨c, -, hsm, hs⟩ : ∃ c : ℝ × ℝ → ℝ, Continuous c ∧ (∀ p, n p = c p • Np p.1 p.2) ∧
      ((∀ p, 0 < c p) ∨ (∀ p, c p < 0)) := by
    refine rigid_normal continuous_Np (fun p => Np_ne_zero p.1 p.2) hn.cont hn.ne
      dense_w_ne_zero ?_
    intro p hp
    obtain ⟨h1, h2⟩ := hn.perp p hp
    have h := cross_of_perp h1 h2
    rw [cross_PTv_PTw, cross_smul_right] at h
    have hc : p.1 ^ 2 ≠ 0 := pow_ne_zero 2 hp
    have h' := congrArg (fun z : V3 => (p.1 ^ 2)⁻¹ • z) h
    simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
    rw [h']
    simp [wp]
  refine side_mul_P_of_rigid (α := ℝ × ℝ) (n := n) (N₀ := fun p => Np p.1 p.2) (c := c) hsm hs
    (q₁ := Pch w₁ v₁) (q₂ := Pch w₂ v₂) (p₁ := (w₁, v₁)) (p₂ := (w₂, v₂)) ?_
  simp only [sideP_Pch]
  have a1 : 0 < w₁ ^ 2 := by positivity
  have a2 : 0 < w₂ ^ 2 := by positivity
  have b1 : 0 < 2 * w₁ ^ 2 * (1 + 4 * w₁ ^ 2) := mul_pos (by linarith) (by linarith)
  have b2 : 0 < 2 * w₂ ^ 2 * (1 + 4 * w₂ ^ 2) := mul_pos (by linarith) (by linarith)
  exact mul_pos b1 b2

theorem Pch_mirror (w v : ℝ) : Pch (-w) v = mirror (Pch w v) := by
  simp [Pch, mirror]

theorem Np_mirror (w v : ℝ) : Np (-w) v = mirror (Np w v) := by
  simp [Np, mirror]

/-- **命題 D**：同じ助変数のホーンの、二つの解析的な継続。 -/
structure ChartDichotomy : Prop where
  /-- 同じホーンの点が二つのチャートへ写る。 -/
  same_horn : ∀ w v, w ≠ 0 → inv3 (H (1 / w) v) = G w v ∧ proj (H (1 / w) v) = Pch w v
  /-- どちらのチャートの基準も、ホーンの外側を読む。 -/
  same_reference : ∀ p : V3, p.1 ≠ 0 →
    (0 < Phi (inv3 p) ↔ 0 < hornOuter p) ∧ (0 < Psi (proj p) ↔ 0 < hornOuter p)
  /-- どちらのチャートでも w = 0 を越えて滑らかである。 -/
  smooth_conformal : ContDiff ℝ ⊤ fun p : ℝ × ℝ => G p.1 p.2
  smooth_projective : ContDiff ℝ ⊤ fun p : ℝ × ℝ => Pch p.1 p.2
  /-- 共形チャート：どの連続な余向きでもラベルは逆になる。通過則は E。 -/
  conformal_reverses : ∀ n, IsCoorientation n → ∀ w₁ w₂ v₁ v₂, 0 < w₁ → w₂ < 0 →
    side (G w₁ v₁) (n (w₁, v₁)) * side (G w₂ v₂) (n (w₂, v₂)) < 0
  conformal_law : ∀ w v, (G (-w) v, N (-w) v) = Everse (G w v, N w v)
  conformal_cross : ∀ w v, cross (Tv w v) (Tw w v) = (w ^ 3 / D w ^ 3) • N w v
  /-- 射影チャート：どの連続な余向きでもラベルは同じ。通過則は鏡映。 -/
  projective_keeps : ∀ n, IsCoorientationP n → ∀ w₁ w₂ v₁ v₂, 0 < w₁ → w₂ < 0 →
    0 < sideP (Pch w₁ v₁) (n (w₁, v₁)) * sideP (Pch w₂ v₂) (n (w₂, v₂))
  projective_law : ∀ w v, Pch (-w) v = mirror (Pch w v) ∧ Np (-w) v = mirror (Np w v)
  projective_tangents : ∀ w v,
    HasDerivAt (fun w => Pch w v) (PTw w v) w ∧ HasDerivAt (fun v => Pch w v) (PTv w v) v
  projective_cross : ∀ w v, cross (PTv w v) (PTw w v) = (w ^ 2) • Np w v

theorem contDiff_G : ContDiff ℝ ⊤ fun p : ℝ × ℝ => G p.1 p.2 := by
  have hD : ContDiff ℝ ⊤ fun p : ℝ × ℝ => D p.1 := by
    unfold D; fun_prop
  have hne : ∀ p : ℝ × ℝ, D p.1 ≠ 0 := fun p => D_ne _
  have h1 : ContDiff ℝ ⊤ fun p : ℝ × ℝ => p.1 := contDiff_fst
  have h2 : ContDiff ℝ ⊤ fun p : ℝ × ℝ => p.2 := contDiff_snd
  refine (h1.div hD hne).prodMk ?_
  refine ContDiff.prodMk ?_ ?_
  · exact ((h1.pow 3).mul (Real.contDiff_cos.comp h2)).div hD hne
  · exact ((h1.pow 3).mul (Real.contDiff_sin.comp h2)).div hD hne

theorem chart_dichotomy : ChartDichotomy where
  same_horn := fun w v hw => ⟨inv3_H hw v, proj_H hw v⟩
  same_reference := by
    intro p hp
    have hn : 0 < nsq p := by
      simp only [nsq, dot]
      have h1 : 0 < p.1 * p.1 := mul_self_pos.mpr hp
      nlinarith [mul_self_nonneg p.2.1, mul_self_nonneg p.2.2]
    constructor
    · rw [Phi_inv3 hn.ne']
      have : 0 < nsq p ^ 4 := by positivity
      exact div_pos_iff_of_pos_right this
    · rw [Psi_proj hp]
      have : 0 < p.1 ^ 4 := by positivity
      exact div_pos_iff_of_pos_right this
  smooth_conformal := contDiff_G
  smooth_projective := by
    have h1 : ContDiff ℝ ⊤ fun p : ℝ × ℝ => p.1 := contDiff_fst
    have h2 : ContDiff ℝ ⊤ fun p : ℝ × ℝ => p.2 := contDiff_snd
    refine h1.prodMk (ContDiff.prodMk ?_ ?_)
    · exact (h1.pow 2).mul (Real.contDiff_cos.comp h2)
    · exact (h1.pow 2).mul (Real.contDiff_sin.comp h2)
  conformal_reverses := fun n hn w₁ w₂ v₁ v₂ h₁ h₂ => ideal_reversal hn h₁ h₂ v₁ v₂
  conformal_law := fun w v => by simp only [Everse, G_odd, N_even]
  conformal_cross := cross_Tv_Tw_smul
  projective_keeps := fun n hn w₁ w₂ v₁ v₂ h₁ h₂ =>
    projective_no_reversal hn h₁.ne' h₂.ne v₁ v₂
  projective_law := fun w v => ⟨Pch_mirror w v, Np_mirror w v⟩
  projective_tangents := fun w v => ⟨hasDerivAt_Pch_w w v, hasDerivAt_Pch_v w v⟩
  projective_cross := cross_PTv_PTw

end Zeno.Model
