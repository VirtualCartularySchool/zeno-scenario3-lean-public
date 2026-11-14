/-
# Zeno.NeckLemma : 首の補題（Smale を使わない）

面 Σ(w, v) = Rot₂(ψ(w))·(A(w), B(w)eⁱᵛ) を考える。Rot₂ は q₂ 軸まわりの回転である。
B ≠ 0、断面曲線 (A, B) が正則で、ψ が動く所では A² + B² が単調なら、Σ ははめ込みである。
半径が単調なら、切り口の円は ℘ を中心とする同心球の上を自由に動ける。
-/
import Zeno.Side
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod

noncomputable section

namespace Zeno.Model

open Real

/-- q₂ 軸まわりの回転。 -/
def rot2 (ψ : ℝ) (q : V3) : V3 :=
  (q.1 * cos ψ + q.2.2 * sin ψ, q.2.1, -(q.1 * sin ψ) + q.2.2 * cos ψ)

theorem rot2_zero (q : V3) : rot2 0 q = q := by
  simp [rot2]

/-- Rot₂(π)。 -/
theorem rot2_pi (q : V3) : rot2 π q = (-q.1, q.2.1, -q.2.2) := by
  simp [rot2]

theorem rot2_dot (ψ : ℝ) (a b : V3) : dot (rot2 ψ a) (rot2 ψ b) = dot a b := by
  have h := sin_sq_add_cos_sq ψ
  simp only [dot, rot2]
  linear_combination (a.1 * b.1 + a.2.2 * b.2.2) * h

theorem nsq_rot2 (ψ : ℝ) (q : V3) : nsq (rot2 ψ q) = nsq q := rot2_dot ψ q q

theorem rot2_cross (ψ : ℝ) (a b : V3) : cross (rot2 ψ a) (rot2 ψ b) = rot2 ψ (cross a b) := by
  have h := sin_sq_add_cos_sq ψ
  simp only [cross, rot2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; ring
  · simp only
    linear_combination (a.2.2 * b.1 - a.1 * b.2.2) * h
  · simp only; ring

theorem rot2_eq_wp {ψ : ℝ} {q : V3} (h : rot2 ψ q = wp) : q = wp := by
  by_contra hq
  have h1 := dot_self_ne hq
  rw [← rot2_dot ψ q q, h] at h1
  exact h1 (by simp [dot, wp])

/-- 同心球の上の円の族。 -/
def sigmaOf (A B ψ : ℝ → ℝ) (w v : ℝ) : V3 :=
  rot2 (ψ w) (A w, B w * cos v, B w * sin v)

/-- ∂Σ/∂v -/
def sigV (ψ B v : ℝ) : V3 := rot2 ψ (0, -(B * sin v), B * cos v)

/-- ∂Σ/∂w -/
def sigW (ψ A B dA dB dψ v : ℝ) : V3 :=
  rot2 ψ (dA + dψ * (B * sin v), dB * cos v, dB * sin v - dψ * A)

theorem hasDerivAt_sigma_v (A B ψ : ℝ → ℝ) (w v : ℝ) :
    HasDerivAt (fun v => sigmaOf A B ψ w v) (sigV (ψ w) (B w) v) v := by
  have h2 : HasDerivAt (fun v => B w * cos v) (-(B w * sin v)) v := by
    simpa using (hasDerivAt_cos v).const_mul (B w)
  have h3 : HasDerivAt (fun v => B w * sin v) (B w * cos v) v := (hasDerivAt_sin v).const_mul (B w)
  have h1 := (hasDerivAt_const v (A w * cos (ψ w))).add (h3.mul_const (sin (ψ w)))
  have h3' := (hasDerivAt_const v (-(A w * sin (ψ w)))).add (h3.mul_const (cos (ψ w)))
  refine (h1.prodMk (h2.prodMk h3')).congr_deriv ?_
  simp only [sigV, rot2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem hasDerivAt_sigma_w {A B ψ : ℝ → ℝ} {dA dB dψ w : ℝ} (hA : HasDerivAt A dA w)
    (hB : HasDerivAt B dB w) (hψ : HasDerivAt ψ dψ w) (v : ℝ) :
    HasDerivAt (fun w => sigmaOf A B ψ w v) (sigW (ψ w) (A w) (B w) dA dB dψ v) w := by
  have hc := hψ.cos
  have hs := hψ.sin
  have h1 := (hA.mul hc).add ((hB.mul_const (sin v)).mul hs)
  have h2 := hB.mul_const (cos v)
  have h3 := ((hA.mul hs).neg).add ((hB.mul_const (sin v)).mul hc)
  refine (h1.prodMk (h2.prodMk h3)).congr_deriv ?_
  simp only [sigW, rot2]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- 回転枠での外積の式。 -/
theorem cross_sig (ψ A B dA dB dψ v : ℝ) :
    cross (sigV ψ B v) (sigW ψ A B dA dB dψ v) =
      rot2 ψ (B * (A * dψ * sin v - dB),
        B * cos v * (dψ * B * sin v + dA), B * sin v * (dψ * B * sin v + dA)) := by
  have h := sin_sq_add_cos_sq v
  simp only [sigV, sigW, rot2_cross]
  congr 1
  simp only [cross]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    linear_combination (-(B * dB)) * h
  · simp only; ring
  · simp only; ring

/-- **首の補題の代数**。外積が消えるなら A A′ + B B′ = 0 で、ψ′ = 0 なら断面の速度も消える。 -/
theorem neck_core {A B dA dB dψ s c : ℝ} (hB : B ≠ 0) (hsc : s ^ 2 + c ^ 2 = 1)
    (h1 : B * (A * dψ * s - dB) = 0)
    (h2 : B * c * (dψ * B * s + dA) = 0)
    (h3 : B * s * (dψ * B * s + dA) = 0) :
    A * dA + B * dB = 0 ∧ (dψ = 0 → dA = 0 ∧ dB = 0) := by
  have hF : dψ * B * s + dA = 0 := by
    have e : B * (dψ * B * s + dA) = 0 := by
      linear_combination c * h2 + s * h3 - (dψ * B * s + dA) * B * hsc
    exact (mul_eq_zero.mp e).resolve_left hB
  have hG : A * dψ * s - dB = 0 := (mul_eq_zero.mp h1).resolve_left hB
  constructor
  · linear_combination A * hF - B * hG
  · intro h0
    subst h0
    constructor
    · linarith
    · linarith

/-- **首の補題**。B ≠ 0、(A′, B′) ≠ 0、ψ′ ≠ 0 なら A A′ + B B′ ≠ 0、のとき外積は消えない。 -/
theorem neck_lemma {ψ A B dA dB dψ : ℝ} (hB : B ≠ 0) (hprof : ¬(dA = 0 ∧ dB = 0))
    (hψ : dψ ≠ 0 → A * dA + B * dB ≠ 0) (v : ℝ) :
    cross (sigV ψ B v) (sigW ψ A B dA dB dψ v) ≠ wp := by
  intro h
  rw [cross_sig] at h
  have h0 := rot2_eq_wp h
  have h1 : B * (A * dψ * sin v - dB) = 0 := congrArg Prod.fst h0
  have h2 : B * cos v * (dψ * B * sin v + dA) = 0 := congrArg (fun z : V3 => z.2.1) h0
  have h3 : B * sin v * (dψ * B * sin v + dA) = 0 := congrArg (fun z : V3 => z.2.2) h0
  obtain ⟨hr, hz⟩ := neck_core hB (sin_sq_add_cos_sq v) h1 h2 h3
  by_cases hd : dψ = 0
  · exact hprof (hz hd)
  · exact hψ hd hr

end Zeno.Model
