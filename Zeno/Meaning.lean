/-
# Zeno.Meaning : 表裏の位置としての意味と、理想形の一致の強制

1. `side`、`sideP` は基準 Φ、Ψ の方向微分である。したがって Front の側へ少しずらした点は
   ホーンの外（Φ > 0）に、Back の側へずらした点は内（Φ < 0）にある。
2. ゼノンの段階が無限に続き、二人が極限の時刻で連続なら、その時刻に二人は同じ点にいる。
   理想形 A の t∗ での一致はこの定理から強制される。正則形 B、C が段階を有限個に保つのはこのためである。

どちらも既存の定理の文を変えない。
-/
import Zeno.Charts
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology

/-- ε ↦ q + εn の座標の導関数。 -/
theorem hasDerivAt_line_coord (a b : ℝ) : HasDerivAt (fun ε : ℝ => a + ε * b) b 0 := by
  simpa using ((hasDerivAt_id' (0 : ℝ)).mul_const b).const_add a

/-- **`side` は Φ の方向微分である**（`gradPhi` は Φ の勾配）。 -/
theorem hasDerivAt_Phi_line (q n : V3) :
    HasDerivAt (fun ε : ℝ => Phi (q + ε • n)) (side q n) 0 := by
  have ha := hasDerivAt_line_coord q.1 n.1
  have hb := hasDerivAt_line_coord q.2.1 n.2.1
  have hc := hasDerivAt_line_coord q.2.2 n.2.2
  have hS := ((ha.pow 2).add (hb.pow 2)).add (hc.pow 2)
  have h := ((ha.pow 2).mul ((hb.pow 2).add (hc.pow 2))).sub (hS.pow 4)
  have e : (fun ε : ℝ => Phi (q + ε • n)) = fun ε =>
      (q.1 + ε * n.1) ^ 2 * ((q.2.1 + ε * n.2.1) ^ 2 + (q.2.2 + ε * n.2.2) ^ 2) -
        ((q.1 + ε * n.1) ^ 2 + (q.2.1 + ε * n.2.1) ^ 2 + (q.2.2 + ε * n.2.2) ^ 2) ^ 4 := by
    funext ε
    simp only [Phi, nsq, dot, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  rw [e]
  refine h.congr_deriv ?_
  simp only [side, gradPhi, nsq, dot, Pi.add_apply, Pi.pow_apply, zero_mul, add_zero]
  push_cast
  ring

/-- 値 0 から正の傾きで出る関数は、右側ですぐ正になる。 -/
theorem eventually_pos_of_hasDerivAt {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0) (h0 : f 0 = 0)
    (hd : 0 < d) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < f ε := by
  have h := hf.tendsto_slope_zero_right
  filter_upwards [h.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with ε hε hpos
  have hp : 0 < ε := hpos
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hε
  have := mul_pos hp hε
  rwa [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] at this

/-- **表の意味**：基準の零点 q で Front なら、法線の側へ少しずらした点はホーンの外（Φ > 0）にある。 -/
theorem front_outside {q n : V3} (h0 : Phi q = 0) (h : Front q n) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < Phi (q + ε • n) :=
  eventually_pos_of_hasDerivAt (hasDerivAt_Phi_line q n) (by simpa using h0) h

/-- **裏の意味**：基準の零点 q で Back なら、法線の側へ少しずらした点はホーンの内（Φ < 0）にある。 -/
theorem back_inside {q n : V3} (h0 : Phi q = 0) (h : Back q n) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), Phi (q + ε • n) < 0 := by
  have h1 := eventually_pos_of_hasDerivAt (hasDerivAt_Phi_line q n).neg
    (by simp [h0]) (by have := h; simp only [Back] at this; linarith)
  filter_upwards [h1] with ε hε
  simp only [Pi.neg_apply] at hε
  linarith

/-- Ψ は射影チャートの面の上で 0 である。 -/
theorem Psi_Pch (w v : ℝ) : Psi (Pch w v) = 0 := by
  have h := sin_sq_add_cos_sq v
  simp only [Psi, Pch]
  linear_combination (w ^ 4) * h

/-- **`sideP` は Ψ の方向微分である**（`gradPsi` は Ψ の勾配）。 -/
theorem hasDerivAt_Psi_line (q n : V3) :
    HasDerivAt (fun ε : ℝ => Psi (q + ε • n)) (sideP q n) 0 := by
  have ha := hasDerivAt_line_coord q.1 n.1
  have hb := hasDerivAt_line_coord q.2.1 n.2.1
  have hc := hasDerivAt_line_coord q.2.2 n.2.2
  have h := ((hb.pow 2).add (hc.pow 2)).sub (ha.pow 4)
  have e : (fun ε : ℝ => Psi (q + ε • n)) = fun ε =>
      (q.2.1 + ε * n.2.1) ^ 2 + (q.2.2 + ε * n.2.2) ^ 2 - (q.1 + ε * n.1) ^ 4 := by
    funext ε
    simp only [Psi, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rw [e]
  refine h.congr_deriv ?_
  simp only [sideP, gradPsi, dot, zero_mul, add_zero]
  push_cast
  ring

/-- **ゼノンの一致の強制**：異時刻の一致 A(τₖ₊₁) = T(τₖ) が無限に続き、τₖ → t₀ で、
二人が t₀ で連続なら、t₀ に二人は同じ点にいる。どんなハウスドルフ空間でも成り立つ。 -/
theorem zeno_steps_force_coincidence {X : Type*} [TopologicalSpace X] [T2Space X]
    {T A : ℝ → X} {τ : ℕ → ℝ} {t₀ : ℝ} (hτ : Tendsto τ atTop (𝓝 t₀))
    (hstep : ∀ k, A (τ (k + 1)) = T (τ k)) (hT : ContinuousAt T t₀) (hA : ContinuousAt A t₀) :
    T t₀ = A t₀ := by
  have h1 : Tendsto (fun k => T (τ k)) atTop (𝓝 (T t₀)) := hT.tendsto.comp hτ
  have h2 : Tendsto (fun k => A (τ (k + 1))) atTop (𝓝 (A t₀)) :=
    hA.tendsto.comp (hτ.comp (tendsto_add_atTop_nat 1))
  have h3 : (fun k => A (τ (k + 1))) = fun k => T (τ k) := funext hstep
  rw [h3] at h2
  exact tendsto_nhds_unique h1 h2

/-- 理想形の二人は t∗ で連続である。アキレスの円は ℘ に潰れる。 -/
theorem ideal_continuousAt (R : Race) :
    ContinuousAt R.idealT R.tstar ∧ ContinuousAt R.idealA R.tstar := by
  have hcg := R.continuous_g
  have hT : Continuous R.idealT :=
    contDiff_G.continuous.comp ((continuous_const.mul hcg).prodMk continuous_const)
  have h1 : Tendsto R.g (𝓝 R.tstar) (𝓝 0) := by
    have := hcg.tendsto R.tstar
    rwa [R.g_tstar] at this
  have e : R.idealA R.tstar = wp := by
    simp [Race.idealA, R.g_tstar, G_zero]
  refine ⟨hT.continuousAt, ?_⟩
  rw [ContinuousAt, e]
  exact (tendsto_G_wp (theta R.r)).comp h1

/-- **A6 の一致は強制される**：理想形の t∗ での一致は、無限個のゼノンの段階と t∗ での連続性だけから出る。 -/
theorem ideal_coincidence_forced (R : Race) : R.idealT R.tstar = R.idealA R.tstar :=
  zeno_steps_force_coincidence R.tendsto_tn (fun k => ((ideal_passage R).meet_before k).2)
    (ideal_continuousAt R).1 (ideal_continuousAt R).2

end Zeno.Model
