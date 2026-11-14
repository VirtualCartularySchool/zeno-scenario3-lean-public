/-
# Zeno.Uniform : 正則形から理想形への一様収束

首の形（定理 B）と裏返しの形（定理 C2）の走者は、理想形の走者に一様に収束する。
誤差の上界は、首の形で 2rⁿ（全時刻）、裏返しの形で 2η（t ∈ [0, 2t∗]）である。
証明に使うのは二つの事実だけである。窓の外では理想形と同じ点を通ること、
窓の中ではどちらの走者も ℘ の小さな球の中にいること。
-/
import Zeno.Regular
import Zeno.Flex

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology

/-! ### 距離の評価 -/

theorem nsq_zero_V3 : nsq (0 : V3) = 0 := by
  simp [nsq, dot]

/-- 半径 c の球の中の二点の距離の 2 乗は 4c² 未満である。 -/
theorem nsq_sub_lt {a b : V3} {c : ℝ} (ha : nsq a < c ^ 2) (hb : nsq b ≤ c ^ 2) :
    nsq (a - b) < 4 * c ^ 2 := by
  simp only [nsq, dot, Prod.fst_sub, Prod.snd_sub] at *
  nlinarith [sq_nonneg (a.1 + b.1), sq_nonneg (a.2.1 + b.2.1), sq_nonneg (a.2.2 + b.2.2)]

/-- 積空間の距離は、ユークリッドの長さ √(nsq) 以下である。 -/
theorem dist_le_sqrt_nsq (a b : V3) : dist a b ≤ √(nsq (a - b)) := by
  have h1 : |a.1 - b.1| ≤ √(nsq (a - b)) := by
    apply Real.abs_le_sqrt
    simp only [nsq, dot, Prod.fst_sub, Prod.snd_sub]
    nlinarith [mul_self_nonneg (a.2.1 - b.2.1), mul_self_nonneg (a.2.2 - b.2.2)]
  have h2 : |a.2.1 - b.2.1| ≤ √(nsq (a - b)) := by
    apply Real.abs_le_sqrt
    simp only [nsq, dot, Prod.fst_sub, Prod.snd_sub]
    nlinarith [mul_self_nonneg (a.1 - b.1), mul_self_nonneg (a.2.2 - b.2.2)]
  have h3 : |a.2.2 - b.2.2| ≤ √(nsq (a - b)) := by
    apply Real.abs_le_sqrt
    simp only [nsq, dot, Prod.fst_sub, Prod.snd_sub]
    nlinarith [mul_self_nonneg (a.1 - b.1), mul_self_nonneg (a.2.1 - b.2.1)]
  rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq]
  exact max_le h1 (max_le h2 h3)

theorem dist_lt_of_nsq_lt {a b : V3} {e : ℝ} (he : 0 < e) (h : nsq (a - b) < e ^ 2) :
    dist a b < e :=
  calc dist a b ≤ √(nsq (a - b)) := dist_le_sqrt_nsq a b
    _ < √(e ^ 2) := Real.sqrt_lt_sqrt (nsq_nonneg _) h
    _ = e := Real.sqrt_sq he.le

theorem sq_lt_sq_of_abs_lt {x c : ℝ} (h : |x| < c) : x ^ 2 < c ^ 2 := by
  nlinarith [sq_abs x, abs_nonneg x]

/-! ### 首の形：誤差は 2rⁿ 未満 -/

/-- **首の形の亀の一様評価**：w₀ = c = rⁿ の首の上の亀と理想形の亀の距離の 2 乗は、
すべての時刻で 4(rⁿ)² 未満である。 -/
theorem regular_uniform_T (R : Race) (n : ℕ) (t : ℝ) :
    nsq (R.runT (Sig (R.r ^ n)) (VtR (R.r ^ n)) t - R.idealT t) < 4 * (R.r ^ n) ^ 2 := by
  have hr0 := R.r_pos
  have hc0 : 0 < R.r ^ n := pow_pos hr0 n
  by_cases h : R.r ^ n ≤ |R.r * R.g t|
  · rw [reg_agree_T R hc0 le_rfl t h, sub_self, nsq_zero_V3]
    positivity
  · push Not at h
    have hT : nsq (R.runT (Sig (R.r ^ n)) (VtR (R.r ^ n)) t) < (R.r ^ n) ^ 2 := by
      simp only [Race.runT]
      exact nsq_Sig_neck hc0 h.le _
    have hI : nsq (R.idealT t) ≤ (R.r ^ n) ^ 2 := by
      simp only [Race.idealT]
      exact (nsq_G_le_sq _ _).trans (sq_lt_sq_of_abs_lt h).le
    exact nsq_sub_lt hT hI

/-- **首の形のアキレスの一様評価**。 -/
theorem regular_uniform_A (R : Race) (n : ℕ) (t : ℝ) :
    nsq (R.runA (Sig (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n) t - R.idealA t) <
      4 * (R.r ^ n) ^ 2 := by
  have hr0 := R.r_pos
  have hc0 : 0 < R.r ^ n := pow_pos hr0 n
  by_cases h : R.r ^ n ≤ |R.g t|
  · rw [reg_agree_A R hc0 le_rfl n t h, sub_self, nsq_zero_V3]
    positivity
  · push Not at h
    have hA : nsq (R.runA (Sig (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n) t) < (R.r ^ n) ^ 2 := by
      simp only [Race.runA]
      exact nsq_Sig_neck hc0 h.le _
    have hI : nsq (R.idealA t) ≤ (R.r ^ n) ^ 2 := by
      simp only [Race.idealA]
      exact (nsq_G_le_sq _ _).trans (sq_lt_sq_of_abs_lt h).le
    exact nsq_sub_lt hA hI

theorem eventually_two_pow_lt (R : Race) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, 2 * R.r ^ n < δ := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one R.r_pos.le R.r_lt_one
  have h2 : Tendsto (fun n : ℕ => 2 * R.r ^ n) atTop (𝓝 (2 * 0)) := hpow.const_mul 2
  rw [mul_zero] at h2
  exact h2.eventually (gt_mem_nhds hδ)

/-- **首の形の亀は理想形の亀に一様に収束する**（全時刻で）。 -/
theorem regular_tendstoUniformly_T (R : Race) :
    TendstoUniformly (fun n : ℕ => R.runT (Sig (R.r ^ n)) (VtR (R.r ^ n))) R.idealT atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [eventually_two_pow_lt R hδ] with n hn
  intro t
  rw [dist_comm]
  have hc : 0 < 2 * R.r ^ n := by have := pow_pos R.r_pos n; positivity
  have h := regular_uniform_T R n t
  have e : 4 * (R.r ^ n) ^ 2 = (2 * R.r ^ n) ^ 2 := by ring
  rw [e] at h
  exact (dist_lt_of_nsq_lt hc h).trans hn

/-- **首の形のアキレスは理想形のアキレスに一様に収束する**（全時刻で）。 -/
theorem regular_tendstoUniformly_A (R : Race) :
    TendstoUniformly (fun n : ℕ => R.runA (Sig (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n))
      R.idealA atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  filter_upwards [eventually_two_pow_lt R hδ] with n hn
  intro t
  rw [dist_comm]
  have hc : 0 < 2 * R.r ^ n := by have := pow_pos R.r_pos n; positivity
  have h := regular_uniform_A R n t
  have e : 4 * (R.r ^ n) ^ 2 = (2 * R.r ^ n) ^ 2 := by ring
  rw [e] at h
  exact (dist_lt_of_nsq_lt hc h).trans hn

/-! ### 裏返しの形：誤差は 2η 未満 -/

/-- 窓の中では、動く面の上の走者の半径 ρ は η 未満である。 -/
theorem rhoT_sq_lt (R : Race) {η : ℝ} (hη : 0 < η) {t : ℝ} (h : |R.g t| < η) :
    R.rhoT η t ^ 2 < η ^ 2 := by
  simp only [Race.rhoT]
  rw [rho_sq hη.ne']
  have hg : R.g t ^ 2 < η ^ 2 := sq_lt_sq_of_abs_lt h
  have e : hh η (η ^ 2) = η ^ 2 := hh_of_ge hη.ne' (by nlinarith [pow_pos hη 2])
  calc hh η (R.g t ^ 2) < hh η (η ^ 2) := hh_strictMono hη.ne' hg
    _ = η ^ 2 := e

/-- **裏返しの形の亀の一様評価**：t ∈ [0, 2t∗] で、動く面の上の亀と理想形の亀の距離の 2 乗は
4η² 未満である。 -/
theorem flex_uniform_T (R : Race) {κ₀ ε η : ℝ} {f : ℝ → ℝ × ℝ → V3} (h0 : 0 < κ₀)
    (h1 : κ₀ ≤ 1) (hf : IsPlaneEversion κ₀ ε f) (hη : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar)) :
    nsq (f (R.sT η t) (R.yTt η t) - R.idealT t) < 4 * η ^ 2 := by
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  by_cases h : η ≤ |R.g t|
  · rw [flex_agree_T R hη hη1 hf ht h, sub_self, nsq_zero_V3]
    positivity
  · push Not at h
    have hT : nsq (f (R.sT η t) (R.yTt η t)) < η ^ 2 := by
      rw [flexT_eq R hη hη1 hf ht, nsq_smul]
      have hk1 := kapS_le h1 (R.sT η t)
      have hk2 := kapS_pos h0 h1 (R.sT η t)
      have hk : kapS κ₀ (R.sT η t) ^ 2 ≤ 1 := by nlinarith
      have hρ := rhoT_sq_lt R hη h
      have hρp := rhoT_pos R hη t
      have h3 : nsq (Lam (phiS (R.sT η t)) (G (R.r * R.rhoT η t) 0)) < η ^ 2 := by
        refine lt_of_le_of_lt ((nsq_Lam_le _ _).trans (nsq_G_le_sq _ _)) ?_
        have e2 : (R.r * R.rhoT η t) ^ 2 = R.r ^ 2 * R.rhoT η t ^ 2 := by ring
        rw [e2]
        have hr2 : R.r ^ 2 ≤ 1 := by nlinarith
        nlinarith [pow_pos hρp 2]
      have h5 := nsq_nonneg (Lam (phiS (R.sT η t)) (G (R.r * R.rhoT η t) 0))
      nlinarith
    have hI : nsq (R.idealT t) ≤ η ^ 2 := by
      simp only [Race.idealT]
      refine (nsq_G_le_sq _ _).trans ?_
      have hg : R.g t ^ 2 < η ^ 2 := sq_lt_sq_of_abs_lt h
      have e2 : (R.r * R.g t) ^ 2 = R.r ^ 2 * R.g t ^ 2 := by ring
      rw [e2]
      have hr2 : R.r ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg (R.g t)]
    exact nsq_sub_lt hT hI

/-- **裏返しの形のアキレスの一様評価**。 -/
theorem flex_uniform_A (R : Race) {κ₀ ε η : ℝ} {f : ℝ → ℝ × ℝ → V3} (h0 : 0 < κ₀)
    (h1 : κ₀ ≤ 1) (hf : IsPlaneEversion κ₀ ε f) (hη : 0 < η) (hη1 : η < 1) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar)) :
    nsq (f (R.sT η t) (R.yAt η t) - R.idealA t) < 4 * η ^ 2 := by
  by_cases h : η ≤ |R.g t|
  · rw [flex_agree_A R hη hη1 hf ht h, sub_self, nsq_zero_V3]
    positivity
  · push Not at h
    have hA : nsq (f (R.sT η t) (R.yAt η t)) < η ^ 2 := by
      rw [flexA_eq R hη hη1 hf ht, nsq_smul]
      have hk1 := kapS_le h1 (R.sT η t)
      have hk2 := kapS_pos h0 h1 (R.sT η t)
      have hk : kapS κ₀ (R.sT η t) ^ 2 ≤ 1 := by nlinarith
      have h3 : nsq (Lam (phiS (R.sT η t)) (G (R.rhoT η t) (R.thT η t))) < η ^ 2 :=
        lt_of_le_of_lt ((nsq_Lam_le _ _).trans (nsq_G_le_sq _ _)) (rhoT_sq_lt R hη h)
      have h5 := nsq_nonneg (Lam (phiS (R.sT η t)) (G (R.rhoT η t) (R.thT η t)))
      nlinarith
    have hI : nsq (R.idealA t) ≤ η ^ 2 := by
      simp only [Race.idealA]
      exact (nsq_G_le_sq _ _).trans (sq_lt_sq_of_abs_lt h).le
    exact nsq_sub_lt hA hI

/-- **裏返しの形の亀は理想形の亀に一様に収束する**（t ∈ [0, 2t∗] で、f を固定して η → 0）。 -/
theorem flex_tendstoUniformlyOn_T (R : Race) {κ₀ ε : ℝ} {f : ℝ → ℝ × ℝ → V3} (h0 : 0 < κ₀)
    (h1 : κ₀ ≤ 1) (hf : IsPlaneEversion κ₀ ε f) :
    TendstoUniformlyOn (fun η t => f (R.sT η t) (R.yTt η t)) R.idealT (𝓝[>] 0)
      (Icc 0 (2 * R.tstar)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hpos : 0 < min 1 (δ / 2) := lt_min one_pos (half_pos hδ)
  filter_upwards [Ioo_mem_nhdsGT hpos] with η hη
  intro t ht
  have hη1 : η < 1 := lt_of_lt_of_le hη.2 (min_le_left _ _)
  have hη2 : η < δ / 2 := lt_of_lt_of_le hη.2 (min_le_right _ _)
  rw [dist_comm]
  have h := flex_uniform_T R h0 h1 hf hη.1 hη1 ht
  have e : 4 * η ^ 2 = (2 * η) ^ 2 := by ring
  rw [e] at h
  have hc : 0 < 2 * η := by linarith [hη.1]
  exact (dist_lt_of_nsq_lt hc h).trans (by linarith)

/-- **裏返しの形のアキレスは理想形のアキレスに一様に収束する**。 -/
theorem flex_tendstoUniformlyOn_A (R : Race) {κ₀ ε : ℝ} {f : ℝ → ℝ × ℝ → V3} (h0 : 0 < κ₀)
    (h1 : κ₀ ≤ 1) (hf : IsPlaneEversion κ₀ ε f) :
    TendstoUniformlyOn (fun η t => f (R.sT η t) (R.yAt η t)) R.idealA (𝓝[>] 0)
      (Icc 0 (2 * R.tstar)) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro δ hδ
  have hpos : 0 < min 1 (δ / 2) := lt_min one_pos (half_pos hδ)
  filter_upwards [Ioo_mem_nhdsGT hpos] with η hη
  intro t ht
  have hη1 : η < 1 := lt_of_lt_of_le hη.2 (min_le_left _ _)
  have hη2 : η < δ / 2 := lt_of_lt_of_le hη.2 (min_le_right _ _)
  rw [dist_comm]
  have h := flex_uniform_A R h0 h1 hf hη.1 hη1 ht
  have e : 4 * η ^ 2 = (2 * η) ^ 2 := by ring
  rw [e] at h
  have hc : 0 < 2 * η := by linarith [hη.1]
  exact (dist_lt_of_nsq_lt hc h).trans (by linarith)

end Zeno.Model
