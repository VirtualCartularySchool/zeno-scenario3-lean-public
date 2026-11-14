/-
# ZenoSmale.KleinIdeal : D7 の三つの比較の分離、量化の順序、理想形への一様収束

1. **D7 の比較**。t∗ での比較には三つの別の量がある。
   - 助変数の比較 𝒞 = r g − g：t∗ でだけ 0（`compare_zero`。静的・動的に共通）。
   - 静的な面の上の x̂ の比較：x̂(runT(t∗)) = x̂(runA(t∗))（`compare_xhat`）。
   - 動的な面の上の x̂ の比較：基底では差が 2bb₀/N₀ > 0（`base_xhat_sep`）、
     F では ε < bb₀ のとき x̂(dynT(t∗)) > 0 > x̂(dynA(t∗))（`DynamicPassage.xhat_sign`）。
   したがって静的な等式 (2″) は動的な面では成り立たない。断面の座標の差は、静的には (0, 2bb₀)、
   動的な基底では (0, 0) である。回転枠 rot2(−π/2) では静的な値に戻る（`base_rotated_frame`）。

2. **量化の順序**。面の族と導線を固定して、すべての段階数 n₁ について `DynamicPassage`（または
   `KleinPassage`）を満たすことはできない（`no_uniform_dynamic_passage`）。これは定理 10.1
   （`zeno_steps_force_coincidence`）の系である。証明された形 ∀n₁ ∃F は、この意味で最良である。

3. **理想化の極限**。w₀ = c = ε = rⁿ の裏返し F_n の上の走者は、[0, 2t∗] の上で理想形の走者に
   一様に収束する（誤差は 4rⁿ 未満）。窓 [t₁, t₂] は t∗ に、首の球の半径 2rⁿ は 0 に収束する。

4. **℘ の回避**。ε が中央円の径 √N₀ より小さければ、動く面の上の二人は全時刻で ℘ を通らない
   （`DynamicPassage.runner_T_ne_wp`）。bb₀ < √N₀ なので ε < bb₀ で足りる。
-/
import ZenoSmale.KleinNormal
import Zeno.Uniform
import Zeno.Meaning

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff
open Zeno.Model

/-! ### 成分とノルム -/

theorem abs_fst_le_en (q : V3) : |q.1| ≤ en q := by
  show |q.1| ≤ √(nsq q)
  apply Real.abs_le_sqrt
  simp only [nsq, dot]
  nlinarith [mul_self_nonneg q.2.1, mul_self_nonneg q.2.2]

theorem abs_snd_fst_le_en (q : V3) : |q.2.1| ≤ en q := by
  show |q.2.1| ≤ √(nsq q)
  apply Real.abs_le_sqrt
  simp only [nsq, dot]
  nlinarith [mul_self_nonneg q.1, mul_self_nonneg q.2.2]

theorem abs_snd_snd_le_en (q : V3) : |q.2.2| ≤ en q := by
  show |q.2.2| ≤ √(nsq q)
  apply Real.abs_le_sqrt
  simp only [nsq, dot]
  nlinarith [mul_self_nonneg q.1, mul_self_nonneg q.2.1]

theorem nsq_pos_of_fst_ne {q : V3} (h : q.1 ≠ 0) : 0 < nsq q := by
  have h2 := mul_self_pos.mpr h
  simp only [nsq, dot]
  nlinarith [mul_self_nonneg q.2.1, mul_self_nonneg q.2.2]

theorem xhat_pos_of {q : V3} (h : 0 < q.1) : 0 < xhat q := by
  unfold xhat
  exact div_pos h (nsq_pos_of_fst_ne h.ne')

theorem xhat_neg_of {q : V3} (h : q.1 < 0) : xhat q < 0 := by
  unfold xhat
  exact div_neg_of_neg_of_pos h (nsq_pos_of_fst_ne h.ne)

/-! ### D7：基底の上の比較 -/

section BaseCompare

variable (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 in
theorem xhat_baseT {c : ℝ} (hc : 0 < c) :
    xhat (baseT R w₀ c R.tstar) = BB w₀ 0 / (AA w₀ 0 ^ 2 + BB w₀ 0 ^ 2) := by
  rw [(Model.base_tstar h0 R hc 0).1]
  simp only [xhat, nsq, dot]
  congr 1
  ring

include h0 in
theorem xhat_baseA {c : ℝ} (hc : 0 < c) (n₁ : ℕ) :
    xhat (baseA R w₀ c n₁ R.tstar) = -(BB w₀ 0) / (AA w₀ 0 ^ 2 + BB w₀ 0 ^ 2) := by
  rw [(Model.base_tstar h0 R hc n₁).2]
  simp only [xhat, nsq, dot]
  congr 1
  ring

include h0 h1 in
/-- **動的な基底の x̂ の差**は 2bb₀/N₀ > 0 である（静的な走者では 0：`compare_xhat`）。 -/
theorem base_xhat_sep {c : ℝ} (hc : 0 < c) (n₁ : ℕ) :
    xhat (baseT R w₀ c R.tstar) - xhat (baseA R w₀ c n₁ R.tstar) =
        2 * BB w₀ 0 / (AA w₀ 0 ^ 2 + BB w₀ 0 ^ 2) ∧
      0 < 2 * BB w₀ 0 / (AA w₀ 0 ^ 2 + BB w₀ 0 ^ 2) := by
  have hBB := BB_pos h0 h1 0
  have hN : 0 < AA w₀ 0 ^ 2 + BB w₀ 0 ^ 2 := by nlinarith [sq_nonneg (AA w₀ 0), pow_pos hBB 2]
  refine ⟨?_, div_pos (by linarith) hN⟩
  rw [xhat_baseT R h0 hc, xhat_baseA R h0 hc n₁]
  field_simp
  ring

include h0 in
/-- 動的な基底では、固定枠の断面の座標（第 2・第 3 成分）の差は 0 である
（静的には (0, 2bb₀)：`cross_section`）。 -/
theorem base_cross_section {c : ℝ} (hc : 0 < c) (n₁ : ℕ) :
    (baseT R w₀ c R.tstar).2 - (baseA R w₀ c n₁ R.tstar).2 = ((0 : ℝ), (0 : ℝ)) := by
  obtain ⟨eT, eA⟩ := Model.base_tstar h0 R hc n₁
  rw [eT, eA]
  simp only [sub_self]
  rfl

include h0 h1 in
/-- **回転枠**：動的な基底の t∗ の位置を rot2(−π/2) で戻すと静的な位置になる。
したがって回転枠では (2″)（`compare_xhat`）と (1″)（`cross_section`）が正確に成り立つ。 -/
theorem base_rotated_frame {c : ℝ} (hc : w₀ ≤ c) (n₁ : ℕ) :
    rot2 (-(π / 2)) (baseT R w₀ c R.tstar) = R.runT (Shat w₀) (VtR c) R.tstar ∧
      rot2 (-(π / 2)) (baseA R w₀ c n₁ R.tstar) =
        R.runA (Shat w₀) (VaR R.r w₀ c n₁) R.tstar := by
  obtain ⟨eT, eA⟩ := Model.base_rotation h0 h1 R hc n₁
  rw [eT, eA, rot2_neg_self, rot2_neg_self]
  exact ⟨rfl, rfl⟩

end BaseCompare

/-! ### D7：動的な F の上の比較 -/

section DynCompare

variable {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3} {F : ℝ → ℝ → ℝ → V3}
  {Vt Va : ℝ → ℝ} (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va)

include P in
/-- ε < bb₀ なら、t∗ で亀の第 1 成分は正である。 -/
theorem DynamicPassage.fst_T_pos (hε : ε < BB w₀ 0) : 0 < (dynT R w₀ F Vt R.tstar).1 := by
  have hT : en (dynT R w₀ F Vt R.tstar - baseT R w₀ c R.tstar) ≤ ε :=
    P.near_T R.tstar R.tstar_mem
  have h := abs_fst_le_en (dynT R w₀ F Vt R.tstar - baseT R w₀ c R.tstar)
  have e : (dynT R w₀ F Vt R.tstar - baseT R w₀ c R.tstar).1 =
      (dynT R w₀ F Vt R.tstar).1 - BB w₀ 0 := by
    rw [P.base_tstar.1]; rfl
  rw [e] at h
  have h2 := abs_le.mp (h.trans hT)
  linarith [h2.1]

include P in
/-- ε < bb₀ なら、t∗ でアキレスの第 1 成分は負である。 -/
theorem DynamicPassage.fst_A_neg (hε : ε < BB w₀ 0) : (dynA R w₀ F Va R.tstar).1 < 0 := by
  have hA : en (dynA R w₀ F Va R.tstar - baseA R w₀ c n₁ R.tstar) ≤ ε :=
    P.near_A R.tstar R.tstar_mem
  have h := abs_fst_le_en (dynA R w₀ F Va R.tstar - baseA R w₀ c n₁ R.tstar)
  have e : (dynA R w₀ F Va R.tstar - baseA R w₀ c n₁ R.tstar).1 =
      (dynA R w₀ F Va R.tstar).1 + BB w₀ 0 := by
    rw [P.base_tstar.2]
    show (dynA R w₀ F Va R.tstar).1 - -(BB w₀ 0) = _
    ring
  rw [e] at h
  have h2 := abs_le.mp (h.trans hA)
  linarith [h2.2]

include P in
/-- **動的な F の上の x̂ の比較**：ε < bb₀ なら、t∗ で x̂(T) > 0 > x̂(A)。
静的な等式 (2″)（`compare_xhat`）は動的な面では成り立たない。 -/
theorem DynamicPassage.xhat_sign (hε : ε < BB w₀ 0) :
    0 < xhat (dynT R w₀ F Vt R.tstar) ∧ xhat (dynA R w₀ F Va R.tstar) < 0 :=
  ⟨xhat_pos_of (P.fst_T_pos hε), xhat_neg_of (P.fst_A_neg hε)⟩

include P in
theorem DynamicPassage.xhat_ne (hε : ε < BB w₀ 0) :
    xhat (dynT R w₀ F Vt R.tstar) ≠ xhat (dynA R w₀ F Va R.tstar) := by
  have h := P.xhat_sign hε
  intro e
  rw [e] at h
  linarith [h.1, h.2]

include P in
/-- 動的な F の上では、t∗ での固定枠の断面の座標の差は 2ε 以内である（静的には (0, 2bb₀)）。 -/
theorem DynamicPassage.cross_section_small :
    |(dynT R w₀ F Vt R.tstar).2.1 - (dynA R w₀ F Va R.tstar).2.1| ≤ 2 * ε ∧
      |(dynT R w₀ F Vt R.tstar).2.2 - (dynA R w₀ F Va R.tstar).2.2| ≤ 2 * ε := by
  have h : en (dynT R w₀ F Vt R.tstar - dynA R w₀ F Va R.tstar - (2 * BB w₀ 0, 0, 0)) ≤ 2 * ε :=
    P.separation
  have h1 := (abs_snd_fst_le_en _).trans h
  have h2 := (abs_snd_snd_le_en _).trans h
  have e1 : (dynT R w₀ F Vt R.tstar - dynA R w₀ F Va R.tstar - (2 * BB w₀ 0, 0, 0)).2.1 =
      (dynT R w₀ F Vt R.tstar).2.1 - (dynA R w₀ F Va R.tstar).2.1 := by
    show (dynT R w₀ F Vt R.tstar).2.1 - (dynA R w₀ F Va R.tstar).2.1 - 0 = _
    ring
  have e2 : (dynT R w₀ F Vt R.tstar - dynA R w₀ F Va R.tstar - (2 * BB w₀ 0, 0, 0)).2.2 =
      (dynT R w₀ F Vt R.tstar).2.2 - (dynA R w₀ F Va R.tstar).2.2 := by
    show (dynT R w₀ F Vt R.tstar).2.2 - (dynA R w₀ F Va R.tstar).2.2 - 0 = _
    ring
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1, h2⟩

end DynCompare

/-! ### 動的な走者は ℘ を通らない -/

section Avoid

variable {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {X : ℝ → ℝ → V3} {F : ℝ → ℝ → ℝ → V3}
  {Vt Va : ℝ → ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)
  (P : DynamicPassage R w₀ c ε n₁ (Shat w₀) X F Vt Va)

include h0 h1 in
/-- 首の帯 |w| ≤ 1 の上で、Σ の径は中央円の径以上である。 -/
theorem nsq_Sig_zero_le {w : ℝ} (hw : |w| ≤ 1) (v : ℝ) :
    nsq (Sig w₀ 0 0) ≤ nsq (Sig w₀ w v) := by
  rcases eq_or_ne w 0 with rfl | hne
  · rw [nsq_Sig h0.ne', nsq_Sig h0.ne']
  · have hlt : |(0 : ℝ)| < |w| := by simpa using abs_pos.mpr hne
    exact (nsq_Sig_lt h0.ne' (by nlinarith) hlt hw 0 v).le

include h0 h1 in
/-- bb₀ は中央円の径 √N₀ より小さい。 -/
theorem BB_zero_lt_en : BB w₀ 0 < en (Sig w₀ 0 0) := by
  have hBB := BB_pos h0 h1 0
  have hAA : 0 < AA w₀ 0 := by rw [AA_zero]; exact aa_pos (rho_pos h0.ne' 0)
  obtain ⟨e1, e2⟩ := Sig_zero_sq h0 0
  have hN : nsq (Sig w₀ 0 0) = AA w₀ 0 ^ 2 + BB w₀ 0 ^ 2 := by
    simp only [nsq, dot]
    nlinarith [e1, e2]
  have hlt : BB w₀ 0 ^ 2 < nsq (Sig w₀ 0 0) := by rw [hN]; nlinarith [pow_pos hAA 2]
  have h := Real.sqrt_lt_sqrt (sq_nonneg (BB w₀ 0)) hlt
  rwa [Real.sqrt_sq hBB.le] at h

include h0 h1 P in
/-- **動く面の上の亀は ℘ を通らない**（ε が中央円の径より小さいとき。全時刻）。 -/
theorem DynamicPassage.runner_T_ne_wp (hε : ε < en (Sig w₀ 0 0)) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar)) : dynT R w₀ F Vt t ≠ wp := by
  by_cases hA : t ≤ t1 R w₀
  · rw [(P.static_before t hA).1]
    exact Shat_ne_wp h0 h1 _ _
  · by_cases hB : t2 R w₀ ≤ t
    · rw [(P.static_after t hB ht.2).1]
      intro h
      exact Shat_ne_wp h0 h1 _ _ (neg_eq_zero.mp h)
    · push Not at hA hB
      have hs : |en (dynT R w₀ F Vt t) - en (Sig w₀ (R.r * R.g t) 0)| ≤ ε :=
        P.sandwich_T t ⟨hA.le, hB.le⟩
      have hlow : en (Sig w₀ 0 0) ≤ en (Sig w₀ (R.r * R.g t) 0) :=
        Real.sqrt_le_sqrt (nsq_Sig_zero_le h0 h1 (R.abs_r_g_le_one ht) 0)
      have h2 := abs_le.mp hs
      have hpos : 0 < en (dynT R w₀ F Vt t) := by linarith [h2.1]
      intro h
      rw [h] at hpos
      have hz : en wp = 0 := (en_eq_zero_iff wp).mpr rfl
      linarith

include h0 h1 P in
/-- **動く面の上のアキレスは ℘ を通らない**。 -/
theorem DynamicPassage.runner_A_ne_wp (hε : ε < en (Sig w₀ 0 0)) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar)) : dynA R w₀ F Va t ≠ wp := by
  by_cases hA : t ≤ t1 R w₀
  · rw [(P.static_before t hA).2]
    exact Shat_ne_wp h0 h1 _ _
  · by_cases hB : t2 R w₀ ≤ t
    · rw [(P.static_after t hB ht.2).2]
      intro h
      exact Shat_ne_wp h0 h1 _ _ (neg_eq_zero.mp h)
    · push Not at hA hB
      have hs : |en (dynA R w₀ F Va t) - en (Sig w₀ (R.g t) 0)| ≤ ε :=
        P.sandwich_A t ⟨hA.le, hB.le⟩
      have hlow : en (Sig w₀ 0 0) ≤ en (Sig w₀ (R.g t) 0) :=
        Real.sqrt_le_sqrt (nsq_Sig_zero_le h0 h1 (R.abs_g_le ht.1 ht.2) 0)
      have h2 := abs_le.mp hs
      have hpos : 0 < en (dynA R w₀ F Va t) := by linarith [h2.1]
      intro h
      rw [h] at hpos
      have hz : en wp = 0 := (en_eq_zero_iff wp).mpr rfl
      linarith

end Avoid

/-! ### 量化の順序：一つの面の族ですべての段階を実現することはできない -/

/-- **定理 10.1 の系**：t∗ で連続な二人の軌道が、すべての k でゼノンの段階 A(tₖ₊₁) = T(tₖ) を満たすなら、
t∗ に二人は同じ点にいる。 -/
theorem all_steps_force_meeting (R : Race) {T A : ℝ → V3} (hT : ContinuousAt T R.tstar)
    (hA : ContinuousAt A R.tstar) (hstep : ∀ k, A (R.tn (k + 1)) = T (R.tn k)) :
    T R.tstar = A R.tstar :=
  zeno_steps_force_coincidence R.tendsto_tn hstep hT hA

/-- **量化の順序（動的）**：首の幅 w₀、面 S、裏返しの族 F、導線 Vt・Va を固定して、すべての段階数 n₁ に
ついて `DynamicPassage` を満たすことはできない（岸の閾値 c と近さ ε は n₁ ごとに変えてもよい）。 -/
theorem no_uniform_dynamic_passage (R : Race) :
    ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (F : ℝ → ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
      ∀ n₁ : ℕ, ∃ c ε : ℝ, DynamicPassage R w₀ c ε n₁ S X F Vt Va := by
  rintro ⟨w₀, S, X, F, Vt, Va, h⟩
  obtain ⟨c₀, ε₀, P₀⟩ := h 0
  have hstep : ∀ k, dynA R w₀ F Va (R.tn (k + 1)) = dynT R w₀ F Vt (R.tn k) := by
    intro k
    obtain ⟨c, ε, P⟩ := h (k + 1)
    exact P.step_before k (Nat.lt_succ_self k)
  have hmeet := all_steps_force_meeting R P₀.smooth_T.continuous.continuousAt
    P₀.smooth_A.continuous.continuousAt hstep
  exact P₀.no_collision R.tstar R.tstar_mem hmeet

/-- **量化の順序（静的）**：面 S と導線を固定して、すべての段階数 n₁ について `KleinPassage` を
満たすことはできない。 -/
theorem no_uniform_klein_passage (R : Race) :
    ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
      ∀ n₁ : ℕ, ∃ c : ℝ, KleinPassage R w₀ c n₁ S X Vt Va := by
  rintro ⟨w₀, S, X, Vt, Va, h⟩
  obtain ⟨c₀, P₀⟩ := h 0
  have hstep : ∀ k, R.runA S Va (R.tn (k + 1)) = R.runT S Vt (R.tn k) := by
    intro k
    obtain ⟨c, P⟩ := h (k + 1)
    exact P.step_before k (Nat.lt_succ_self k)
  have hmeet := all_steps_force_meeting R P₀.smooth_T.continuous.continuousAt
    P₀.smooth_A.continuous.continuousAt hstep
  exact P₀.no_collision R.tstar R.tstar_mem hmeet

/-! ### 理想形への一様収束 -/

section Limit

variable {R : Race} {w₀ ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3} {F : ℝ → ℝ → ℝ → V3}
  {Vt Va : ℝ → ℝ}

/-- **動的な亀の一様評価**：岸の閾値が首の幅に等しい（c = w₀）とき、[0, 2t∗] の上で、動く面の上の亀と
理想形の亀の距離の 2 乗は 4(w₀ + ε)² 未満である。 -/
theorem DynamicPassage.uniform_T (P : DynamicPassage R w₀ w₀ ε n₁ S X F Vt Va) (h0 : 0 < w₀)
    (hε : 0 ≤ ε) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    nsq (dynT R w₀ F Vt t - R.idealT t) < 4 * (w₀ + ε) ^ 2 := by
  have hpos : 0 < w₀ + ε := by linarith
  by_cases h : w₀ ≤ |R.r * R.g t|
  · rw [P.agree_T t ht h, sub_self, nsq_zero_V3]
    positivity
  · push Not at h
    have hT : nsq (dynT R w₀ F Vt t) < (w₀ + ε) ^ 2 := P.eversion.ball _ _ _ h.le
    have hI : nsq (R.idealT t) ≤ (w₀ + ε) ^ 2 := by
      simp only [Race.idealT]
      refine (nsq_G_le_sq _ _).trans ?_
      have h2 := sq_lt_sq_of_abs_lt h
      nlinarith [mul_nonneg hε h0.le, sq_nonneg ε]
    exact nsq_sub_lt hT hI

/-- **動的なアキレスの一様評価**。 -/
theorem DynamicPassage.uniform_A (P : DynamicPassage R w₀ w₀ ε n₁ S X F Vt Va) (h0 : 0 < w₀)
    (hε : 0 ≤ ε) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    nsq (dynA R w₀ F Va t - R.idealA t) < 4 * (w₀ + ε) ^ 2 := by
  have hpos : 0 < w₀ + ε := by linarith
  by_cases h : w₀ ≤ |R.g t|
  · rw [P.agree_A t ht h, sub_self, nsq_zero_V3]
    positivity
  · push Not at h
    have hA : nsq (dynA R w₀ F Va t) < (w₀ + ε) ^ 2 := P.eversion.ball _ _ _ h.le
    have hI : nsq (R.idealA t) ≤ (w₀ + ε) ^ 2 := by
      simp only [Race.idealA]
      refine (nsq_G_le_sq _ _).trans ?_
      have h2 := sq_lt_sq_of_abs_lt h
      nlinarith [mul_nonneg hε h0.le, sq_nonneg ε]
    exact nsq_sub_lt hA hI

end Limit

/-- **一様収束の判定**：各 n ≥ 1 で w₀ = c = ε = rⁿ の `DynamicPassage` を満たす族 F_n の上の走者は、
[0, 2t∗] の上で理想形の走者に一様に収束する。誤差は 4rⁿ 未満である。 -/
theorem dynamic_tendstoUniformlyOn (R : Race) {F : ℕ → ℝ → ℝ → ℝ → V3}
    {S X : ℕ → ℝ → ℝ → V3}
    (hF : ∀ n : ℕ, 1 ≤ n → DynamicPassage R (R.r ^ n) (R.r ^ n) (R.r ^ n) n (S n) (X n) (F n)
      (VtR (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n)) :
    (∀ n : ℕ, 1 ≤ n → ∀ t ∈ Icc 0 (2 * R.tstar),
        nsq (dynT R (R.r ^ n) (F n) (VtR (R.r ^ n)) t - R.idealT t) < (4 * R.r ^ n) ^ 2 ∧
        nsq (dynA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n) t - R.idealA t) <
          (4 * R.r ^ n) ^ 2) ∧
      TendstoUniformlyOn (fun n => dynT R (R.r ^ n) (F n) (VtR (R.r ^ n))) R.idealT atTop
        (Icc 0 (2 * R.tstar)) ∧
      TendstoUniformlyOn (fun n => dynA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n))
        R.idealA atTop (Icc 0 (2 * R.tstar)) := by
  have hbound : ∀ n : ℕ, 1 ≤ n → ∀ t ∈ Icc 0 (2 * R.tstar),
      nsq (dynT R (R.r ^ n) (F n) (VtR (R.r ^ n)) t - R.idealT t) < (4 * R.r ^ n) ^ 2 ∧
      nsq (dynA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n) t - R.idealA t) <
        (4 * R.r ^ n) ^ 2 := by
    intro n hn t ht
    have P := hF n hn
    have hp := pow_pos R.r_pos n
    have e : 4 * (R.r ^ n + R.r ^ n) ^ 2 = (4 * R.r ^ n) ^ 2 := by ring
    constructor
    · have h := P.uniform_T hp hp.le ht
      rwa [e] at h
    · have h := P.uniform_A hp hp.le ht
      rwa [e] at h
  refine ⟨hbound, ?_, ?_⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [eventually_two_pow_lt R (half_pos hδ), eventually_ge_atTop 1] with n hn hn1
    intro t ht
    rw [dist_comm]
    have hc : 0 < 4 * R.r ^ n := by have := pow_pos R.r_pos n; positivity
    exact (dist_lt_of_nsq_lt hc (hbound n hn1 t ht).1).trans (by linarith)
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [eventually_two_pow_lt R (half_pos hδ), eventually_ge_atTop 1] with n hn hn1
    intro t ht
    rw [dist_comm]
    have hc : 0 < 4 * R.r ^ n := by have := pow_pos R.r_pos n; positivity
    exact (dist_lt_of_nsq_lt hc (hbound n hn1 t ht).2).trans (by linarith)

/-- **理想化の極限**：各 n ≥ 1 について w₀ = c = ε = rⁿ の `DynamicPassage` を満たす裏返し F_n があり、
その上の二人の走者は [0, 2t∗] の上で理想形（定理 4.1）の走者に一様に収束する。誤差は 4rⁿ 未満である。 -/
theorem klein_dynamic_limit (R : Race) :
    ∃ F : ℕ → ℝ → ℝ → ℝ → V3,
      (∀ n : ℕ, 1 ≤ n → DynamicPassage R (R.r ^ n) (R.r ^ n) (R.r ^ n) n (Shat (R.r ^ n))
        (Xhat (R.r ^ n)) (F n) (VtR (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n)) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ t ∈ Icc 0 (2 * R.tstar),
        nsq (dynT R (R.r ^ n) (F n) (VtR (R.r ^ n)) t - R.idealT t) < (4 * R.r ^ n) ^ 2 ∧
        nsq (dynA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n) t - R.idealA t) <
          (4 * R.r ^ n) ^ 2) ∧
      TendstoUniformlyOn (fun n => dynT R (R.r ^ n) (F n) (VtR (R.r ^ n))) R.idealT atTop
        (Icc 0 (2 * R.tstar)) ∧
      TendstoUniformlyOn (fun n => dynA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n))
        R.idealA atTop (Icc 0 (2 * R.tstar)) := by
  have hex : ∀ n : ℕ, ∃ F : ℝ → ℝ → ℝ → V3, 1 ≤ n →
      DynamicPassage R (R.r ^ n) (R.r ^ n) (R.r ^ n) n (Shat (R.r ^ n))
        (Xhat (R.r ^ n)) F (VtR (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n) := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨F, P⟩ := dynamic_passage R hn (pow_pos R.r_pos n)
      exact ⟨F, fun _ => P⟩
    · exact ⟨fun _ _ _ => wp, fun h => absurd h hn⟩
  choose F hF using hex
  exact ⟨F, hF, dynamic_tendstoUniformlyOn R hF⟩

/-- **窓と球の収束**：n → ∞ で、裏返しの窓の両端 t₁、t₂ は t∗ に、首を含む球の半径 2rⁿ は 0 に収束する。 -/
theorem klein_window_tendsto (R : Race) :
    Tendsto (fun n : ℕ => t1 R (R.r ^ n)) atTop (𝓝 R.tstar) ∧
      Tendsto (fun n : ℕ => t2 R (R.r ^ n)) atTop (𝓝 R.tstar) ∧
      Tendsto (fun n : ℕ => 2 * R.r ^ n) atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one R.r_pos.le R.r_lt_one
  refine ⟨?_, ?_, ?_⟩
  · have h : Tendsto (fun n : ℕ => R.tstar * (1 - R.r ^ n / 4)) atTop
        (𝓝 (R.tstar * (1 - 0 / 4))) :=
      (tendsto_const_nhds.sub (hpow.div_const 4)).const_mul _
    simpa [t1] using h
  · have h : Tendsto (fun n : ℕ => R.tstar * (1 + R.r ^ n / 4)) atTop
        (𝓝 (R.tstar * (1 + 0 / 4))) :=
      (tendsto_const_nhds.add (hpow.div_const 4)).const_mul _
    simpa [t2] using h
  · have h : Tendsto (fun n : ℕ => 2 * R.r ^ n) atTop (𝓝 (2 * 0)) := hpow.const_mul 2
    simpa using h

end Zeno.Smale
