/-
# ZenoSmale.KleinConception : 原構想との対応に使う橋（閉路、モノドロミー、ラベルの時刻、枠の法則 E、無限捻転、ホーン）

`KleinSynthesis` の結果を、研究用の証明本文（命題 A、被覆空間の辞書、原構想との対応）が使う形に
つなぐ小さな定理を置く。

- 首の帯：{|w| < 2} の上で被覆写像 `toM` が同一視するのは T の冪だけである（`toM_eq_of_strip`）。
  したがって首の円 {w = 0} は M の中で環の芯である。
- モノドロミー：p から γ_{k,m}(p) への道に沿って運んだ法線は、(−1)ᵏ の正の倍で戻る
  （`normal_monodromy_gam`）。静的な面と族のどの段にも適用する。
- 閉路：亀とアキレスの閉路は、首の円の持ち上げ {w ∈ 4ℤ} を t∗ にちょうど一度、0 でない速度で横切り、
  終点は γ_{−1,0}（= Ω の逆）による始点の像である（`klein_loop_T`、`klein_loop_A`）。
- ラベルの交換の時刻：動く面の法線でのラベルが 0 になる時刻は首の中にあり、|t − t∗| は亀で
  t∗ rⁿ⁻¹、アキレスで t∗ rⁿ より小さい。n → ∞ で t∗ に収束する。静的な面では、t∗ に二人はまだ
  元のラベルにいて、t∗ の後の首の中にラベルの零点がある。
- 枠の法則 E：裏返しの終わりの首の枠は、Ŝ の首の枠を φ で引き戻して E で写したものである
  （`stage_frame_finish`）。窓の前の走者の枠は静的な枠であり、窓の後の走者の枠は、鏡の時刻 2t∗ − t の
  静的な枠を E で写したものである（`DynamicPassage.frame_after_T`、`frame_after_A`）。
- 動く面の上のモノドロミー：段が連続に変わる間に運んだ側も (−1)ᵏ の正の倍で戻る
  （`dynamic_monodromy`）。走者の閉路では反転して戻る（`dynamic_loop_T`、`dynamic_loop_A`）。
- 比較の値 x̂：岸では理想形の値 1/(r g)、1/g であり（`DynamicPassage.xhat_shore_T`、`xhat_shore_A`）、
  動く面の上では t∗ の後の首の中に x̂(T) = x̂(A) となる時刻があって、そのとき二人は別の点にいる
  （`xhat_zero_after`）。
- 【議論】の形：同じ F の上の M1、非衝突、最初の段階、M2、比較（`klein_argument_form`）。
- 無限捻転：アキレスの角度は w = rᵏ（k ≤ n₁）で 2πk、首の中央で π/2 + 2πn₁ であり、n₁ → ∞ で
  発散する（`twist_at_step`、`twist_tendsto`）。
- ホーン：族のどの段も、反転したホーンの |X| ≤ 1/w₀ の部分を正確に含み、n → ∞ でホーンを尽くす。
  コンパクトな M の連続像は非有界なホーンを含まず、反転したホーンの全体を含む連続像は ℘ を通る。
-/
import ZenoSmale.KleinSynthesis

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff
open Zeno.Model

local notation "s₀" => Real.smoothTransition

/-! ### 首の帯：首の円は M の中で環の芯である -/

/-- 首の帯 {|w| < 2} の上で、被覆写像が同一視するのは T の冪だけである。 -/
theorem toM_eq_of_strip {p q : ℝ × ℝ} (hp : |p.1| < 2) (hq : |q.1| < 2) (h : toM p = toM q) :
    ∃ m : ℤ, q = (p.1, p.2 + (m : ℝ) * (2 * π)) := by
  obtain ⟨k, m, hkm⟩ := toM_eq_iff.mp h
  have h1 : p.1 + 4 * (k : ℝ) = q.1 := by rw [← hkm]; rfl
  obtain ⟨hp1, hp2⟩ := abs_lt.mp hp
  obtain ⟨hq1, hq2⟩ := abs_lt.mp hq
  have hk : k = 0 := by
    have h3 : (-1 : ℝ) < k := by linarith
    have h4 : (k : ℝ) < 1 := by linarith
    have h5 : (-1 : ℤ) < k := by exact_mod_cast h3
    have h6 : k < 1 := by exact_mod_cast h4
    omega
  refine ⟨m, ?_⟩
  rw [← hkm, hk]
  simp [gam, sgn_zero]

/-! ### モノドロミーは向きの指標 (−1)ᵏ である -/

theorem sgn_of_even {k : ℤ} (h : Even k) : sgn k = 1 := by simp [sgn, h]

theorem sgn_of_not_even {k : ℤ} (h : ¬ Even k) : sgn k = -1 := by simp [sgn, h]

/-- **モノドロミー**。X が Γ の作用で X∘γ_{k,m} = (−1)ᵏ X を満たすとき、終点が γ_{k,m}(始点) である道に
沿って連続に運んだ消えない法線は、(−1)ᵏ の正の倍で戻る。 -/
theorem normal_monodromy_gam {X : ℝ → ℝ → V3}
    (hX : Continuous (fun p : ℝ × ℝ => X p.1 p.2)) (hne : ∀ w v, X w v ≠ wp)
    (hgam : ∀ (k m : ℤ) (p : ℝ × ℝ), X (gam k m p).1 (gam k m p).2 = sgn k • X p.1 p.2)
    {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ) {a b : ℝ} {k m : ℤ} (hend : γ b = gam k m (γ a))
    {n : ℝ → V3} (hn : Continuous n) (hn0 : ∀ u, n u ≠ wp)
    (hperp : ∀ u, cross (n u) (X (γ u).1 (γ u).2) = wp) :
    ∃ κ : ℝ, 0 < κ ∧ n b = (κ * sgn k) • n a := by
  have hY : Continuous fun u => X (γ u).1 (γ u).2 := hX.comp hγ
  obtain ⟨c, -, hsm, hsign⟩ :=
    rigid_normal hY (fun u => hne _ _) hn hn0 dense_univ fun u _ => hperp u
  have hflip : X (γ b).1 (γ b).2 = sgn k • X (γ a).1 (γ a).2 := by rw [hend]; exact hgam k m _
  have hpos : 0 < c b / c a := by
    rcases hsign with hp | hp
    · exact div_pos (hp b) (hp a)
    · exact div_pos_of_neg_of_neg (hp b) (hp a)
  have hca : c a ≠ 0 := by
    rcases hsign with hp | hp
    · exact (hp a).ne'
    · exact (hp a).ne
  refine ⟨c b / c a, hpos, ?_⟩
  have e : c b * sgn k = c b / c a * sgn k * c a := by field_simp
  rw [hsm b, hsm a, hflip, smul_smul, smul_smul, e]

/-- 静的な面 Ŝ のモノドロミー。 -/
theorem Shat_monodromy {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ)
    {a b : ℝ} {k m : ℤ} (hend : γ b = gam k m (γ a)) {n : ℝ → V3} (hn : Continuous n)
    (hn0 : ∀ u, n u ≠ wp) (hperp : ∀ u, cross (n u) (Xhat w₀ (γ u).1 (γ u).2) = wp) :
    ∃ κ : ℝ, 0 < κ ∧ n b = (κ * sgn k) • n a :=
  normal_monodromy_gam (continuous_Xhat h0 h1) (Xhat_ne h0 h1) (Xhat_gam h0 h1) hγ hend hn hn0 hperp

/-- 族のどの段 F_s でも、モノドロミーは同じ指標 (−1)ᵏ である。 -/
theorem stage_monodromy {w₀ ε : ℝ} {F : ℝ → ℝ → ℝ → V3} (E : NeckEversion w₀ ε (Shat w₀) F)
    (s : ℝ) {γ : ℝ → ℝ × ℝ} (hγ : Continuous γ) {a b : ℝ} {k m : ℤ}
    (hend : γ b = gam k m (γ a)) {n : ℝ → V3} (hn : Continuous n) (hn0 : ∀ u, n u ≠ wp)
    (hperp : ∀ u, cross (n u) (XF F s (γ u).1 (γ u).2) = wp) :
    ∃ κ : ℝ, 0 < κ ∧ n b = (κ * sgn k) • n a :=
  normal_monodromy_gam (continuous_XF E s) (XF_ne E s) (XF_gam E s) hγ hend hn hn0 hperp

/-! ### 閉路と首の円 -/

theorem gam_neg_one (p : ℝ × ℝ) : gam (-1) 0 p = (p.1 - 4, -p.2) := by
  have h : sgn (-1) = -1 := by rw [sgn_neg, sgn_one]
  refine Prod.ext ?_ ?_
  · simp only [gam]; push_cast; ring
  · simp only [gam, h]; push_cast; ring

/-- 閉路の w 成分。 -/
theorem loopExt_fst (p : ℝ → ℝ × ℝ) (T t : ℝ) :
    (loopExt p T t).1 =
      (1 - s₀ ((t - 2 * T) / T)) * (p t).1 + s₀ ((t - 2 * T) / T) * ((p 0).1 - 4) := by
  simp only [loopExt, Prod.fst_add, Prod.smul_fst, Prod.fst_sub, smul_eq_mul]
  ring

theorem hasDerivAt_race_g (R : Race) (t : ℝ) : HasDerivAt R.g (-(1 / R.tstar)) t := by
  have h : R.g = fun t => 1 - t / R.tstar := funext R.g_eq
  rw [h]
  have h2 := ((hasDerivAt_id t).div_const R.tstar).const_sub 1
  exact h2

/-- **亀の閉路は首の円の持ち上げを t∗ にちょうど一度横切る**。 -/
theorem loop_T_cross (R : Race) (V : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc 0 (3 * R.tstar)) :
    (∃ k : ℤ, (loopExt (fun u => (R.r * R.g u, V (R.r * R.g u))) R.tstar t).1 = 4 * (k : ℝ)) ↔
      t = R.tstar := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  constructor
  · rintro ⟨k, hk⟩
    by_cases h2 : t ≤ 2 * R.tstar
    · simp only [loopExt_of_le hT h2] at hk
      obtain ⟨hg1, hg2⟩ := abs_le.mp (R.abs_g_le ht.1 h2)
      have hrg1 : R.r * R.g t ≤ R.r := by nlinarith
      have hrg2 : -R.r ≤ R.r * R.g t := by nlinarith
      have hk0 : k = 0 := by
        have h3 : (-1 : ℝ) < k := by linarith
        have h4 : (k : ℝ) < 1 := by linarith
        have h5 : (-1 : ℤ) < k := by exact_mod_cast h3
        have h6 : k < 1 := by exact_mod_cast h4
        omega
      rw [hk0] at hk
      have hg0 : R.g t = 0 := by
        have h3 : R.r * R.g t = 0 := by simpa using hk
        exact (mul_eq_zero.mp h3).resolve_left hr0.ne'
      exact (R.g_eq_zero_iff t).mp hg0
    · exfalso
      push Not at h2
      rw [loopExt_fst] at hk
      simp only at hk
      have hσ0 : 0 ≤ s₀ ((t - 2 * R.tstar) / R.tstar) := Real.smoothTransition.nonneg _
      have hσ1 : s₀ ((t - 2 * R.tstar) / R.tstar) ≤ 1 := Real.smoothTransition.le_one _
      have hg0 : R.g 0 = 1 := by rw [R.g_eq]; simp
      have hq2 : 2 < t / R.tstar := by rw [lt_div_iff₀ hT]; linarith
      have hq3 : t / R.tstar ≤ 3 := by rw [div_le_iff₀ hT]; linarith [ht.2]
      have hgl : R.g t < -1 := by rw [R.g_eq]; linarith
      have hgu : -2 ≤ R.g t := by rw [R.g_eq]; linarith
      rw [hg0, mul_one] at hk
      generalize s₀ ((t - 2 * R.tstar) / R.tstar) = σ at hk hσ0 hσ1
      have ha1 : R.r * R.g t ≤ -R.r := by nlinarith
      have ha2 : -(2 * R.r) ≤ R.r * R.g t := by nlinarith
      have hb1 : (1 - σ) * (R.r * R.g t) ≤ (1 - σ) * (-R.r) :=
        mul_le_mul_of_nonneg_left ha1 (by linarith)
      have hb2 : (1 - σ) * (-(2 * R.r)) ≤ (1 - σ) * (R.r * R.g t) :=
        mul_le_mul_of_nonneg_left ha2 (by linarith)
      have hp1 : 0 ≤ σ * (4 - 2 * R.r) := mul_nonneg hσ0 (by linarith)
      have hp2 : 0 ≤ (1 - σ) * (4 - 3 * R.r) := mul_nonneg (by linarith) (by linarith)
      have h3 : (-1 : ℝ) < k := by nlinarith
      have h4 : (k : ℝ) < 0 := by nlinarith
      have h5 : (-1 : ℤ) < k := by exact_mod_cast h3
      have h6 : k < 0 := by exact_mod_cast h4
      omega
  · intro h
    refine ⟨0, ?_⟩
    rw [h]
    simp only [loopExt_of_le hT (by linarith : R.tstar ≤ 2 * R.tstar), R.g_tstar]
    simp

/-- **アキレスの閉路は首の円の持ち上げを t∗ にちょうど一度横切る**。 -/
theorem loop_A_cross (R : Race) (V : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc 0 (3 * R.tstar)) :
    (∃ k : ℤ, (loopExt (fun u => (R.g u, V (R.g u))) R.tstar t).1 = 4 * (k : ℝ)) ↔
      t = R.tstar := by
  have hT := R.tstar_pos
  constructor
  · rintro ⟨k, hk⟩
    by_cases h2 : t ≤ 2 * R.tstar
    · simp only [loopExt_of_le hT h2] at hk
      obtain ⟨hg1, hg2⟩ := abs_le.mp (R.abs_g_le ht.1 h2)
      have hk0 : k = 0 := by
        have h3 : (-1 : ℝ) < k := by linarith
        have h4 : (k : ℝ) < 1 := by linarith
        have h5 : (-1 : ℤ) < k := by exact_mod_cast h3
        have h6 : k < 1 := by exact_mod_cast h4
        omega
      rw [hk0] at hk
      have hg0 : R.g t = 0 := by simpa using hk
      exact (R.g_eq_zero_iff t).mp hg0
    · exfalso
      push Not at h2
      rw [loopExt_fst] at hk
      simp only at hk
      have hσ0 : 0 ≤ s₀ ((t - 2 * R.tstar) / R.tstar) := Real.smoothTransition.nonneg _
      have hσ1 : s₀ ((t - 2 * R.tstar) / R.tstar) ≤ 1 := Real.smoothTransition.le_one _
      have hg0 : R.g 0 = 1 := by rw [R.g_eq]; simp
      have hq2 : 2 < t / R.tstar := by rw [lt_div_iff₀ hT]; linarith
      have hq3 : t / R.tstar ≤ 3 := by rw [div_le_iff₀ hT]; linarith [ht.2]
      have hgl : R.g t < -1 := by rw [R.g_eq]; linarith
      have hgu : -2 ≤ R.g t := by rw [R.g_eq]; linarith
      rw [hg0] at hk
      generalize s₀ ((t - 2 * R.tstar) / R.tstar) = σ at hk hσ0 hσ1
      have hb1 : (1 - σ) * R.g t ≤ (1 - σ) * (-1) :=
        mul_le_mul_of_nonneg_left hgl.le (by linarith)
      have hb2 : (1 - σ) * (-2) ≤ (1 - σ) * R.g t :=
        mul_le_mul_of_nonneg_left hgu (by linarith)
      have h3 : (-1 : ℝ) < k := by nlinarith
      have h4 : (k : ℝ) < 0 := by nlinarith
      have h5 : (-1 : ℤ) < k := by exact_mod_cast h3
      have h6 : k < 0 := by exact_mod_cast h4
      omega
  · intro h
    refine ⟨0, ?_⟩
    rw [h]
    simp only [loopExt_of_le hT (by linarith : R.tstar ≤ 2 * R.tstar), R.g_tstar]
    simp

/-- **亀の閉路**。M の上で閉じ、終点は γ_{−1,0}（Ω の逆）による始点の像であり、首の円の持ち上げ
{w ∈ 4ℤ} を t∗ にちょうど一度、速度 −r/t∗ ≠ 0 で横切る。 -/
theorem klein_loop_T (R : Race) (n₁ : ℕ) :
    ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.r * R.g t, VtR (R.r ^ n₁) (R.r * R.g t))) ∧
      γ (3 * R.tstar) = gam (-1) 0 (γ 0) ∧ toM (γ (3 * R.tstar)) = toM (γ 0) ∧
      (∀ t ∈ Icc 0 (3 * R.tstar), (∃ k : ℤ, (γ t).1 = 4 * (k : ℝ)) ↔ t = R.tstar) ∧
      HasDerivAt (fun t => (γ t).1) (-(R.r / R.tstar)) R.tstar ∧ -(R.r / R.tstar) ≠ 0 := by
  have hT := R.tstar_pos
  have hrg : ContDiff ℝ ∞ (fun t => R.r * R.g t) := contDiff_const.mul R.contDiff_g
  have hp : ContDiff ℝ ∞ (fun u => (R.r * R.g u, VtR (R.r ^ n₁) (R.r * R.g u))) :=
    hrg.prodMk ((contDiff_VtR _).comp hrg)
  have hend : loopExt (fun u => (R.r * R.g u, VtR (R.r ^ n₁) (R.r * R.g u))) R.tstar
      (3 * R.tstar) = gam (-1) 0
        (loopExt (fun u => (R.r * R.g u, VtR (R.r ^ n₁) (R.r * R.g u))) R.tstar 0) := by
    rw [loopExt_end hT, loopExt_zero hT, gam_neg_one]
  refine ⟨_, contDiff_loopExt hp R.tstar, fun t ht => loopExt_of_le hT ht.2, hend, ?_,
    fun t ht => loop_T_cross R _ ht, ?_, ?_⟩
  · rw [hend]; exact toM_gam _ _ _
  · have h : HasDerivAt (fun t => R.r * R.g t) (R.r * (-(1 / R.tstar))) R.tstar :=
      (hasDerivAt_race_g R R.tstar).const_mul R.r
    have e : (fun t => (loopExt (fun u => (R.r * R.g u, VtR (R.r ^ n₁) (R.r * R.g u)))
        R.tstar t).1) =ᶠ[𝓝 R.tstar] fun t => R.r * R.g t := by
      filter_upwards [Iio_mem_nhds (show R.tstar < 2 * R.tstar by linarith)] with t ht
      simp only [loopExt_of_le hT (le_of_lt ht)]
    have h' := h.congr_of_eventuallyEq e
    have e2 : -(R.r / R.tstar) = R.r * (-(1 / R.tstar)) := by ring
    rw [e2]
    exact h'
  · exact neg_ne_zero.mpr (div_pos R.r_pos hT).ne'

/-- **アキレスの閉路**。M の上で閉じ、終点は γ_{−1,0} による始点の像であり、首の円の持ち上げを
t∗ にちょうど一度、速度 −1/t∗ ≠ 0 で横切る。 -/
theorem klein_loop_A (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (n₁ : ℕ) :
    ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.g t, VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t))) ∧
      γ (3 * R.tstar) = gam (-1) 0 (γ 0) ∧ toM (γ (3 * R.tstar)) = toM (γ 0) ∧
      (∀ t ∈ Icc 0 (3 * R.tstar), (∃ k : ℤ, (γ t).1 = 4 * (k : ℝ)) ↔ t = R.tstar) ∧
      HasDerivAt (fun t => (γ t).1) (-(1 / R.tstar)) R.tstar ∧ -(1 / R.tstar) ≠ 0 := by
  have hT := R.tstar_pos
  have hg := R.contDiff_g
  have hp : ContDiff ℝ ∞ (fun u => (R.g u, VaR R.r w₀ (R.r ^ n₁) n₁ (R.g u))) :=
    hg.prodMk ((contDiff_VaR R.r h0.ne' _ n₁).comp hg)
  have hend : loopExt (fun u => (R.g u, VaR R.r w₀ (R.r ^ n₁) n₁ (R.g u))) R.tstar
      (3 * R.tstar) = gam (-1) 0
        (loopExt (fun u => (R.g u, VaR R.r w₀ (R.r ^ n₁) n₁ (R.g u))) R.tstar 0) := by
    rw [loopExt_end hT, loopExt_zero hT, gam_neg_one]
  refine ⟨_, contDiff_loopExt hp R.tstar, fun t ht => loopExt_of_le hT ht.2, hend, ?_,
    fun t ht => loop_A_cross R _ ht, ?_, ?_⟩
  · rw [hend]; exact toM_gam _ _ _
  · have h := hasDerivAt_race_g R R.tstar
    have e : (fun t => (loopExt (fun u => (R.g u, VaR R.r w₀ (R.r ^ n₁) n₁ (R.g u)))
        R.tstar t).1) =ᶠ[𝓝 R.tstar] R.g := by
      filter_upwards [Iio_mem_nhds (show R.tstar < 2 * R.tstar by linarith)] with t ht
      simp only [loopExt_of_le hT (le_of_lt ht)]
    exact h.congr_of_eventuallyEq e
  · exact neg_ne_zero.mpr (one_div_pos.mpr hT).ne'

/-! ### ラベルの交換の時刻 -/

section LabelTime

variable {R : Race} {w₀ : ℝ} {n₁ : ℕ} {F : ℝ → ℝ → ℝ → V3}

theorem abs_sub_tstar_eq (R : Race) (t : ℝ) : |t - R.tstar| = R.tstar * |R.g t| := by
  have hT := R.tstar_pos
  have e : t - R.tstar = -(R.tstar * R.g t) := by
    rw [R.g_eq]; field_simp; ring
  rw [e, abs_neg, abs_mul, abs_of_pos hT]

/-- 亀のラベルが 0 になる時刻は首の中にある。 -/
theorem DynamicEffects.zero_T_in_neck (E : DynamicEffects R w₀ n₁ F) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar))
    (hz : side (dynT R w₀ F (VtR (R.r ^ n₁)) t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t) = 0) :
    |R.r * R.g t| < R.r ^ n₁ := by
  rw [abs_lt]
  constructor
  · by_contra hcon
    push Not at hcon
    have := E.label_T_left t ht hcon
    simp only [Back] at this
    linarith
  · by_contra hcon
    push Not at hcon
    have := E.label_T_right t ht hcon
    simp only [Front] at this
    linarith

/-- アキレスのラベルが 0 になる時刻は首の中にある。 -/
theorem DynamicEffects.zero_A_in_neck (E : DynamicEffects R w₀ n₁ F) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar))
    (hz : side (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
      (-dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) = 0) :
    |R.g t| < R.r ^ n₁ := by
  rw [abs_lt]
  constructor
  · by_contra hcon
    push Not at hcon
    have := E.label_A_left t ht hcon
    simp only [Front] at this
    linarith
  · by_contra hcon
    push Not at hcon
    have := E.label_A_right t ht hcon
    simp only [Back] at this
    linarith

/-- 亀のラベルの交換の時刻：r |t − t∗| < t∗ rⁿ¹。 -/
theorem DynamicEffects.zero_T_time (E : DynamicEffects R w₀ n₁ F) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar))
    (hz : side (dynT R w₀ F (VtR (R.r ^ n₁)) t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t) = 0) :
    R.r * |t - R.tstar| < R.tstar * R.r ^ n₁ := by
  have h := E.zero_T_in_neck ht hz
  rw [abs_mul, abs_of_pos R.r_pos] at h
  have hT := R.tstar_pos
  rw [abs_sub_tstar_eq]
  nlinarith

/-- アキレスのラベルの交換の時刻：|t − t∗| < t∗ rⁿ¹。 -/
theorem DynamicEffects.zero_A_time (E : DynamicEffects R w₀ n₁ F) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar))
    (hz : side (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
      (-dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) = 0) :
    |t - R.tstar| < R.tstar * R.r ^ n₁ := by
  have h := E.zero_A_in_neck ht hz
  rw [abs_sub_tstar_eq]
  exact mul_lt_mul_of_pos_left h R.tstar_pos

end LabelTime

/-- **亀のラベルの交換の時刻は t∗ に収束する**。 -/
theorem label_zero_T_tendsto (R : Race) {F : ℕ → ℝ → ℝ → ℝ → V3}
    (hF : ∀ n : ℕ, 1 ≤ n → DynamicEffects R (R.r ^ n) n (F n)) {τ : ℕ → ℝ}
    (hτ : ∀ n : ℕ, 1 ≤ n → τ n ∈ Icc 0 (2 * R.tstar) ∧
      side (dynT R (R.r ^ n) (F n) (VtR (R.r ^ n)) (τ n))
        (dynNT R (R.r ^ n) (F n) (VtR (R.r ^ n)) (τ n)) = 0) :
    Tendsto τ atTop (𝓝 R.tstar) := by
  have hr0 := R.r_pos
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le R.r_lt_one
  have hb : Tendsto (fun n : ℕ => R.tstar / R.r * R.r ^ n) atTop (𝓝 0) := by
    have h := hpow.const_mul (R.tstar / R.r)
    simpa using h
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_ hb
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨ht, hz⟩ := hτ n hn
  have h := (hF n hn).zero_T_time ht hz
  rw [Real.dist_eq, div_mul_eq_mul_div, le_div_iff₀ hr0]
  linarith

/-- **アキレスのラベルの交換の時刻は t∗ に収束する**。 -/
theorem label_zero_A_tendsto (R : Race) {F : ℕ → ℝ → ℝ → ℝ → V3}
    (hF : ∀ n : ℕ, 1 ≤ n → DynamicEffects R (R.r ^ n) n (F n)) {τ : ℕ → ℝ}
    (hτ : ∀ n : ℕ, 1 ≤ n → τ n ∈ Icc 0 (2 * R.tstar) ∧
      side (dynA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n) (τ n))
        (-dynNA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n) (τ n)) = 0) :
    Tendsto τ atTop (𝓝 R.tstar) := by
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one R.r_pos.le R.r_lt_one
  have hb : Tendsto (fun n : ℕ => R.tstar * R.r ^ n) atTop (𝓝 0) := by
    have h := hpow.const_mul R.tstar
    simpa using h
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) ?_ hb
  filter_upwards [eventually_ge_atTop 1] with n hn
  obtain ⟨ht, hz⟩ := hτ n hn
  have h := (hF n hn).zero_A_time ht hz
  rw [Real.dist_eq]
  exact h.le

/-! ### 静的な面でのラベル：t∗ にはまだ交換していない -/

section Static

variable (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (n₁ : ℕ)

include h0 h1 in
/-- 静的な面では、t∗ に亀はまだ表に、アキレスはまだ裏にいる（中央円の側は正）。 -/
theorem static_label_tstar :
    Front (R.runT (Shat w₀) (VtR (R.r ^ n₁)) R.tstar)
        (Xhat w₀ (R.r * R.g R.tstar) (VtR (R.r ^ n₁) (R.r * R.g R.tstar))) ∧
      Back (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) R.tstar)
        (-Xhat w₀ (R.g R.tstar) (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g R.tstar))) := by
  have hS : ∀ u, Shat w₀ 0 u = Sig w₀ 0 u := fun u => Shat_neck h0 h1 (by simp) u
  constructor
  · simp only [Front, Race.runT, R.g_tstar, mul_zero]
    rw [hS]
    exact side_middle_pos h0 h1 _
  · simp only [Back, Race.runA, R.g_tstar]
    rw [hS, side_neg]
    have := side_middle_pos h0 h1 (VaR R.r w₀ (R.r ^ n₁) n₁ 0)
    linarith

include h0 h1 in
/-- 静的な面では、t∗ の後の首の中に亀のラベルの零点がある。 -/
theorem static_zero_T (hn : 1 ≤ n₁) (hc : w₀ ≤ R.r ^ n₁) :
    ∃ t ∈ Ioo R.tstar (2 * R.tstar), |R.r * R.g t| < R.r ^ n₁ ∧
      side (R.runT (Shat w₀) (VtR (R.r ^ n₁)) t)
        (Xhat w₀ (R.r * R.g t) (VtR (R.r ^ n₁) (R.r * R.g t))) = 0 := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  have P := klein_passage R h0 h1 n₁ hc
  have hpow : R.r ^ n₁ ≤ R.r := pow_le_of_le_one hr0.le R.r_lt_one.le (by omega)
  have hrg : Continuous (fun t => R.r * R.g t) := continuous_const.mul R.continuous_g
  have hcont : Continuous (fun t => side (R.runT (Shat w₀) (VtR (R.r ^ n₁)) t)
      (Xhat w₀ (R.r * R.g t) (VtR (R.r ^ n₁) (R.r * R.g t)))) := by
    have h := continuous_side.comp (P.smooth_T.continuous.prodMk
      ((continuous_Xhat h0 h1).comp
        (hrg.prodMk ((contDiff_VtR (R.r ^ n₁)).continuous.comp hrg))))
    exact h
  have hg2 : R.g (2 * R.tstar) = -1 := by rw [R.g_eq]; field_simp; ring
  have ha := (static_label_tstar R h0 h1 n₁).1
  have hb : side (R.runT (Shat w₀) (VtR (R.r ^ n₁)) (2 * R.tstar))
      (Xhat w₀ (R.r * R.g (2 * R.tstar)) (VtR (R.r ^ n₁) (R.r * R.g (2 * R.tstar)))) < 0 :=
    P.side_T_left (2 * R.tstar) ⟨by linarith, le_rfl⟩ (by rw [hg2]; linarith)
  simp only [Front] at ha
  have hivt := intermediate_value_Ioo' (by linarith : R.tstar ≤ 2 * R.tstar) hcont.continuousOn
  obtain ⟨t, ht, hval⟩ := hivt (show (0 : ℝ) ∈ Ioo _ _ from ⟨hb, ha⟩)
  refine ⟨t, ht, ?_, hval⟩
  have htI : t ∈ Icc 0 (2 * R.tstar) := ⟨by linarith [ht.1], ht.2.le⟩
  rw [abs_lt]
  constructor
  · by_contra hcon
    push Not at hcon
    have := P.side_T_left t htI hcon
    simp only [Back] at this
    linarith
  · by_contra hcon
    push Not at hcon
    have := P.side_T_right t htI hcon
    simp only [Front] at this
    linarith

include h0 h1 in
/-- 静的な面では、t∗ の後の首の中にアキレスのラベルの零点がある。 -/
theorem static_zero_A (hc : w₀ ≤ R.r ^ n₁) :
    ∃ t ∈ Ioo R.tstar (2 * R.tstar), |R.g t| < R.r ^ n₁ ∧
      side (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) t)
        (-Xhat w₀ (R.g t) (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t))) = 0 := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  have P := klein_passage R h0 h1 n₁ hc
  have hpow : R.r ^ n₁ ≤ 1 := pow_le_one₀ hr0.le R.r_lt_one.le
  have hg := R.continuous_g
  have hcont : Continuous (fun t => side (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) t)
      (-Xhat w₀ (R.g t) (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t)))) := by
    have h := continuous_side.comp (P.smooth_A.continuous.prodMk
      ((continuous_Xhat h0 h1).comp
        (hg.prodMk ((contDiff_VaR R.r h0.ne' (R.r ^ n₁) n₁).continuous.comp hg))).neg)
    exact h
  have hg2 : R.g (2 * R.tstar) = -1 := by rw [R.g_eq]; field_simp; ring
  have ha := (static_label_tstar R h0 h1 n₁).2
  have hb : 0 < side (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) (2 * R.tstar))
      (-Xhat w₀ (R.g (2 * R.tstar)) (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g (2 * R.tstar)))) :=
    P.side_A_left (2 * R.tstar) ⟨by linarith, le_rfl⟩ (by rw [hg2]; linarith)
  simp only [Back] at ha
  have hivt := intermediate_value_Ioo (by linarith : R.tstar ≤ 2 * R.tstar) hcont.continuousOn
  obtain ⟨t, ht, hval⟩ := hivt (show (0 : ℝ) ∈ Ioo _ _ from ⟨ha, hb⟩)
  refine ⟨t, ht, ?_, hval⟩
  have htI : t ∈ Icc 0 (2 * R.tstar) := ⟨by linarith [ht.1], ht.2.le⟩
  rw [abs_lt]
  constructor
  · by_contra hcon
    push Not at hcon
    have := P.side_A_left t htI hcon
    simp only [Front] at this
    linarith
  · by_contra hcon
    push Not at hcon
    have := P.side_A_right t htI hcon
    simp only [Back] at this
    linarith

end Static

/-! ### ホーン：有限の部分は正確に含まれ、全体は含まれない -/

section Horns

/-- 族のどの段も、右のホーンの 1 ≤ X ≤ 1/w₀ の部分の反転像を正確に含む。 -/
theorem stage_horn_right {w₀ ε : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) {F : ℝ → ℝ → ℝ → V3}
    (E : NeckEversion w₀ ε (Shat w₀) F) (s : ℝ) {X : ℝ} (hX1 : 1 ≤ X) (hX : X ≤ 1 / w₀)
    (v : ℝ) : F s (1 / X) v = inv3 (H X v) := by
  have hXpos : 0 < X := by linarith
  have h2 : X * w₀ ≤ 1 := (le_div_iff₀ h0).mp hX
  have hw : w₀ ≤ 1 / X := by rw [le_div_iff₀ hXpos]; linarith
  have hw1 : 1 / X ≤ 1 := by rw [div_le_one hXpos]; exact hX1
  rw [F_horn_right h0 h1 E s hw hw1 v]
  have h := inv3_H (w := 1 / X) (one_div_pos.mpr hXpos).ne' v
  rw [one_div_one_div] at h
  exact h.symm

/-- 族のどの段も、左のホーンの −1/w₀ ≤ X ≤ −1 の部分の反転像を正確に含む。 -/
theorem stage_horn_left {w₀ ε : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) {F : ℝ → ℝ → ℝ → V3}
    (E : NeckEversion w₀ ε (Shat w₀) F) (s : ℝ) {X : ℝ} (hX1 : X ≤ -1) (hX : -(1 / w₀) ≤ X)
    (v : ℝ) : F s (1 / X) v = inv3 (H X (π - v)) := by
  have hXneg : X < 0 := by linarith
  have h2 : -X * w₀ ≤ 1 := (le_div_iff₀ h0).mp (by linarith)
  have hw1 : -1 ≤ 1 / X := by rw [le_div_iff_of_neg hXneg]; linarith
  have hw : 1 / X ≤ -w₀ := by rw [div_le_iff_of_neg hXneg]; linarith
  rw [F_horn_left h0 h1 E s hw1 hw v]
  have h := inv3_H (w := 1 / X) (one_div_neg.mpr hXneg).ne (π - v)
  rw [one_div_one_div] at h
  exact h.symm

/-- **ホーンの汲み尽くし**。首の幅 rⁿ の裏返しの列について、右のホーンの各点 H(X, v)（X ≥ 1）と
左のホーンの各点 H(−X, v) の反転像は、十分大きい n のすべてで、どの段の面の上にもある。 -/
theorem horn_exhaustion (R : Race) {F : ℕ → ℝ → ℝ → ℝ → V3} {ε : ℕ → ℝ}
    (hF : ∀ n : ℕ, 1 ≤ n → NeckEversion (R.r ^ n) (ε n) (Shat (R.r ^ n)) (F n)) {X : ℝ}
    (hX : 1 ≤ X) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s v : ℝ,
      F n s (1 / X) v = inv3 (H X v) ∧ F n s (1 / -X) v = inv3 (H (-X) (π - v)) := by
  have hXpos : 0 < X := by linarith
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hXpos) R.r_lt_one
  refine ⟨max N₀ 1, fun n hn s v => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have h0 : 0 < R.r ^ n := pow_pos R.r_pos n
  have h1 : R.r ^ n < 1 := R.pow_lt_one hn1
  have hle : R.r ^ n ≤ R.r ^ N₀ := pow_le_pow_of_le_one R.r_pos.le R.r_lt_one.le hn0
  have hlt : R.r ^ n < 1 / X := lt_of_le_of_lt hle hN₀
  have h3 : R.r ^ n * X < 1 := (lt_div_iff₀ hXpos).mp hlt
  have hXle : X ≤ 1 / R.r ^ n := by rw [le_div_iff₀ h0]; linarith
  refine ⟨stage_horn_right h0 h1 (hF n hn1) s hX hXle v,
    stage_horn_left h0 h1 (hF n hn1) s (by linarith) (by linarith) v⟩

/-- **非有界なホーンは M の連続像に入らない**（コンパクト性）。 -/
theorem horn_not_in_compact_image {f : KleinM → V3} (hf : Continuous f) :
    ¬ ∀ X v : ℝ, 1 ≤ X → H X v ∈ range f := by
  intro h
  obtain ⟨C, hC⟩ := (isCompact_range hf).bddAbove_image (f := fun q : V3 => q.1)
    continuous_fst.continuousOn
  have hmem : (H (max 1 (C + 1)) 0).1 ∈ (fun q : V3 => q.1) '' range f :=
    ⟨_, h _ 0 (le_max_left _ _), rfl⟩
  have h2 := hC hmem
  simp only [H] at h2
  linarith [le_max_right 1 (C + 1)]

/-- **反転したホーンの全体を含む M の連続像は ℘ を通る**。 -/
theorem inverted_horn_forces_wp {f : KleinM → V3} (hf : Continuous f)
    (h : ∀ w v : ℝ, 0 < w → w ≤ 1 → G w v ∈ range f) : wp ∈ range f := by
  have hcl : IsClosed (range f) := (isCompact_range hf).isClosed
  have hG : Continuous (fun w : ℝ => G w 0) :=
    contDiff_G.continuous.comp (continuous_id.prodMk continuous_const)
  have hlim : Tendsto (fun n : ℕ => G (1 / ((n : ℝ) + 1)) 0) atTop (𝓝 wp) := by
    have h3 := (hG.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    rw [G_zero] at h3
    exact h3
  refine hcl.mem_of_tendsto hlim (Eventually.of_forall fun n => h _ 0 (by positivity) ?_)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_one (by positivity)]
  linarith

/-- 静的な面 Ŝ（M からの写像）は反転したホーンの全体を含まない（Ŝ は ℘ を通らないので）。 -/
theorem ShatM_misses_horn {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) :
    ¬ ∀ w v : ℝ, 0 < w → w ≤ 1 → G w v ∈ range (ShatM w₀) := by
  intro h
  obtain ⟨x, hx⟩ := inverted_horn_forces_wp (continuous_ShatM h0 h1) h
  obtain ⟨p, rfl⟩ := toM_surjective x
  exact Shat_ne_wp h0 h1 p.1 p.2 hx

end Horns

/-! ### 枠の法則 E：裏返しの終わりの首の枠と、窓の前後の走者の枠 -/

section Frame

variable {w₀ ε : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) {F : ℝ → ℝ → ℝ → V3}
  (E : NeckEversion w₀ ε (Shat w₀) F)

include h0 h1 E in
/-- **裏返しの終わりの首は、Ŝ の首の枠つきの像を E で写したものである**：s ≥ 1、|w| < 1 で
(F_s(p), X_{F,s}(p)) = E(Ŝ(φp), X̂(φp))、φ(w, v) = (−w, π − v)。 -/
theorem stage_frame_finish {s : ℝ} (hs : 1 ≤ s) {w : ℝ} (hw : |w| < 1) (v : ℝ) :
    (F s w v, XF F s w v) = Everse (Shat w₀ (-w) (π - v), Xhat w₀ (-w) (π - v)) := by
  rw [E.finish s w v hs hw.le, XF_of_finish h0 h1 E hs hw v]
  rfl

include h0 h1 E in
/-- 裏返しの終わりの首では、外在的な側は φ で写した点での側の符号を変えたものである。 -/
theorem side_stage_finish {s : ℝ} (hs : 1 ≤ s) {w : ℝ} (hw : |w| < 1) (v : ℝ) :
    side (F s w v) (XF F s w v) = -side (Shat w₀ (-w) (π - v)) (Xhat w₀ (-w) (π - v)) := by
  rw [E.finish s w v hs hw.le, XF_of_finish h0 h1 E hs hw v, side_neg_pos]

include E in
/-- 裏返しの始まりの枠は静的な枠である。 -/
theorem stage_frame_start {s : ℝ} (hs : s ≤ 0) (w v : ℝ) :
    (F s w v, XF F s w v) = (Shat w₀ w v, Xhat w₀ w v) := by
  rw [E.start s w v hs, XF_of_start E hs w v]

include h0 h1 in
/-- −Ŝ∘φ の法線は X̂∘φ である（連鎖律）。 -/
theorem normalOf_negphi (w v : ℝ) :
    normalOf (fun w' v' => -(Shat w₀ (-w') (π - v'))) w v = Xhat w₀ (-w) (π - v) := by
  have hd := differentiableAt_Shat h0 h1
  simp only [normalOf, Xhat]
  have hv : deriv (fun v' => -(Shat w₀ (-w) (π - v'))) v =
      deriv (fun v => Shat w₀ (-w) v) (π - v) := by
    have h := (differentiableAt_partial_v (hd (-w, π - v))).hasDerivAt
    have hl : HasDerivAt (fun v' : ℝ => π - v') (-1) v := (hasDerivAt_id v).const_sub π
    have h2 : HasDerivAt (fun v' => -(Shat w₀ (-w) (π - v')))
        (-((-1 : ℝ) • deriv (fun v => Shat w₀ (-w) v) (π - v))) v := (h.scomp v hl).neg
    rw [h2.deriv, neg_one_smul, neg_neg]
  have hw' : deriv (fun w' => -(Shat w₀ (-w') (π - v))) w =
      deriv (fun w => Shat w₀ w (π - v)) (-w) := by
    have h := (differentiableAt_partial_w (hd (-w, π - v))).hasDerivAt
    have hl : HasDerivAt (fun w' : ℝ => -w') (-1) w := (hasDerivAt_id w).neg
    have h2 : HasDerivAt (fun w' => -(Shat w₀ (-w') (π - v)))
        (-((-1 : ℝ) • deriv (fun w => Shat w₀ w (π - v)) (-w))) w := (h.scomp w hl).neg
    rw [h2.deriv, neg_one_smul, neg_neg]
  rw [hv, hw']

include h0 h1 in
/-- 岸では X̂(φp) = X̂(p)（`Shat_E_fixed` の微分）。 -/
theorem Xhat_E_fixed {w : ℝ} (hw : w₀ * (4 / 5) < |w|) (hw1 : |w| < 1) (v : ℝ) :
    Xhat w₀ (-w) (π - v) = Xhat w₀ w v := by
  rw [← normalOf_negphi h0 h1 w v]
  have hopen : IsOpen {p : ℝ × ℝ | w₀ * (4 / 5) < |p.1| ∧ |p.1| < 1} :=
    (isOpen_lt continuous_const (continuous_abs.comp continuous_fst)).inter
      (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const)
  have h : (fun p : ℝ × ℝ => -(Shat w₀ (-p.1) (π - p.2))) =ᶠ[𝓝 (w, v)]
      fun p => Shat w₀ p.1 p.2 := by
    filter_upwards [hopen.mem_nhds
      (show (w, v) ∈ {p : ℝ × ℝ | w₀ * (4 / 5) < |p.1| ∧ |p.1| < 1} from ⟨hw, hw1⟩)] with p hp
    exact Shat_E_fixed h0 h1 hp.1 hp.2.le p.2
  exact normalOf_congr (F' := fun w' v' => -(Shat w₀ (-w') (π - v'))) (F := Shat w₀)
    (q := (w, v)) h

include h0 h1 in
/-- **岸では静的な面がすでに枠の法則 E を満たす**：4w₀/5 < |w| < 1 で
(Ŝ(p), X̂(p)) = E(Ŝ(φp), X̂(φp))。 -/
theorem static_frame_shore {w : ℝ} (hw : w₀ * (4 / 5) < |w|) (hw1 : |w| < 1) (v : ℝ) :
    (Shat w₀ w v, Xhat w₀ w v) = Everse (Shat w₀ (-w) (π - v), Xhat w₀ (-w) (π - v)) := by
  rw [Xhat_E_fixed h0 h1 hw hw1 v]
  simp only [Everse]
  rw [Shat_E_fixed h0 h1 hw hw1.le v]

end Frame

section RunnerFrame

variable {R : Race} {w₀ ε : ℝ} {n₁ : ℕ} {F : ℝ → ℝ → ℝ → V3}
  (P : DynamicPassage R w₀ (R.r ^ n₁) ε n₁ (Shat w₀) (Xhat w₀) F (VtR (R.r ^ n₁))
    (VaR R.r w₀ (R.r ^ n₁) n₁))

include P in
/-- 窓の前：動く面の上の亀の枠（位置と動く面の法線）は静的な枠である。 -/
theorem DynamicPassage.frame_before_T (h0 : 0 < w₀) {t : ℝ} (ht : t ≤ t1 R w₀) :
    (dynT R w₀ F (VtR (R.r ^ n₁)) t, dynNT R w₀ F (VtR (R.r ^ n₁)) t) =
      (R.runT (Shat w₀) (VtR (R.r ^ n₁)) t,
        Xhat w₀ (R.r * R.g t) (VtR (R.r ^ n₁) (R.r * R.g t))) := by
  rw [(P.static_before t ht).1]
  simp only [dynNT]
  rw [XF_of_start P.eversion (sched_le_zero h0 R ht)]

include P in
/-- 窓の前：動く面の上のアキレスの枠は静的な枠である。 -/
theorem DynamicPassage.frame_before_A (h0 : 0 < w₀) {t : ℝ} (ht : t ≤ t1 R w₀) :
    (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t, dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) =
      (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) t,
        Xhat w₀ (R.g t) (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t))) := by
  rw [(P.static_before t ht).2]
  simp only [dynNA]
  rw [XF_of_start P.eversion (sched_le_zero h0 R ht)]

include P in
/-- **窓の後の亀の枠は、鏡の時刻 2t∗ − t の静的な枠を E で写したものである**。 -/
theorem DynamicPassage.frame_after_T (h0 : 0 < w₀) (h1 : w₀ < 1) (hc : w₀ ≤ R.r ^ n₁) {t : ℝ}
    (ht2 : t2 R w₀ ≤ t) (ht : t ≤ 2 * R.tstar) :
    (dynT R w₀ F (VtR (R.r ^ n₁)) t, dynNT R w₀ F (VtR (R.r ^ n₁)) t) =
      Everse (R.runT (Shat w₀) (VtR (R.r ^ n₁)) (2 * R.tstar - t),
        Xhat w₀ (R.r * R.g (2 * R.tstar - t))
          (VtR (R.r ^ n₁) (R.r * R.g (2 * R.tstar - t)))) := by
  have hs := sched_ge_one h0 R ht2
  have ht0 : 0 ≤ t := by linarith [t1_pos R h1, t1_lt_tstar R h0, tstar_lt_t2 R h0]
  have hcp : 0 < R.r ^ n₁ := lt_of_lt_of_le h0 hc
  have hw : |R.r * R.g t| < 1 := by
    rw [abs_mul, abs_of_pos R.r_pos]
    have := R.abs_g_le ht0 ht
    nlinarith [R.r_pos, R.r_lt_one, abs_nonneg (R.g t)]
  have e2 : dynNT R w₀ F (VtR (R.r ^ n₁)) t =
      Xhat w₀ (R.r * R.g (2 * R.tstar - t)) (VtR (R.r ^ n₁) (R.r * R.g (2 * R.tstar - t))) := by
    simp only [dynNT]
    rw [XF_of_finish h0 h1 P.eversion hs hw, R.g_reflect, mul_neg, VtR_neg hcp]
    have e : π - VtR (R.r ^ n₁) (R.r * R.g t) =
        (-π - VtR (R.r ^ n₁) (R.r * R.g t)) + 2 * π := by ring
    rw [e, Xhat_periodic h0 h1]
  rw [(P.static_after t ht2 ht).1, e2]
  rfl

include P in
/-- **窓の後のアキレスの枠は、鏡の時刻 2t∗ − t の静的な枠を E で写したものである**。
t = 2t∗ では w = −1 が首の帯の境界にあるので、法線の等式は連続性で延ばす。 -/
theorem DynamicPassage.frame_after_A (h0 : 0 < w₀) (h1 : w₀ < 1) (hc : w₀ ≤ R.r ^ n₁) {t : ℝ}
    (ht2 : t2 R w₀ ≤ t) (ht : t ≤ 2 * R.tstar) :
    (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t, dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) =
      Everse (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) (2 * R.tstar - t),
        Xhat w₀ (R.g (2 * R.tstar - t))
          (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g (2 * R.tstar - t)))) := by
  have hT := R.tstar_pos
  have hcp : 0 < R.r ^ n₁ := lt_of_lt_of_le h0 hc
  have key : ∀ u : ℝ, t2 R w₀ ≤ u → u < 2 * R.tstar →
      dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) u =
        Xhat w₀ (R.g (2 * R.tstar - u)) (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g (2 * R.tstar - u))) := by
    intro u hu2 hu
    have hs := sched_ge_one h0 R hu2
    have hu' : R.tstar < u := lt_of_lt_of_le (tstar_lt_t2 R h0) hu2
    have hw : |R.g u| < 1 := by
      rw [R.g_eq, abs_lt]
      have hq1 : 1 < u / R.tstar := by rw [lt_div_iff₀ hT]; linarith
      have hq2 : u / R.tstar < 2 := by rw [div_lt_iff₀ hT]; linarith
      constructor <;> linarith
    simp only [dynNA]
    rw [XF_of_finish h0 h1 P.eversion hs hw, R.g_reflect, VaR_neg hcp]
    have e : π - VaR R.r w₀ (R.r ^ n₁) n₁ (R.g u) =
        (π + 4 * π * n₁ - VaR R.r w₀ (R.r ^ n₁) n₁ (R.g u)) +
          (((-(2 * (n₁ : ℤ))) : ℤ) : ℝ) * (2 * π) := by
      push_cast; ring
    rw [e, periodic_int_curried (Xhat_periodic h0 h1)]
  have e2 : dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t =
      Xhat w₀ (R.g (2 * R.tstar - t)) (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g (2 * R.tstar - t))) := by
    rcases lt_or_eq_of_le ht with hlt | heq
    · exact key t ht2 hlt
    · have hc1 : Continuous (dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁)) :=
        continuous_dynNA R h0 n₁ P.eversion
      have hg' : Continuous (fun u : ℝ => R.g (2 * R.tstar - u)) :=
        R.continuous_g.comp (continuous_const.sub continuous_id)
      have hc2 : Continuous (fun u : ℝ => Xhat w₀ (R.g (2 * R.tstar - u))
          (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g (2 * R.tstar - u)))) := by
        have h := (continuous_Xhat h0 h1).comp
          (hg'.prodMk ((contDiff_VaR R.r h0.ne' (R.r ^ n₁) n₁).continuous.comp hg'))
        exact h
      have hcl := isClosed_eq hc1 hc2
      have hlt2 : t2 R w₀ < 2 * R.tstar := by simp only [t2]; nlinarith
      have hmem : 2 * R.tstar ∈ closure (Ico (t2 R w₀) (2 * R.tstar)) := by
        rw [closure_Ico hlt2.ne]
        exact ⟨hlt2.le, le_rfl⟩
      have h3 := hcl.closure_subset_iff.mpr (fun u hu => key u hu.1 hu.2) hmem
      rw [heq]
      exact h3
  rw [(P.static_after t ht2 ht).2, e2]
  rfl

include P in
/-- 窓の後の亀のラベルは、鏡の時刻の静的なラベルの符号を変えたものである。 -/
theorem DynamicPassage.label_after_T (h0 : 0 < w₀) (h1 : w₀ < 1) (hc : w₀ ≤ R.r ^ n₁) {t : ℝ}
    (ht2 : t2 R w₀ ≤ t) (ht : t ≤ 2 * R.tstar) :
    side (dynT R w₀ F (VtR (R.r ^ n₁)) t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t) =
      -side (R.runT (Shat w₀) (VtR (R.r ^ n₁)) (2 * R.tstar - t))
        (Xhat w₀ (R.r * R.g (2 * R.tstar - t))
          (VtR (R.r ^ n₁) (R.r * R.g (2 * R.tstar - t)))) := by
  have h := P.frame_after_T h0 h1 hc ht2 ht
  simp only [Everse, Prod.mk.injEq] at h
  rw [h.1, h.2, side_neg_pos]

include P in
/-- 窓の後のアキレスのラベルは、鏡の時刻の静的なラベルの符号を変えたものである。 -/
theorem DynamicPassage.label_after_A (h0 : 0 < w₀) (h1 : w₀ < 1) (hc : w₀ ≤ R.r ^ n₁) {t : ℝ}
    (ht2 : t2 R w₀ ≤ t) (ht : t ≤ 2 * R.tstar) :
    side (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
        (-dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) =
      -side (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) (2 * R.tstar - t))
        (-Xhat w₀ (R.g (2 * R.tstar - t))
          (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g (2 * R.tstar - t)))) := by
  have h := P.frame_after_A h0 h1 hc ht2 ht
  simp only [Everse, Prod.mk.injEq] at h
  rw [h.1, h.2, side_neg_pos]

end RunnerFrame

/-! ### 無限捻転：アキレスの角度 -/

/-- **アキレスの角度**。k ≤ n₁ のゼノンの段階の点 w = rᵏ では 2πk（k 回転）であり、首の中央 w = 0 では
π/2 + 2πn₁ である。 -/
theorem twist_at_step (R : Race) {n₁ k : ℕ} (hk : k ≤ n₁) :
    VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ (R.r ^ k) = k * (2 * π) := by
  have hr0 := R.r_pos
  have hc : 0 < R.r ^ n₁ := pow_pos hr0 n₁
  have hle : R.r ^ n₁ ≤ R.r ^ k := pow_le_pow_of_le_one hr0.le R.r_lt_one.le hk
  have hsq : (R.r ^ n₁) ^ 2 / 2 ≤ (R.r ^ k) ^ 2 := by nlinarith [pow_pos hr0 k]
  simp only [VaR, ell_of_ge hc hle]
  rw [thetaSm_of hc.ne' hsq, theta_pow hr0 R.r_lt_one]
  ring

theorem twist_at_centre (R : Race) (n₁ : ℕ) :
    VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ 0 = π / 2 + n₁ * (2 * π) :=
  VaR_zero (pow_pos R.r_pos n₁) n₁

/-- **無限捻転**：首の中央でのアキレスの角度は、段階数 n → ∞ で発散する。 -/
theorem twist_tendsto (R : Race) :
    Tendsto (fun n : ℕ => VaR R.r (R.r ^ n) (R.r ^ n) n 0) atTop atTop := by
  have h : (fun n : ℕ => VaR R.r (R.r ^ n) (R.r ^ n) n 0) =
      fun n : ℕ => π / 2 + (n : ℝ) * (2 * π) := funext fun n => twist_at_centre R n
  rw [h]
  exact tendsto_atTop_add_const_left _ _
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity))

/-! ### 動く面の上のモノドロミー：裏返しの途中でも、閉路に沿って運んだ側は反転して戻る -/

section DynMonodromy

variable {w₀ ε : ℝ} {F : ℝ → ℝ → ℝ → V3} (E : NeckEversion w₀ ε (Shat w₀) F)

include E in
/-- **動く面の上のモノドロミー**。段 σ(u) が連続に変わる間、道 γ に沿って、動く面 F_{σ(u)} の法線に
平行な連続で消えない法線 n を運ぶ。γ の終点が γ_{k,m}(始点) で、始点が首の動く部分の外にあれば、
n は (−1)ᵏ の正の倍で戻る。 -/
theorem dynamic_monodromy (h1 : w₀ < 1) {σ : ℝ → ℝ} (hσ : Continuous σ) {γ : ℝ → ℝ × ℝ}
    (hγ : Continuous γ) {a b : ℝ} {k m : ℤ} (hend : γ b = gam k m (γ a))
    (hbase : w₀ * (9 / 10) < |(γ a).1|) (hbase2 : |(γ a).1| < 2) {n : ℝ → V3}
    (hn : Continuous n) (hn0 : ∀ u, n u ≠ wp)
    (hperp : ∀ u, cross (n u) (XF F (σ u) (γ u).1 (γ u).2) = wp) :
    ∃ κ : ℝ, 0 < κ ∧ n b = (κ * sgn k) • n a := by
  have hY : Continuous fun u => XF F (σ u) (γ u).1 (γ u).2 := by
    have h := (continuous_XF_joint E).comp (hσ.prodMk hγ)
    exact h
  obtain ⟨c, -, hsm, hsign⟩ :=
    rigid_normal hY (fun u => XF_ne E _ _ _) hn hn0 dense_univ fun u _ => hperp u
  have hflip : XF F (σ b) (γ b).1 (γ b).2 = sgn k • XF F (σ a) (γ a).1 (γ a).2 := by
    rw [hend, XF_gam E (σ b) k m (γ a), XF_of_shore h1 E (σ b) hbase hbase2,
      XF_of_shore h1 E (σ a) hbase hbase2]
  have hpos : 0 < c b / c a := by
    rcases hsign with hp | hp
    · exact div_pos (hp b) (hp a)
    · exact div_pos_of_neg_of_neg (hp b) (hp a)
  have hca : c a ≠ 0 := by
    rcases hsign with hp | hp
    · exact (hp a).ne'
    · exact (hp a).ne
  refine ⟨c b / c a, hpos, ?_⟩
  have e : c b * sgn k = c b / c a * sgn k * c a := by field_simp
  rw [hsm b, hsm a, hflip, smul_smul, smul_smul, e]

include E in
/-- **亀の閉路の上の、動く面のモノドロミー**。競走の間は段 sched(t) の面の上を歩き（そこでの法線は
`dynNT`）、その後も段を sched(t) のまま閉路を閉じる。運んだ側は反転して戻る。 -/
theorem dynamic_loop_T (R : Race) (h0 : 0 < w₀) (h1 : w₀ < 1) {n₁ : ℕ} (hn : 1 ≤ n₁)
    (hc : w₀ ≤ R.r ^ n₁) :
    ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.r * R.g t, VtR (R.r ^ n₁) (R.r * R.g t))) ∧
      toM (γ (3 * R.tstar)) = toM (γ 0) ∧
      (∀ t ∈ Icc 0 (2 * R.tstar),
        XF F (sched R w₀ t) (γ t).1 (γ t).2 = dynNT R w₀ F (VtR (R.r ^ n₁)) t) ∧
      (∀ n : ℝ → V3, Continuous n → (∀ u, n u ≠ wp) →
        (∀ u, cross (n u) (XF F (sched R w₀ u) (γ u).1 (γ u).2) = wp) →
        ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0)) := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  obtain ⟨γ, hsm, hγ, hend, hM, -, -, -⟩ := klein_loop_T R n₁
  have hγ0 : (γ 0).1 = R.r := by
    rw [hγ 0 ⟨le_rfl, by linarith⟩, R.g_eq]
    simp
  have hpow : R.r ^ n₁ ≤ R.r := pow_le_of_le_one hr0.le R.r_lt_one.le (by omega)
  refine ⟨γ, hsm, hγ, hM, fun t ht => ?_, fun n hn' hn0 hperp => ?_⟩
  · rw [hγ t ht]; rfl
  · obtain ⟨κ, hκ, hκn⟩ := dynamic_monodromy E h1 (continuous_sched R w₀) hsm.continuous hend
      (by rw [hγ0, abs_of_pos hr0]; nlinarith) (by rw [hγ0, abs_of_pos hr0]; linarith [R.r_lt_one])
      hn' hn0 hperp
    refine ⟨κ, hκ, ?_⟩
    have hs : sgn (-1) = -1 := by rw [sgn_neg, sgn_one]
    rw [hκn, hs, mul_neg_one, neg_smul]

include E in
/-- **アキレスの閉路の上の、動く面のモノドロミー**。 -/
theorem dynamic_loop_A (R : Race) (h0 : 0 < w₀) (h1 : w₀ < 1) (n₁ : ℕ) :
    ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.g t, VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t))) ∧
      toM (γ (3 * R.tstar)) = toM (γ 0) ∧
      (∀ t ∈ Icc 0 (2 * R.tstar),
        XF F (sched R w₀ t) (γ t).1 (γ t).2 = dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) ∧
      (∀ n : ℝ → V3, Continuous n → (∀ u, n u ≠ wp) →
        (∀ u, cross (n u) (XF F (sched R w₀ u) (γ u).1 (γ u).2) = wp) →
        ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0)) := by
  have hT := R.tstar_pos
  obtain ⟨γ, hsm, hγ, hend, hM, -, -, -⟩ := klein_loop_A R h0 n₁
  have hγ0 : (γ 0).1 = 1 := by
    rw [hγ 0 ⟨le_rfl, by linarith⟩, R.g_eq]
    simp
  refine ⟨γ, hsm, hγ, hM, fun t ht => ?_, fun n hn' hn0 hperp => ?_⟩
  · rw [hγ t ht]; rfl
  · obtain ⟨κ, hκ, hκn⟩ := dynamic_monodromy E h1 (continuous_sched R w₀) hsm.continuous hend
      (by rw [hγ0]; norm_num; linarith) (by rw [hγ0]; norm_num) hn' hn0 hperp
    refine ⟨κ, hκ, ?_⟩
    have hs : sgn (-1) = -1 := by rw [sgn_neg, sgn_one]
    rw [hκn, hs, mul_neg_one, neg_smul]

end DynMonodromy

/-! ### 比較の値 x̂：岸では理想形の値、動く面の上では t∗ の後の首の中に零点 -/

section XhatCompare

variable {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3} {F : ℝ → ℝ → ℝ → V3}
  {Vt Va : ℝ → ℝ}

/-- 岸では、亀の射影座標 x̂ は理想形の値 1/(r g) である。 -/
theorem DynamicPassage.xhat_shore_T (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va) (hc : 0 < c)
    {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) (hw : c ≤ |R.r * R.g t|) :
    xhat (dynT R w₀ F Vt t) = 1 / (R.r * R.g t) := by
  have hne : R.r * R.g t ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw
    linarith
  rw [P.agree_T t ht hw, Race.idealT, xhat_G hne]

/-- 岸では、アキレスの射影座標 x̂ は理想形の値 1/g である。 -/
theorem DynamicPassage.xhat_shore_A (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va) (hc : 0 < c)
    {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) (hw : c ≤ |R.g t|) :
    xhat (dynA R w₀ F Va t) = 1 / R.g t := by
  have hne : R.g t ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw
    linarith
  rw [P.agree_A t ht hw, Race.idealA, xhat_G hne]

theorem continuousOn_xhat_comp {f : ℝ → V3} (hf : Continuous f) {s : Set ℝ}
    (hne : ∀ t ∈ s, f t ≠ wp) : ContinuousOn (fun t => xhat (f t)) s := by
  have h1 : ContinuousOn (fun t => (f t).1) s := (continuous_fst.comp hf).continuousOn
  have h2 : ContinuousOn (fun t => nsq (f t)) s := (continuous_nsq.comp hf).continuousOn
  exact h1.div h2 fun t ht => (nsq_pos_of_ne (hne t ht)).ne'

/-- **動く面の上の x̂ の比較**。t∗ では x̂(T) > 0 > x̂(A) であり、t∗ の後の首の中に x̂(T) = x̂(A) となる
時刻がある。そのとき二人は別の点にいる。 -/
theorem xhat_zero_after
    (P : DynamicPassage R w₀ (R.r ^ n₁) ε n₁ S X F (VtR (R.r ^ n₁)) (VaR R.r w₀ (R.r ^ n₁) n₁))
    (E : DynamicEffects R w₀ n₁ F) (hn : 1 ≤ n₁) :
    ∃ t ∈ Ioo R.tstar (2 * R.tstar),
      xhat (dynT R w₀ F (VtR (R.r ^ n₁)) t) = xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) ∧
      dynT R w₀ F (VtR (R.r ^ n₁)) t ≠ dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t ∧
      |R.r * R.g t| < R.r ^ n₁ := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hc : 0 < R.r ^ n₁ := pow_pos hr0 n₁
  have hpow : R.r ^ n₁ ≤ R.r := pow_le_of_le_one hr0.le hr1.le (by omega)
  have hsub : Icc R.tstar (2 * R.tstar) ⊆ Icc 0 (2 * R.tstar) :=
    Icc_subset_Icc_left hT.le
  have hcT := continuousOn_xhat_comp P.smooth_T.continuous
    (s := Icc R.tstar (2 * R.tstar)) fun t ht => E.avoids_T t (hsub ht)
  have hcA := continuousOn_xhat_comp P.smooth_A.continuous
    (s := Icc R.tstar (2 * R.tstar)) fun t ht => E.avoids_A t (hsub ht)
  have hcont := hcT.sub hcA
  have hg2 : R.g (2 * R.tstar) = -1 := by rw [R.g_eq]; field_simp; ring
  have h2mem : 2 * R.tstar ∈ Icc 0 (2 * R.tstar) := ⟨by linarith, le_rfl⟩
  have hTe := P.xhat_shore_T hc h2mem (by rw [hg2, mul_neg, mul_one, abs_neg, abs_of_pos hr0]; exact hpow)
  have hAe := P.xhat_shore_A hc h2mem (by
    rw [hg2, abs_neg, abs_one]; exact pow_le_one₀ hr0.le hr1.le)
  have hb : xhat (dynT R w₀ F (VtR (R.r ^ n₁)) (2 * R.tstar)) -
      xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) (2 * R.tstar)) < 0 := by
    rw [hTe, hAe, hg2, mul_neg, mul_one]
    have h3 : 1 < 1 / R.r := by rw [lt_div_iff₀ hr0]; linarith
    have e : (1 : ℝ) / -R.r = -(1 / R.r) := by rw [div_neg]
    have e2 : (1 : ℝ) / -1 = -1 := by norm_num
    rw [e, e2]
    linarith
  have ha : 0 < xhat (dynT R w₀ F (VtR (R.r ^ n₁)) R.tstar) -
      xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) R.tstar) := by
    have := E.xhat_sign
    linarith [this.1, this.2]
  have hivt := intermediate_value_Ioo' (by linarith : R.tstar ≤ 2 * R.tstar) hcont
  obtain ⟨t, ht, hval⟩ := hivt (show (0 : ℝ) ∈ Ioo _ _ from ⟨hb, ha⟩)
  have htI : t ∈ Icc 0 (2 * R.tstar) := ⟨by linarith [ht.1], ht.2.le⟩
  have heq : xhat (dynT R w₀ F (VtR (R.r ^ n₁)) t) =
      xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) := by
    have h3 : xhat (dynT R w₀ F (VtR (R.r ^ n₁)) t) -
      xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) = 0 := hval
    linarith
  refine ⟨t, ht, heq, P.no_collision t htI, ?_⟩
  have hgneg : R.g t < 0 := by
    rw [R.g_eq]
    have : 1 < t / R.tstar := by rw [lt_div_iff₀ hT]; linarith [ht.1]
    linarith
  have hrg : R.r * R.g t < 0 := mul_neg_of_pos_of_neg hr0 hgneg
  rw [abs_of_neg hrg]
  by_contra hcon
  push Not at hcon
  have hw1 : R.r ^ n₁ ≤ |R.r * R.g t| := by rw [abs_of_neg hrg]; exact hcon
  have hw2 : R.r ^ n₁ ≤ |R.g t| := by
    rw [abs_of_neg hgneg]
    nlinarith
  rw [P.xhat_shore_T hc htI hw1, P.xhat_shore_A hc htI hw2] at heq
  have hgne : R.g t ≠ 0 := hgneg.ne
  field_simp at heq
  nlinarith

end XhatCompare

/-! ### 【議論】の形：同じ F の上の M1、M2、非衝突、最初の段階、比較 -/

/-- **【議論】の形（動く面の上）**。n₁ ≥ 1、ε > 0 について、`DynamicPassage` と `DynamicEffects` を満たす
同じ F の上で、次が成り立つ。(1) 右の位置 t = 0 に亀は表、アキレスは裏にいて、左の位置 t = 2t∗ に亀は裏、
アキレスは表にいる（動く面の法線での M1）。(2) その間、全時刻で二人は同じ点におらず、最初のゼノンの
段階は正確である。(3) 動く面の上で二人の閉路に沿って運んだ側は、反転して戻る（M2）。(4) 比較の値 x̂ は
t∗ の後の首の中で一致し、そのとき二人は別の点にいる。 -/
theorem klein_argument_form (R : Race) {n₁ : ℕ} (hn : 1 ≤ n₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℝ → ℝ → ℝ → V3,
      DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ (Shat (R.r ^ n₁)) (Xhat (R.r ^ n₁)) F
        (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) ∧
      DynamicEffects R (R.r ^ n₁) n₁ F ∧
      (Front (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) 0) (dynNT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) 0) ∧
        Back (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) 0)
          (-dynNA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) 0)) ∧
      (Back (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) (2 * R.tstar))
          (dynNT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) (2 * R.tstar)) ∧
        Front (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) (2 * R.tstar))
          (-dynNA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) (2 * R.tstar))) ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t ≠
        dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) ∧
      dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) (R.tn 1) =
        dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) (R.tn 0) ∧
      (∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
        (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.r * R.g t, VtR (R.r ^ n₁) (R.r * R.g t))) ∧
        toM (γ (3 * R.tstar)) = toM (γ 0) ∧
        (∀ t ∈ Icc 0 (2 * R.tstar), XF F (sched R (R.r ^ n₁) t) (γ t).1 (γ t).2 =
          dynNT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t) ∧
        (∀ n : ℝ → V3, Continuous n → (∀ u, n u ≠ wp) →
          (∀ u, cross (n u) (XF F (sched R (R.r ^ n₁) u) (γ u).1 (γ u).2) = wp) →
          ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0))) ∧
      (∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
        (∀ t ∈ Icc 0 (2 * R.tstar),
          γ t = (R.g t, VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ (R.g t))) ∧
        toM (γ (3 * R.tstar)) = toM (γ 0) ∧
        (∀ t ∈ Icc 0 (2 * R.tstar), XF F (sched R (R.r ^ n₁) t) (γ t).1 (γ t).2 =
          dynNA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) ∧
        (∀ n : ℝ → V3, Continuous n → (∀ u, n u ≠ wp) →
          (∀ u, cross (n u) (XF F (sched R (R.r ^ n₁) u) (γ u).1 (γ u).2) = wp) →
          ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0))) ∧
      (∃ t ∈ Ioo R.tstar (2 * R.tstar),
        xhat (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t) =
          xhat (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) ∧
        dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t ≠
          dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t ∧
        |R.r * R.g t| < R.r ^ n₁) := by
  have hT := R.tstar_pos
  have hr0 := R.r_pos
  have h0 : 0 < R.r ^ n₁ := pow_pos hr0 n₁
  have h1 : R.r ^ n₁ < 1 := R.pow_lt_one hn
  have hpow : R.r ^ n₁ ≤ R.r := pow_le_of_le_one hr0.le R.r_lt_one.le (by omega)
  obtain ⟨F, P, E⟩ := dynamic_effects R hn hε
  have hg0 : R.g 0 = 1 := by rw [R.g_eq]; simp
  have hg2 : R.g (2 * R.tstar) = -1 := by rw [R.g_eq]; field_simp; ring
  have m0 : (0 : ℝ) ∈ Icc 0 (2 * R.tstar) := ⟨le_rfl, by linarith⟩
  have m2 : 2 * R.tstar ∈ Icc 0 (2 * R.tstar) := ⟨by linarith, le_rfl⟩
  refine ⟨F, P, E, ⟨E.label_T_right 0 m0 (by rw [hg0, mul_one]; exact hpow),
      E.label_A_right 0 m0 (by rw [hg0]; exact h1.le)⟩,
    ⟨E.label_T_left _ m2 (by rw [hg2]; linarith), E.label_A_left _ m2 (by rw [hg2]; linarith)⟩,
    P.no_collision, P.step_before 0 (by omega),
    dynamic_loop_T P.eversion R h0 h1 hn le_rfl, dynamic_loop_A P.eversion R h0 h1 n₁,
    xhat_zero_after P E hn⟩

/-! ### 束 -/

/-- **原構想との対応に使う橋の束**。`KleinSynthesis` に、閉路、モノドロミー、ラベルの交換の時刻、
ホーンの汲み尽くしと限界を加える。F についての欄は、条件を満たすすべての F について述べる。 -/
structure KleinConception (R : Race) : Prop where
  /-- 静的な束、K3⁺、その帰結（`mathemagical_klein_synthesis`）。 -/
  synthesis : KleinSynthesis R
  /-- 首の帯の上で被覆写像が同一視するのは T の冪だけである（首の円は環の芯）。 -/
  strip : ∀ p q : ℝ × ℝ, |p.1| < 2 → |q.1| < 2 → toM p = toM q →
    ∃ m : ℤ, q = (p.1, p.2 + (m : ℝ) * (2 * π))
  /-- 亀の閉路：M の上で閉じ、首の円の持ち上げを t∗ にちょうど一度、速度 −r/t∗ で横切る。 -/
  loop_T : ∀ n₁ : ℕ, ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
    (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.r * R.g t, VtR (R.r ^ n₁) (R.r * R.g t))) ∧
    γ (3 * R.tstar) = gam (-1) 0 (γ 0) ∧ toM (γ (3 * R.tstar)) = toM (γ 0) ∧
    (∀ t ∈ Icc 0 (3 * R.tstar), (∃ k : ℤ, (γ t).1 = 4 * (k : ℝ)) ↔ t = R.tstar) ∧
    HasDerivAt (fun t => (γ t).1) (-(R.r / R.tstar)) R.tstar ∧ -(R.r / R.tstar) ≠ 0
  /-- アキレスの閉路：同様。速度は −1/t∗。 -/
  loop_A : ∀ n₁ : ℕ, 1 ≤ n₁ → ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
    (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.g t, VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ (R.g t))) ∧
    γ (3 * R.tstar) = gam (-1) 0 (γ 0) ∧ toM (γ (3 * R.tstar)) = toM (γ 0) ∧
    (∀ t ∈ Icc 0 (3 * R.tstar), (∃ k : ℤ, (γ t).1 = 4 * (k : ℝ)) ↔ t = R.tstar) ∧
    HasDerivAt (fun t => (γ t).1) (-(1 / R.tstar)) R.tstar ∧ -(1 / R.tstar) ≠ 0
  /-- モノドロミー（静的な面）：γ_{k,m} に対応する道に沿って、法線は (−1)ᵏ の正の倍で戻る。 -/
  monodromy_static : ∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 → ∀ (γ : ℝ → ℝ × ℝ) (a b : ℝ) (k m : ℤ)
    (n : ℝ → V3), Continuous γ → γ b = gam k m (γ a) → Continuous n → (∀ u, n u ≠ wp) →
    (∀ u, cross (n u) (Xhat w₀ (γ u).1 (γ u).2) = wp) →
    ∃ κ : ℝ, 0 < κ ∧ n b = (κ * sgn k) • n a
  /-- モノドロミー（族のどの段でも）。 -/
  monodromy_stage : ∀ (w₀ ε : ℝ) (F : ℝ → ℝ → ℝ → V3), NeckEversion w₀ ε (Shat w₀) F →
    ∀ (s : ℝ) (γ : ℝ → ℝ × ℝ) (a b : ℝ) (k m : ℤ) (n : ℝ → V3), Continuous γ →
    γ b = gam k m (γ a) → Continuous n → (∀ u, n u ≠ wp) →
    (∀ u, cross (n u) (XF F s (γ u).1 (γ u).2) = wp) →
    ∃ κ : ℝ, 0 < κ ∧ n b = (κ * sgn k) • n a
  /-- ラベルの交換の時刻：動く面の法線でのラベルの零点は首の中にあり、t∗ からの隔たりは
  亀で t∗ rⁿ¹⁻¹、アキレスで t∗ rⁿ¹ より小さい。 -/
  label_time : ∀ (n₁ : ℕ) (w₀ : ℝ) (F : ℝ → ℝ → ℝ → V3), DynamicEffects R w₀ n₁ F →
    ∀ t ∈ Icc 0 (2 * R.tstar),
      (side (dynT R w₀ F (VtR (R.r ^ n₁)) t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t) = 0 →
        |R.r * R.g t| < R.r ^ n₁ ∧ R.r * |t - R.tstar| < R.tstar * R.r ^ n₁) ∧
      (side (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
          (-dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) = 0 →
        |R.g t| < R.r ^ n₁ ∧ |t - R.tstar| < R.tstar * R.r ^ n₁)
  /-- ラベルの交換の時刻は、首を細くする極限で t∗ に収束する（亀）。 -/
  label_limit_T : ∀ F : ℕ → ℝ → ℝ → ℝ → V3,
    (∀ n : ℕ, 1 ≤ n → DynamicEffects R (R.r ^ n) n (F n)) → ∀ τ : ℕ → ℝ,
    (∀ n : ℕ, 1 ≤ n → τ n ∈ Icc 0 (2 * R.tstar) ∧
      side (dynT R (R.r ^ n) (F n) (VtR (R.r ^ n)) (τ n))
        (dynNT R (R.r ^ n) (F n) (VtR (R.r ^ n)) (τ n)) = 0) →
    Tendsto τ atTop (𝓝 R.tstar)
  /-- 同（アキレス）。 -/
  label_limit_A : ∀ F : ℕ → ℝ → ℝ → ℝ → V3,
    (∀ n : ℕ, 1 ≤ n → DynamicEffects R (R.r ^ n) n (F n)) → ∀ τ : ℕ → ℝ,
    (∀ n : ℕ, 1 ≤ n → τ n ∈ Icc 0 (2 * R.tstar) ∧
      side (dynA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n) (τ n))
        (-dynNA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n) (τ n)) = 0) →
    Tendsto τ atTop (𝓝 R.tstar)
  /-- 静的な面では、t∗ に亀はまだ表、アキレスはまだ裏にいて、t∗ の後の首の中にラベルの零点がある。 -/
  static_labels : ∀ n₁ : ℕ, 1 ≤ n₁ →
    (Front (R.runT (Shat (R.r ^ n₁)) (VtR (R.r ^ n₁)) R.tstar)
        (Xhat (R.r ^ n₁) (R.r * R.g R.tstar) (VtR (R.r ^ n₁) (R.r * R.g R.tstar))) ∧
      Back (R.runA (Shat (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) R.tstar)
        (-Xhat (R.r ^ n₁) (R.g R.tstar) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ (R.g R.tstar)))) ∧
    (∃ t ∈ Ioo R.tstar (2 * R.tstar), |R.r * R.g t| < R.r ^ n₁ ∧
      side (R.runT (Shat (R.r ^ n₁)) (VtR (R.r ^ n₁)) t)
        (Xhat (R.r ^ n₁) (R.r * R.g t) (VtR (R.r ^ n₁) (R.r * R.g t))) = 0) ∧
    (∃ t ∈ Ioo R.tstar (2 * R.tstar), |R.g t| < R.r ^ n₁ ∧
      side (R.runA (Shat (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t)
        (-Xhat (R.r ^ n₁) (R.g t) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ (R.g t))) = 0)
  /-- 枠の法則 E（静的な岸）：4w₀/5 < |w| < 1 では、静的な面がすでに
  (Ŝ(p), X̂(p)) = E(Ŝ(φp), X̂(φp)) を満たす。 -/
  frame_static : ∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 → ∀ w v : ℝ, w₀ * (4 / 5) < |w| → |w| < 1 →
    (Shat w₀ w v, Xhat w₀ w v) = Everse (Shat w₀ (-w) (π - v), Xhat w₀ (-w) (π - v))
  /-- 枠の法則 E（面）：裏返しの始まりの枠は静的な枠であり、終わりの首の枠は、Ŝ の首の枠を φ で
  引き戻して E で写したものである。 -/
  frame_stage : ∀ (w₀ ε : ℝ) (F : ℝ → ℝ → ℝ → V3), 0 < w₀ → w₀ < 1 →
    NeckEversion w₀ ε (Shat w₀) F → ∀ s w v : ℝ,
      (s ≤ 0 → (F s w v, XF F s w v) = (Shat w₀ w v, Xhat w₀ w v)) ∧
      (1 ≤ s → |w| < 1 →
        (F s w v, XF F s w v) = Everse (Shat w₀ (-w) (π - v), Xhat w₀ (-w) (π - v)))
  /-- 枠の法則 E（走者）：窓の前の走者の枠は静的な枠であり、窓の後の走者の枠は、鏡の時刻 2t∗ − t の
  静的な枠を E で写したものである。 -/
  frame_runners : ∀ (n₁ : ℕ) (w₀ ε : ℝ) (F : ℝ → ℝ → ℝ → V3), 0 < w₀ → w₀ < 1 → w₀ ≤ R.r ^ n₁ →
    DynamicPassage R w₀ (R.r ^ n₁) ε n₁ (Shat w₀) (Xhat w₀) F (VtR (R.r ^ n₁))
      (VaR R.r w₀ (R.r ^ n₁) n₁) → ∀ t : ℝ,
      (t ≤ t1 R w₀ →
        (dynT R w₀ F (VtR (R.r ^ n₁)) t, dynNT R w₀ F (VtR (R.r ^ n₁)) t) =
            (R.runT (Shat w₀) (VtR (R.r ^ n₁)) t,
              Xhat w₀ (R.r * R.g t) (VtR (R.r ^ n₁) (R.r * R.g t))) ∧
          (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t,
              dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) =
            (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) t,
              Xhat w₀ (R.g t) (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t)))) ∧
      (t2 R w₀ ≤ t → t ≤ 2 * R.tstar →
        (dynT R w₀ F (VtR (R.r ^ n₁)) t, dynNT R w₀ F (VtR (R.r ^ n₁)) t) =
            Everse (R.runT (Shat w₀) (VtR (R.r ^ n₁)) (2 * R.tstar - t),
              Xhat w₀ (R.r * R.g (2 * R.tstar - t))
                (VtR (R.r ^ n₁) (R.r * R.g (2 * R.tstar - t)))) ∧
          (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t,
              dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) =
            Everse (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) (2 * R.tstar - t),
              Xhat w₀ (R.g (2 * R.tstar - t))
                (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g (2 * R.tstar - t)))))
  /-- 窓の後のラベルは、鏡の時刻の静的なラベルの符号を変えたものである。 -/
  label_after : ∀ (n₁ : ℕ) (w₀ ε : ℝ) (F : ℝ → ℝ → ℝ → V3), 0 < w₀ → w₀ < 1 → w₀ ≤ R.r ^ n₁ →
    DynamicPassage R w₀ (R.r ^ n₁) ε n₁ (Shat w₀) (Xhat w₀) F (VtR (R.r ^ n₁))
      (VaR R.r w₀ (R.r ^ n₁) n₁) → ∀ t : ℝ, t2 R w₀ ≤ t → t ≤ 2 * R.tstar →
      side (dynT R w₀ F (VtR (R.r ^ n₁)) t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t) =
          -side (R.runT (Shat w₀) (VtR (R.r ^ n₁)) (2 * R.tstar - t))
            (Xhat w₀ (R.r * R.g (2 * R.tstar - t))
              (VtR (R.r ^ n₁) (R.r * R.g (2 * R.tstar - t)))) ∧
        side (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
            (-dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) =
          -side (R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) (2 * R.tstar - t))
            (-Xhat w₀ (R.g (2 * R.tstar - t))
              (VaR R.r w₀ (R.r ^ n₁) n₁ (R.g (2 * R.tstar - t))))
  /-- 無限捻転：アキレスの角度は w = rᵏ（k ≤ n₁）で 2πk、首の中央で π/2 + 2πn₁ であり、
  段階数 n → ∞ で発散する。 -/
  twist : (∀ n₁ k : ℕ, k ≤ n₁ → VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ (R.r ^ k) = k * (2 * π)) ∧
    (∀ n₁ : ℕ, VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ 0 = π / 2 + n₁ * (2 * π)) ∧
    Tendsto (fun n : ℕ => VaR R.r (R.r ^ n) (R.r ^ n) n 0) atTop atTop
  /-- 動く面の上のモノドロミー：段が連続に変わる間に運んだ側も、(−1)ᵏ の正の倍で戻る
  （始点は首の動く部分の外）。 -/
  monodromy_dynamic : ∀ (w₀ ε : ℝ) (F : ℝ → ℝ → ℝ → V3), w₀ < 1 → NeckEversion w₀ ε (Shat w₀) F →
    ∀ (σ : ℝ → ℝ) (γ : ℝ → ℝ × ℝ) (a b : ℝ) (k m : ℤ) (n : ℝ → V3), Continuous σ →
    Continuous γ → γ b = gam k m (γ a) → w₀ * (9 / 10) < |(γ a).1| → |(γ a).1| < 2 →
    Continuous n → (∀ u, n u ≠ wp) →
    (∀ u, cross (n u) (XF F (σ u) (γ u).1 (γ u).2) = wp) →
    ∃ κ : ℝ, 0 < κ ∧ n b = (κ * sgn k) • n a
  /-- 岸での比較の値 x̂：理想形の値 1/(r g)、1/g に等しい。 -/
  xhat_shore : ∀ (n₁ : ℕ) (w₀ ε : ℝ) (F : ℝ → ℝ → ℝ → V3),
    DynamicPassage R w₀ (R.r ^ n₁) ε n₁ (Shat w₀) (Xhat w₀) F (VtR (R.r ^ n₁))
      (VaR R.r w₀ (R.r ^ n₁) n₁) → ∀ t ∈ Icc 0 (2 * R.tstar),
      (R.r ^ n₁ ≤ |R.r * R.g t| →
        xhat (dynT R w₀ F (VtR (R.r ^ n₁)) t) = 1 / (R.r * R.g t)) ∧
      (R.r ^ n₁ ≤ |R.g t| → xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) = 1 / R.g t)
  /-- 【議論】の形（動く面の上）：同じ F の上の M1、非衝突、最初の段階、M2、比較。 -/
  argument : ∀ n₁ : ℕ, 1 ≤ n₁ → ∀ ε : ℝ, 0 < ε → ∃ F : ℝ → ℝ → ℝ → V3,
    DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ (Shat (R.r ^ n₁)) (Xhat (R.r ^ n₁)) F
      (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) ∧
    DynamicEffects R (R.r ^ n₁) n₁ F ∧
    (Front (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) 0) (dynNT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) 0) ∧
      Back (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) 0)
        (-dynNA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) 0)) ∧
    (Back (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) (2 * R.tstar))
        (dynNT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) (2 * R.tstar)) ∧
      Front (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) (2 * R.tstar))
        (-dynNA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) (2 * R.tstar))) ∧
    (∀ t ∈ Icc 0 (2 * R.tstar), dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t ≠
      dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) ∧
    dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) (R.tn 1) =
      dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) (R.tn 0) ∧
    (∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.r * R.g t, VtR (R.r ^ n₁) (R.r * R.g t))) ∧
      toM (γ (3 * R.tstar)) = toM (γ 0) ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), XF F (sched R (R.r ^ n₁) t) (γ t).1 (γ t).2 =
        dynNT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t) ∧
      (∀ n : ℝ → V3, Continuous n → (∀ u, n u ≠ wp) →
        (∀ u, cross (n u) (XF F (sched R (R.r ^ n₁) u) (γ u).1 (γ u).2) = wp) →
        ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0))) ∧
    (∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t ∈ Icc 0 (2 * R.tstar),
        γ t = (R.g t, VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ (R.g t))) ∧
      toM (γ (3 * R.tstar)) = toM (γ 0) ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), XF F (sched R (R.r ^ n₁) t) (γ t).1 (γ t).2 =
        dynNA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) ∧
      (∀ n : ℝ → V3, Continuous n → (∀ u, n u ≠ wp) →
        (∀ u, cross (n u) (XF F (sched R (R.r ^ n₁) u) (γ u).1 (γ u).2) = wp) →
        ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0))) ∧
    (∃ t ∈ Ioo R.tstar (2 * R.tstar),
      xhat (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t) =
        xhat (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) ∧
      dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t ≠
        dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t ∧
      |R.r * R.g t| < R.r ^ n₁)
  /-- 族のどの段も、反転したホーンの 1 ≤ |X| ≤ 1/w₀ の部分を正確に含む。 -/
  horn_stage : ∀ (w₀ ε : ℝ) (F : ℝ → ℝ → ℝ → V3), 0 < w₀ → w₀ < 1 →
    NeckEversion w₀ ε (Shat w₀) F → ∀ s X v : ℝ,
      (1 ≤ X → X ≤ 1 / w₀ → F s (1 / X) v = inv3 (H X v)) ∧
      (X ≤ -1 → -(1 / w₀) ≤ X → F s (1 / X) v = inv3 (H X (π - v)))
  /-- ホーンの汲み尽くし。 -/
  horn_limit : ∀ (F : ℕ → ℝ → ℝ → ℝ → V3) (ε : ℕ → ℝ),
    (∀ n : ℕ, 1 ≤ n → NeckEversion (R.r ^ n) (ε n) (Shat (R.r ^ n)) (F n)) → ∀ X : ℝ, 1 ≤ X →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ s v : ℝ,
      F n s (1 / X) v = inv3 (H X v) ∧ F n s (1 / -X) v = inv3 (H (-X) (π - v))
  /-- 非有界なホーンは、M の連続像に入らない。 -/
  horn_unbounded : ∀ f : KleinM → V3, Continuous f → ¬ ∀ X v : ℝ, 1 ≤ X → H X v ∈ range f
  /-- 反転したホーンの全体を含む M の連続像は ℘ を通る。静的な面 Ŝ は ℘ を通らないので、全体を含まない。 -/
  horn_tip : (∀ f : KleinM → V3, Continuous f →
      (∀ w v : ℝ, 0 < w → w ≤ 1 → G w v ∈ range f) → wp ∈ range f) ∧
    (∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 → ¬ ∀ w v : ℝ, 0 < w → w ≤ 1 → G w v ∈ range (ShatM w₀))

end Zeno.Smale

namespace Zeno

open Zeno.Model Zeno.Smale Real Set Filter Topology

/-- **原構想との対応に使う橋の束の定理**。 -/
theorem mathemagical_klein_conception (R : Race) : KleinConception R where
  synthesis := mathemagical_klein_synthesis R
  strip := fun _ _ hp hq h => toM_eq_of_strip hp hq h
  loop_T := fun n₁ => klein_loop_T R n₁
  loop_A := fun n₁ _ => klein_loop_A R (pow_pos R.r_pos n₁) n₁
  monodromy_static := fun _ h0 h1 _ _ _ _ _ _ hγ hend hn hn0 hperp =>
    Shat_monodromy h0 h1 hγ hend hn hn0 hperp
  monodromy_stage := fun _ _ _ E s _ _ _ _ _ _ hγ hend hn hn0 hperp =>
    stage_monodromy E s hγ hend hn hn0 hperp
  label_time := fun _ _ _ E _ ht =>
    ⟨fun hz => ⟨E.zero_T_in_neck ht hz, E.zero_T_time ht hz⟩,
      fun hz => ⟨E.zero_A_in_neck ht hz, E.zero_A_time ht hz⟩⟩
  label_limit_T := fun _ hF _ hτ => label_zero_T_tendsto R hF hτ
  label_limit_A := fun _ hF _ hτ => label_zero_A_tendsto R hF hτ
  static_labels := fun n₁ hn =>
    ⟨static_label_tstar R (pow_pos R.r_pos n₁) (R.pow_lt_one hn) n₁,
      static_zero_T R (pow_pos R.r_pos n₁) (R.pow_lt_one hn) n₁ hn le_rfl,
      static_zero_A R (pow_pos R.r_pos n₁) (R.pow_lt_one hn) n₁ le_rfl⟩
  frame_static := fun _ h0 h1 _ v hw hw1 => static_frame_shore h0 h1 hw hw1 v
  frame_stage := fun _ _ _ h0 h1 E _ w v =>
    ⟨fun hs => stage_frame_start E hs w v, fun hs hw => stage_frame_finish h0 h1 E hs hw v⟩
  frame_runners := fun _ _ _ _ h0 h1 hc P _ =>
    ⟨fun ht => ⟨P.frame_before_T h0 ht, P.frame_before_A h0 ht⟩,
      fun ht2 ht => ⟨P.frame_after_T h0 h1 hc ht2 ht, P.frame_after_A h0 h1 hc ht2 ht⟩⟩
  label_after := fun _ _ _ _ h0 h1 hc P _ ht2 ht =>
    ⟨P.label_after_T h0 h1 hc ht2 ht, P.label_after_A h0 h1 hc ht2 ht⟩
  twist := ⟨fun _ _ hk => twist_at_step R hk, fun n₁ => twist_at_centre R n₁, twist_tendsto R⟩
  monodromy_dynamic := fun _ _ _ h1 E _ _ _ _ _ _ _ hσ hγ hend hb hb2 hn hn0 hperp =>
    dynamic_monodromy E h1 hσ hγ hend hb hb2 hn hn0 hperp
  xhat_shore := fun n₁ _ _ _ P _ ht =>
    ⟨fun hw => P.xhat_shore_T (pow_pos R.r_pos n₁) ht hw,
      fun hw => P.xhat_shore_A (pow_pos R.r_pos n₁) ht hw⟩
  argument := fun _ hn _ hε => klein_argument_form R hn hε
  horn_stage := fun _ _ _ h0 h1 E s _ v =>
    ⟨fun hX1 hX => stage_horn_right h0 h1 E s hX1 hX v,
      fun hX1 hX => stage_horn_left h0 h1 E s hX1 hX v⟩
  horn_limit := fun _ _ hF _ hX => horn_exhaustion R hF hX
  horn_unbounded := fun _ hf => horn_not_in_compact_image hf
  horn_tip := ⟨fun _ hf h => inverted_horn_forces_wp hf h, fun _ h0 h1 => ShatM_misses_horn h0 h1⟩

end Zeno
