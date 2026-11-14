/-
# Zeno.Horn : 【仮定】3（ガブリエルのラッパ）の体積と面積

体積と面積は回転体の積分公式で定義する。測度論的な体積ではない（形式化の選択）。
-/
import Zeno.Race
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology MeasureTheory intervalIntegral

/-- y = 1/x の x までの回転体の体積。 -/
def hornV (x : ℝ) : ℝ := π * ∫ s in (1 : ℝ)..x, (1 / s) ^ 2

/-- y = 1/x の x までの回転面の面積。 -/
def hornA (x : ℝ) : ℝ := 2 * π * ∫ s in (1 : ℝ)..x, (1 / s) * √(1 + (1 / s ^ 2) ^ 2)

theorem one_le_mem {x s : ℝ} (hx : 1 ≤ x) (hs : s ∈ uIcc (1 : ℝ) x) : 1 ≤ s := by
  rw [uIcc_of_le hx] at hs; exact hs.1

/-- V(x) = π(1 − 1/x) -/
theorem hornV_eq {x : ℝ} (hx : 1 ≤ x) : hornV x = π * (1 - 1 / x) := by
  have hF : ∀ s ∈ uIcc (1 : ℝ) x, HasDerivAt (fun s : ℝ => -(1 / s)) ((1 / s) ^ 2) s := by
    intro s hs
    have h1 : 1 ≤ s := one_le_mem hx hs
    have h0 : s ≠ 0 := by linarith
    have h := (hasDerivAt_inv h0).neg
    convert h using 1
    · ext y; simp [one_div]
    · field_simp
  have hI : IntervalIntegrable (fun s : ℝ => (1 / s) ^ 2) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have h1 : 1 ≤ s := one_le_mem hx hs
    have h0 : s ≠ 0 := by linarith
    apply ContinuousAt.continuousWithinAt
    exact ((continuousAt_const.div continuousAt_id h0).pow 2)
  simp only [hornV]
  rw [integral_eq_sub_of_hasDerivAt hF hI]
  ring

/-- 全体積は有限（π を超えない）。 -/
theorem hornV_le {x : ℝ} (hx : 1 ≤ x) : hornV x ≤ π := by
  rw [hornV_eq hx]
  have h : 0 ≤ 1 / x := by positivity
  nlinarith [Real.pi_pos]

/-- 面積の被積分関数の連続性。 -/
theorem integrand_contOn {x : ℝ} (hx : 1 ≤ x) :
    ContinuousOn (fun s : ℝ => (1 / s) * √(1 + (1 / s ^ 2) ^ 2)) (uIcc 1 x) := by
  intro s hs
  have h1 : 1 ≤ s := one_le_mem hx hs
  have h0 : s ≠ 0 := by linarith
  apply ContinuousAt.continuousWithinAt
  have hp : s ^ 2 ≠ 0 := pow_ne_zero 2 h0
  apply ContinuousAt.mul (continuousAt_const.div continuousAt_id h0)
  apply ContinuousAt.sqrt
  exact continuousAt_const.add
    ((continuousAt_const.div (continuousAt_id.pow 2) hp).pow 2)

/-- A(x) ≥ 2π ln x -/
theorem hornA_ge {x : ℝ} (hx : 1 ≤ x) : 2 * π * log x ≤ hornA x := by
  have h1 : IntervalIntegrable (fun s : ℝ => 1 / s) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have h1 : 1 ≤ s := one_le_mem hx hs
    have h0 : s ≠ 0 := by linarith
    exact (continuousAt_const.div continuousAt_id h0).continuousWithinAt
  have h2 : IntervalIntegrable (fun s : ℝ => (1 / s) * √(1 + (1 / s ^ 2) ^ 2)) volume 1 x :=
    (integrand_contOn hx).intervalIntegrable
  have hmono : (∫ s in (1 : ℝ)..x, 1 / s) ≤ ∫ s in (1 : ℝ)..x, (1 / s) * √(1 + (1 / s ^ 2) ^ 2) := by
    apply integral_mono_on hx h1 h2
    intro s hs
    have hs1 : 1 ≤ s := hs.1
    have hpos : 0 < 1 / s := by positivity
    have hsq : 1 ≤ √(1 + (1 / s ^ 2) ^ 2) := by
      apply Real.one_le_sqrt.mpr
      have : 0 ≤ (1 / s ^ 2) ^ 2 := by positivity
      linarith
    nlinarith
  have hlog : (∫ s in (1 : ℝ)..x, 1 / s) = log x := by
    rw [integral_one_div_of_pos one_pos (by linarith)]
    simp
  rw [hlog] at hmono
  simp only [hornA]
  have hpi : 0 < 2 * π := by positivity
  exact mul_le_mul_of_nonneg_left hmono hpi.le

/-- 全面積は無限である。 -/
theorem tendsto_hornA : Tendsto hornA atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => 2 * π * log x) atTop atTop :=
    tendsto_log_atTop.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ h1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact hornA_ge hx

/-! ### 競走との辞書 -/

namespace Race

variable (R : Race)

/-- 体積は経過時間の割合に等しい。V(1/g)/π = t/t∗（0 ≤ t < t∗）。 -/
theorem dict_time {t : ℝ} (h0 : 0 ≤ t) (h1 : t < R.tstar) :
    hornV (1 / R.g t) / π = t / R.tstar := by
  have hts := R.tstar_pos
  have hg : R.g t = 1 - t / R.tstar := R.g_eq t
  have hle : t / R.tstar < 1 := (div_lt_one hts).mpr h1
  have hnn : 0 ≤ t / R.tstar := by positivity
  have hgpos : 0 < R.g t := by rw [hg]; linarith
  have hgle : R.g t ≤ 1 := by rw [hg]; linarith
  have hx : 1 ≤ 1 / R.g t := (one_le_div hgpos).mpr hgle
  rw [hornV_eq hx]
  have hpi := Real.pi_pos.ne'
  simp only [one_div, inv_inv]
  rw [hg]
  field_simp
  ring

/-- 面積はステップ数の分だけ増える。A(r⁻ⁿ) ≥ 2π n ln(1/r)。 -/
theorem dict_steps (n : ℕ) :
    2 * π * (n * log (1 / R.r)) ≤ hornA (1 / R.g (R.tn n)) := by
  rw [R.g_tn]
  have hp := pow_pos R.r_pos n
  have hle : R.r ^ n ≤ 1 := pow_le_one₀ R.r_pos.le R.r_lt_one.le
  have hx : 1 ≤ 1 / R.r ^ n := (one_le_div hp).mpr hle
  have h := hornA_ge hx
  have e : log (1 / R.r ^ n) = n * log (1 / R.r) := by
    rw [one_div, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
    ring
  rwa [e] at h

/-- ステップを無限に進めると面積は発散する。 -/
theorem tendsto_steps_area :
    Tendsto (fun n : ℕ => hornA (1 / R.g (R.tn n))) atTop atTop := by
  have hlog : 0 < log (1 / R.r) := by
    apply Real.log_pos
    rw [one_div]
    exact (one_lt_inv₀ R.r_pos).mpr R.r_lt_one
  have h1 : Tendsto (fun n : ℕ => 2 * π * (n * log (1 / R.r))) atTop atTop := by
    have : Tendsto (fun n : ℕ => (n : ℝ) * log (1 / R.r)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hlog
    exact this.const_mul_atTop (by positivity)
  exact tendsto_atTop_mono (fun n => R.dict_steps n) h1

end Race

/-! ### 比較モデル（仮定3 が使われていることの確認） -/

/-- 比較1：y = 1/√x。体積が発散する（時間の有限性と対応しない）。 -/
def thinV (x : ℝ) : ℝ := π * ∫ s in (1 : ℝ)..x, (1 / √s) ^ 2

theorem thinV_eq {x : ℝ} (hx : 1 ≤ x) : thinV x = π * log x := by
  have hcongr : ∫ s in (1 : ℝ)..x, (1 / √s) ^ 2 = ∫ s in (1 : ℝ)..x, 1 / s := by
    apply integral_congr
    intro s hs
    have h1 : 1 ≤ s := one_le_mem hx hs
    have h0 : 0 < s := by linarith
    simp only
    rw [div_pow, one_pow, Real.sq_sqrt h0.le]
  simp only [thinV]
  rw [hcongr, integral_one_div_of_pos one_pos (by linarith)]
  simp

theorem tendsto_thinV : Tendsto thinV atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => π * log x) atTop atTop :=
    tendsto_log_atTop.const_mul_atTop Real.pi_pos
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (thinV_eq hx).symm

/-- 比較2：y = 1/x²。面積が有限である（無限ステップと対応しない）。 -/
def fatA (x : ℝ) : ℝ := 2 * π * ∫ s in (1 : ℝ)..x, (1 / s ^ 2) * √(1 + (2 / s ^ 3) ^ 2)

theorem fatA_le {x : ℝ} (hx : 1 ≤ x) : fatA x ≤ 2 * π * √5 := by
  have hI1 : IntervalIntegrable (fun s : ℝ => (1 / s ^ 2) * √(1 + (2 / s ^ 3) ^ 2)) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have h1 : 1 ≤ s := one_le_mem hx hs
    have h0 : s ≠ 0 := by linarith
    apply ContinuousAt.continuousWithinAt
    have h2 : s ^ 2 ≠ 0 := pow_ne_zero 2 h0
    have h3 : s ^ 3 ≠ 0 := pow_ne_zero 3 h0
    apply ContinuousAt.mul (continuousAt_const.div (continuousAt_id.pow 2) h2)
    apply ContinuousAt.sqrt
    exact continuousAt_const.add ((continuousAt_const.div (continuousAt_id.pow 3) h3).pow 2)
  have hI2 : IntervalIntegrable (fun s : ℝ => √5 * (1 / s) ^ 2) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have h1 : 1 ≤ s := one_le_mem hx hs
    have h0 : s ≠ 0 := by linarith
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.mul ((continuousAt_const.div continuousAt_id h0).pow 2)
  have hmono : (∫ s in (1 : ℝ)..x, (1 / s ^ 2) * √(1 + (2 / s ^ 3) ^ 2)) ≤
      ∫ s in (1 : ℝ)..x, √5 * (1 / s) ^ 2 := by
    apply integral_mono_on hx hI1 hI2
    intro s hs
    have hs1 : 1 ≤ s := hs.1
    have hs0 : 0 < s := by linarith
    have hb : √(1 + (2 / s ^ 3) ^ 2) ≤ √5 := by
      apply Real.sqrt_le_sqrt
      have h3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
      have hd : 2 / s ^ 3 ≤ 2 := div_le_self (by norm_num) h3
      have hd0 : 0 ≤ 2 / s ^ 3 := by positivity
      nlinarith
    have hpos : 0 ≤ 1 / s ^ 2 := by positivity
    calc (1 / s ^ 2) * √(1 + (2 / s ^ 3) ^ 2) ≤ (1 / s ^ 2) * √5 :=
          mul_le_mul_of_nonneg_left hb hpos
      _ = √5 * (1 / s) ^ 2 := by rw [div_pow, one_pow]; ring
  have hval : (∫ s in (1 : ℝ)..x, √5 * (1 / s) ^ 2) = √5 * (hornV x / π) := by
    rw [intervalIntegral.integral_const_mul]
    simp only [hornV]
    field_simp
  have hV := hornV_le hx
  have hV0 : 0 ≤ hornV x / π := by
    rw [hornV_eq hx]
    have hpi := Real.pi_pos
    have h1x : 1 / x ≤ 1 := by
      rw [div_le_one (by linarith)]; exact hx
    have : 0 ≤ π * (1 - 1 / x) := mul_nonneg hpi.le (by linarith)
    positivity
  have hV1 : hornV x / π ≤ 1 := (div_le_one Real.pi_pos).mpr hV
  have h5 : 0 ≤ √5 := Real.sqrt_nonneg 5
  simp only [fatA]
  have hpi : 0 < 2 * π := by positivity
  apply mul_le_mul_of_nonneg_left _ hpi.le
  calc _ ≤ √5 * (hornV x / π) := by rw [← hval]; exact hmono
    _ ≤ √5 * 1 := mul_le_mul_of_nonneg_left hV1 h5
    _ = √5 := mul_one _

end Zeno.Model
