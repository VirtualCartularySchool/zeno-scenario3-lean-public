/-
# Zeno.Race : 競走

g(t) = (亀の位置 − アキレスの位置)/d₀ を w に読む。これは編者の辞書であり、原文の主張ではない。
-/
import Zeno.Infinity

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology OnePoint

/-- 等速の競走。 -/
structure Race where
  d0 : ℝ
  vt : ℝ
  va : ℝ
  hd : 0 < d0
  hvt : 0 < vt
  hlt : vt < va

namespace Race

variable (R : Race)

/-- 亀の位置 -/
def T (t : ℝ) : ℝ := R.d0 + R.vt * t
/-- アキレスの位置 -/
def A (t : ℝ) : ℝ := R.va * t
/-- 標準解の時刻 t∗。消えない。 -/
def tstar : ℝ := R.d0 / (R.va - R.vt)
/-- 正規化した差 -/
def g (t : ℝ) : ℝ := (R.T t - R.A t) / R.d0
/-- 比 r = vₜ/vₐ -/
def r : ℝ := R.vt / R.va
/-- n ステップ後の時刻 -/
def tn (n : ℕ) : ℝ := R.tstar * (1 - R.r ^ n)

theorem va_pos : 0 < R.va := R.hvt.trans R.hlt
theorem gap_pos : 0 < R.va - R.vt := sub_pos.mpr R.hlt
theorem tstar_pos : 0 < R.tstar := div_pos R.hd R.gap_pos
theorem r_pos : 0 < R.r := div_pos R.hvt R.va_pos
theorem r_lt_one : R.r < 1 := (div_lt_one R.va_pos).mpr R.hlt

/-- g(t) = 1 − t/t∗ -/
theorem g_eq (t : ℝ) : R.g t = 1 - t / R.tstar := by
  have h1 := R.hd.ne'
  have h2 := R.gap_pos.ne'
  simp only [g, T, A, tstar]
  field_simp
  ring

/-- n ステップ後の差は rⁿ -/
theorem g_tn (n : ℕ) : R.g (R.tn n) = R.r ^ n := by
  have h := R.tstar_pos.ne'
  rw [g_eq]
  simp only [tn]
  field_simp
  ring

/-- Zeno のステップ。アキレスは n + 1 歩目に、亀の n 歩目の位置に着く。 -/
theorem A_succ_eq_T (n : ℕ) : R.A (R.tn (n + 1)) = R.T (R.tn n) := by
  have h1 := R.gap_pos.ne'
  have h2 := R.va_pos.ne'
  simp only [A, T, tn, tstar, r, pow_succ]
  field_simp
  ring

/-- n ステップの時刻は t∗ に収束する。 -/
theorem tendsto_tn : Tendsto R.tn atTop (𝓝 R.tstar) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one R.r_pos.le R.r_lt_one
  have h2 : Tendsto (fun n => R.tstar * (1 - R.r ^ n)) atTop (𝓝 (R.tstar * (1 - 0))) :=
    (tendsto_const_nhds.sub h).const_mul _
  have e : R.tn = fun n => R.tstar * (1 - R.r ^ n) := rfl
  rw [e]
  simpa using h2

/-- 差の符号は順序そのものである。 -/
theorem g_pos_iff (t : ℝ) : 0 < R.g t ↔ R.A t < R.T t := by
  simp only [g]
  rw [div_pos_iff_of_pos_right R.hd, sub_pos]

theorem g_neg_iff (t : ℝ) : R.g t < 0 ↔ R.T t < R.A t := by
  simp only [g]
  rw [div_lt_iff₀ R.hd, zero_mul, sub_neg]

theorem g_tstar : R.g R.tstar = 0 := by
  have h := R.tstar_pos.ne'
  rw [g_eq]; field_simp; ring

theorem g_eq_zero_iff (t : ℝ) : R.g t = 0 ↔ t = R.tstar := by
  have h := R.tstar_pos.ne'
  rw [g_eq]
  constructor
  · intro h0
    have : t / R.tstar = 1 := by linarith
    field_simp at this
    linarith
  · rintro rfl; field_simp; ring

end Race

end Zeno.Model
