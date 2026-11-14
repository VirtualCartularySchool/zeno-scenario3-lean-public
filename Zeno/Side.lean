/-
# Zeno.Side : 表裏の基準と、余向きの剛性

表裏は曲面の助変数にも走者にもよらない周囲の関数 Φ で読む（172 の「両端の独立な基準」）。
`Front`（外側）と `Back`（内側）は位置 q と法線 n の組の性質である。

連結な定義域の上で、連続で消えない法線場は基準の場の定符号の倍に限る（`rigid_normal`）。
走者がどちらの面に立っていても、そのラベルが岸の間で変わるかどうかはこの定理で決まる。
-/
import Zeno.Geometry
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology

/-! ### 基準 -/

/-- Φ の法線方向の微分。正なら n はホーンの外側を向く。 -/
def side (q n : V3) : ℝ := dot (gradPhi q) n

/-- 表（外側）。 -/
def Front (q n : V3) : Prop := 0 < side q n

/-- 裏（内側）。 -/
def Back (q n : V3) : Prop := side q n < 0

/-- 通過則 E：枠 (q, n) を (−q, n) へ送る。 -/
def Everse {V : Type*} [Neg V] (f : V × V) : V × V := (-f.1, f.2)

/-! ### 内積と外積の代数 -/

theorem dot_smul_right (a : V3) (c : ℝ) (b : V3) : dot a (c • b) = c * dot a b := by
  simp only [dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem dot_neg_right (a b : V3) : dot a (-b) = -dot a b := by
  simp only [dot, Prod.fst_neg, Prod.snd_neg]; ring

theorem side_smul (q : V3) (c : ℝ) (n : V3) : side q (c • n) = c * side q n :=
  dot_smul_right _ _ _

theorem side_neg (q n : V3) : side q (-n) = -side q n :=
  dot_neg_right _ _

theorem nsq_neg (q : V3) : nsq (-q) = nsq q := by
  simp only [nsq, dot, Prod.fst_neg, Prod.snd_neg]; ring

theorem gradPhi_neg (q : V3) : gradPhi (-q) = -gradPhi q := by
  simp only [gradPhi, nsq_neg, Prod.fst_neg, Prod.snd_neg]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_neg]; ring
  · simp only [Prod.fst_neg, Prod.snd_neg]; ring
  · simp only [Prod.snd_neg]; ring

/-- 対蹠点では Φ の法線微分の符号が変わる。 -/
theorem side_neg_pos (q n : V3) : side (-q) n = -side q n := by
  simp only [side, gradPhi_neg, dot, Prod.fst_neg, Prod.snd_neg]; ring

theorem cross_smul_right (a : V3) (c : ℝ) (b : V3) : cross a (c • b) = c • cross a b := by
  simp only [cross, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem cross_neg_left (a b : V3) : cross (-a) b = -cross a b := by
  simp only [cross, Prod.fst_neg, Prod.snd_neg]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring

theorem cross_neg_right (a b : V3) : cross a (-b) = -cross a b := by
  simp only [cross, Prod.fst_neg, Prod.snd_neg]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring

/-- a、b の両方に直交するベクトルは a × b に平行である。 -/
theorem cross_of_perp {n a b : V3} (h1 : dot n a = 0) (h2 : dot n b = 0) :
    cross n (cross a b) = wp := by
  simp only [dot] at h1 h2
  simp only [cross, wp]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; linear_combination (a.1) * h2 - (b.1) * h1
  · simp only; linear_combination (a.2.1) * h2 - (b.2.1) * h1
  · simp only; linear_combination (a.2.2) * h2 - (b.2.2) * h1

/-- u × v = 0 なら (v·v) u = (u·v) v。 -/
theorem smul_of_cross_eq {u v : V3} (h : cross u v = wp) : dot v v • u = dot u v • v := by
  have c1 : u.2.1 * v.2.2 - u.2.2 * v.2.1 = 0 := congrArg Prod.fst h
  have c2 : u.2.2 * v.1 - u.1 * v.2.2 = 0 := congrArg (fun z : V3 => z.2.1) h
  have c3 : u.1 * v.2.1 - u.2.1 * v.1 = 0 := congrArg (fun z : V3 => z.2.2) h
  simp only [dot]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.smul_fst, smul_eq_mul]
    linear_combination (-v.2.2) * c2 + (v.2.1) * c3
  · simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (v.2.2) * c1 - (v.1) * c3
  · simp only [Prod.smul_snd, smul_eq_mul]
    linear_combination (-v.2.1) * c1 + (v.1) * c2

theorem dot_self_ne {u : V3} (h : u ≠ wp) : dot u u ≠ 0 := by
  intro h0
  apply h
  simp only [dot] at h0
  have h1 : u.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2.1, sq_nonneg u.2.2]
  have h2 : u.2.1 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2.1, sq_nonneg u.2.2]
  have h3 : u.2.2 = 0 := by nlinarith [sq_nonneg u.1, sq_nonneg u.2.1, sq_nonneg u.2.2]
  exact Prod.ext h1 (Prod.ext h2 h3)

theorem continuous_dot : Continuous fun p : V3 × V3 => dot p.1 p.2 := by
  unfold dot; fun_prop

theorem continuous_cross : Continuous fun p : V3 × V3 => cross p.1 p.2 := by
  unfold cross; fun_prop

/-! ### 定符号 -/

theorem const_sign_of_ne {α : Type*} [TopologicalSpace α] [PreconnectedSpace α] {c : α → ℝ}
    (hc : Continuous c) (hne : ∀ p, c p ≠ 0) : (∀ p, 0 < c p) ∨ (∀ p, c p < 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := hcon
  obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge hc ⟨p, hp⟩ ⟨q, hq⟩
  exact hne x hx

/-! ### 余向きの剛性 -/

/-- **余向きの剛性**。N₀ は連続で消えない場、n は連続で消えない場で、稠密な集合の上で N₀ に平行とする。
このとき n = c N₀ で、c は連続で定符号である。 -/
theorem rigid_normal {α : Type*} [TopologicalSpace α] [PreconnectedSpace α] {N₀ n : α → V3}
    (hN : Continuous N₀) (hN0 : ∀ p, N₀ p ≠ wp) (hn : Continuous n) (hn0 : ∀ p, n p ≠ wp)
    {S : Set α} (hS : Dense S) (hpar : ∀ p ∈ S, cross (n p) (N₀ p) = wp) :
    ∃ c : α → ℝ, Continuous c ∧ (∀ p, n p = c p • N₀ p) ∧ ((∀ p, 0 < c p) ∨ (∀ p, c p < 0)) := by
  have hcr : Continuous fun p => cross (n p) (N₀ p) := continuous_cross.comp (hn.prodMk hN)
  have hall : ∀ p, cross (n p) (N₀ p) = wp := by
    intro p
    exact congrFun (Continuous.ext_on hS hcr continuous_const hpar) p
  have hdd : ∀ p, dot (N₀ p) (N₀ p) ≠ 0 := fun p => dot_self_ne (hN0 p)
  let c : α → ℝ := fun p => dot (n p) (N₀ p) / dot (N₀ p) (N₀ p)
  have hc : Continuous c := by
    refine (continuous_dot.comp (hn.prodMk hN)).div (continuous_dot.comp (hN.prodMk hN)) hdd
  have hsm : ∀ p, n p = c p • N₀ p := by
    intro p
    have h := smul_of_cross_eq (hall p)
    have e : n p = (dot (N₀ p) (N₀ p))⁻¹ • (dot (N₀ p) (N₀ p) • n p) := by
      rw [smul_smul, inv_mul_cancel₀ (hdd p), one_smul]
    rw [e, h, smul_smul]
    simp only [c, div_eq_inv_mul]
  have hne : ∀ p, c p ≠ 0 := by
    intro p h0
    apply hn0 p
    rw [hsm p, h0, zero_smul]
    rfl
  exact ⟨c, hc, hsm, const_sign_of_ne hc hne⟩

/-- 定符号の倍なので、二点でのラベルの積の符号は基準の場で計算できる。 -/
theorem side_mul_of_rigid {α : Type*} {n N₀ : α → V3} {c : α → ℝ}
    (hsm : ∀ p, n p = c p • N₀ p) (hc : (∀ p, 0 < c p) ∨ (∀ p, c p < 0))
    {q₁ q₂ : V3} {p₁ p₂ : α} :
    (side q₁ (N₀ p₁) * side q₂ (N₀ p₂) < 0 → side q₁ (n p₁) * side q₂ (n p₂) < 0) ∧
    (0 < side q₁ (N₀ p₁) * side q₂ (N₀ p₂) → 0 < side q₁ (n p₁) * side q₂ (n p₂)) := by
  have e : side q₁ (n p₁) * side q₂ (n p₂) =
      (c p₁ * c p₂) * (side q₁ (N₀ p₁) * side q₂ (N₀ p₂)) := by
    rw [hsm p₁, hsm p₂, side_smul, side_smul]; ring
  have hpos : 0 < c p₁ * c p₂ := by
    rcases hc with h | h
    · exact mul_pos (h _) (h _)
    · exact mul_pos_of_neg_of_neg (h _) (h _)
  constructor
  · intro h; rw [e]; exact mul_neg_of_pos_of_neg hpos h
  · intro h; rw [e]; exact mul_pos hpos h

end Zeno.Model
