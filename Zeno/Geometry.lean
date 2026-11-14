/-
# Zeno.Geometry : α の巻き込み G と法線 N（【設定】の幾何）

α は平面 (w, v) で、v の周期 2π で丸められる。
℘ は反転座標の原点で、円 {w = 0} がそこへ潰れる。

ここの定理は恒等式であり、見做しは一つも含まない。
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

namespace Zeno.Model

open Real

/-- 周囲の空間 ℝ³（座標で扱う）。 -/
abbrev V3 := ℝ × ℝ × ℝ

/-- 内積 -/
def dot (a b : V3) : ℝ := a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

/-- 外積 -/
def cross (a b : V3) : V3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
   a.2.2 * b.1 - a.1 * b.2.2,
   a.1 * b.2.1 - a.2.1 * b.1)

/-- 分母 D(w) = 1 + w⁴ -/
def D (w : ℝ) : ℝ := 1 + w ^ 4

theorem D_pos (w : ℝ) : 0 < D w := by unfold D; positivity
theorem D_ne (w : ℝ) : D w ≠ 0 := (D_pos w).ne'

/-- ℘：反転座標の原点。 -/
def wp : V3 := (0, 0, 0)

/-- α の巻き込み G(w, v) = (w, w³ cos v, w³ sin v)/D。ラッパ対の反転像である。 -/
def G (w v : ℝ) : V3 := (w / D w, w ^ 3 * cos v / D w, w ^ 3 * sin v / D w)

/-- 滑らかな法線場 N(w, v)。w = 0 でも消えない。 -/
def N (w v : ℝ) : V3 :=
  (-(3 * w ^ 2 - w ^ 6), (1 - 3 * w ^ 4) * cos v, (1 - 3 * w ^ 4) * sin v)

/-- ∂G/∂w -/
def Tw (w v : ℝ) : V3 :=
  ((1 - 3 * w ^ 4) / D w ^ 2,
   w ^ 2 * (3 - w ^ 4) * cos v / D w ^ 2,
   w ^ 2 * (3 - w ^ 4) * sin v / D w ^ 2)

/-- ∂G/∂v -/
def Tv (w v : ℝ) : V3 := (0, -(w ^ 3 * sin v) / D w, w ^ 3 * cos v / D w)

/-- G は w = 0 の円全体を ℘ へ潰す（設定2）。 -/
theorem G_zero (v : ℝ) : G 0 v = wp := by
  simp [G, wp, D]

/-- v の周期（「丸める」）。 -/
theorem G_periodic (w v : ℝ) : G w (v + 2 * π) = G w v := by
  simp [G]

theorem N_periodic (w v : ℝ) : N w (v + 2 * π) = N w v := by
  simp [N]

/-! ### 接ベクトルは本当に導関数である -/

theorem hasDerivAt_D (w : ℝ) : HasDerivAt D (4 * w ^ 3) w := by
  have h := (hasDerivAt_pow 4 w).const_add 1
  have e : D = fun x => 1 + x ^ 4 := rfl
  rw [e]
  convert h using 1

theorem hasDerivAt_a (w : ℝ) :
    HasDerivAt (fun w : ℝ => w / D w) ((1 - 3 * w ^ 4) / D w ^ 2) w := by
  have h := (hasDerivAt_id' w).div (hasDerivAt_D w) (D_ne w)
  convert h using 1
  unfold D; ring

theorem hasDerivAt_b_mul (c w : ℝ) :
    HasDerivAt (fun w : ℝ => w ^ 3 * c / D w) (w ^ 2 * (3 - w ^ 4) * c / D w ^ 2) w := by
  have h3 : HasDerivAt (fun w : ℝ => w ^ 3) (3 * w ^ 2) w := by
    simpa using hasDerivAt_pow 3 w
  have h := (h3.mul_const c).div (hasDerivAt_D w) (D_ne w)
  convert h using 1
  unfold D; ring

theorem hasDerivAt_G_w (w v : ℝ) : HasDerivAt (fun w => G w v) (Tw w v) w :=
  (hasDerivAt_a w).prodMk ((hasDerivAt_b_mul (cos v) w).prodMk (hasDerivAt_b_mul (sin v) w))

theorem hasDerivAt_G_v (w v : ℝ) : HasDerivAt (fun v => G w v) (Tv w v) v := by
  have h0 : HasDerivAt (fun _ : ℝ => w / D w) 0 v := hasDerivAt_const v _
  have h1 : HasDerivAt (fun v : ℝ => w ^ 3 * cos v / D w) (-(w ^ 3 * sin v) / D w) v := by
    have h := ((hasDerivAt_cos v).const_mul (w ^ 3)).div_const (D w)
    convert h using 1
    ring
  have h2 : HasDerivAt (fun v : ℝ => w ^ 3 * sin v / D w) (w ^ 3 * cos v / D w) v :=
    ((hasDerivAt_sin v).const_mul (w ^ 3)).div_const (D w)
  exact h0.prodMk (h1.prodMk h2)

/-! ### N は単位化できる法線である -/

/-- |N|² = D³ > 0。特に N は w = 0 でも消えない。 -/
theorem dot_N_N (w v : ℝ) : dot (N w v) (N w v) = D w ^ 3 := by
  simp only [dot, N, D]
  linear_combination (1 - 3 * w ^ 4) ^ 2 * sin_sq_add_cos_sq v

theorem N_ne_zero (w v : ℝ) : N w v ≠ wp := by
  intro h
  have h1 := dot_N_N w v
  rw [h] at h1
  have h2 : 0 < D w ^ 3 := pow_pos (D_pos w) 3
  simp [dot, wp] at h1
  rw [← h1] at h2
  exact lt_irrefl _ h2

/-- N ⟂ ∂G/∂w -/
theorem dot_N_Tw (w v : ℝ) : dot (N w v) (Tw w v) = 0 := by
  have hD := D_ne w
  simp only [dot, N, Tw]
  field_simp
  linear_combination (w ^ 2 * (3 - w ^ 4) * (1 - 3 * w ^ 4)) * sin_sq_add_cos_sq v

/-- N ⟂ ∂G/∂v -/
theorem dot_N_Tv (w v : ℝ) : dot (N w v) (Tv w v) = 0 := by
  have hD := D_ne w
  simp only [dot, N, Tv]
  field_simp
  ring

/-! ### 面の値 -/

/-- α の向きから決まる法線は N の w³/D³ 倍である。w = 0 で向きが消える。 -/
theorem cross_Tv_Tw (w v : ℝ) :
    cross (Tv w v) (Tw w v) =
      (w ^ 3 / D w ^ 3 * (N w v).1,
       w ^ 3 / D w ^ 3 * (N w v).2.1,
       w ^ 3 / D w ^ 3 * (N w v).2.2) := by
  have hD := D_ne w
  simp only [cross, Tv, Tw, N]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    field_simp
    linear_combination (-(w ^ 5 * (3 - w ^ 4))) * sin_sq_add_cos_sq v
  · simp only
    field_simp
    ring
  · simp only
    field_simp
    ring

/-! ### 周囲の空間での内外。{Φ = 0} はラッパ対の反転像 -/

/-- |q|² -/
def nsq (q : V3) : ℝ := dot q q

/-- 陰関数 Φ(q) = q₁²(q₂² + q₃²) − |q|⁸。Φ > 0 がラッパの外側に当たる。 -/
def Phi (q : V3) : ℝ := q.1 ^ 2 * (q.2.1 ^ 2 + q.2.2 ^ 2) - nsq q ^ 4

/-- Φ の勾配 -/
def gradPhi (q : V3) : V3 :=
  (2 * q.1 * (q.2.1 ^ 2 + q.2.2 ^ 2) - 8 * nsq q ^ 3 * q.1,
   2 * q.1 ^ 2 * q.2.1 - 8 * nsq q ^ 3 * q.2.1,
   2 * q.1 ^ 2 * q.2.2 - 8 * nsq q ^ 3 * q.2.2)

theorem nsq_G (w v : ℝ) : nsq (G w v) = w ^ 2 / D w := by
  have hD := D_ne w
  simp only [nsq, dot, G]
  field_simp
  simp only [D]
  linear_combination (w ^ 6) * sin_sq_add_cos_sq v

/-- G は {Φ = 0} の上にある。 -/
theorem Phi_G (w v : ℝ) : Phi (G w v) = 0 := by
  have hD := D_ne w
  simp only [Phi, nsq_G]
  simp only [G]
  field_simp
  linear_combination (w ^ 8) * sin_sq_add_cos_sq v

/-- ∇Φ(G) は N の 2w⁵/D⁴ 倍である。 -/
theorem gradPhi_G (w v : ℝ) :
    gradPhi (G w v) =
      (2 * w ^ 5 / D w ^ 4 * (N w v).1,
       2 * w ^ 5 / D w ^ 4 * (N w v).2.1,
       2 * w ^ 5 / D w ^ 4 * (N w v).2.2) := by
  have hD := D_ne w
  simp only [gradPhi, nsq_G]
  simp only [G, N]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only
    field_simp
    simp only [D]
    linear_combination (2 * w ^ 7 * (1 + w ^ 4)) * sin_sq_add_cos_sq v
  · simp only
    field_simp
    simp only [D]
    ring
  · simp only
    field_simp
    simp only [D]
    ring

/-- ⟨∇Φ(G), N⟩ = 2w⁵/D -/
theorem dot_gradPhi_N (w v : ℝ) : dot (gradPhi (G w v)) (N w v) = 2 * w ^ 5 / D w := by
  have hD := D_ne w
  have h := dot_N_N w v
  rw [gradPhi_G]
  simp only [dot] at h ⊢
  calc _ = 2 * w ^ 5 / D w ^ 4 * ((N w v).1 * (N w v).1 + (N w v).2.1 * (N w v).2.1
            + (N w v).2.2 * (N w v).2.2) := by ring
    _ = 2 * w ^ 5 / D w := by rw [h]; field_simp

/-! ### 反転するとラッパ -/

/-- 反転 ι(q) = q/|q|² -/
def inv3 (q : V3) : V3 := (q.1 / nsq q, q.2.1 / nsq q, q.2.2 / nsq q)

/-- 証明C 2.1 の右ラッパ -/
def FR (u v : ℝ) : V3 := (u, cos v / u, sin v / u)

/-- 証明C 2.1 の左ラッパ -/
def FL (u v : ℝ) : V3 := (-u, cos v / u, sin v / u)

theorem inv3_G {w : ℝ} (hw : w ≠ 0) (v : ℝ) :
    inv3 (G w v) = (1 / w, w * cos v, w * sin v) := by
  have hD := D_ne w
  simp only [inv3, nsq_G]
  simp only [G]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; field_simp
  · simp only; field_simp
  · simp only; field_simp

/-- 右岸の反転像は右ラッパである。 -/
theorem inv3_G_right {u : ℝ} (hu : u ≠ 0) (v : ℝ) : inv3 (G (1 / u) v) = FR u v := by
  have hw : (1 / u) ≠ 0 := one_div_ne_zero hu
  rw [inv3_G hw]
  simp only [FR]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp
  · simp only; ring
  · simp only; ring

/-- 左岸の反転像は左ラッパである（v が π ずれる）。 -/
theorem inv3_G_left {u : ℝ} (hu : u ≠ 0) (v : ℝ) : inv3 (G (-(1 / u)) v) = FL u (v + π) := by
  have hw : (-(1 / u)) ≠ 0 := neg_ne_zero.mpr (one_div_ne_zero hu)
  rw [inv3_G hw]
  simp only [FL, cos_add_pi, sin_add_pi]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; field_simp
  · simp only; ring
  · simp only; ring

/-- Φ はラッパの方程式 x²ρ² = 1 の反転である。 -/
theorem Phi_eq_horn {q : V3} (hq : nsq q ≠ 0) :
    Phi q = nsq q ^ 4 * ((inv3 q).1 ^ 2 * ((inv3 q).2.1 ^ 2 + (inv3 q).2.2 ^ 2) - 1) := by
  simp only [Phi, inv3]
  field_simp

/-! ### 対称性 -/

/-- 鏡映 x ↦ −x（℘ を通る平面に関する）。 -/
def mirror (q : V3) : V3 := (-q.1, q.2.1, q.2.2)

theorem D_neg (w : ℝ) : D (-w) = D w := by
  unfold D; ring

/-- G は w について奇（点対称）。 -/
theorem G_odd (w v : ℝ) : G (-w) v = -G w v := by
  simp only [G, D_neg]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_neg]; ring
  · simp only [Prod.fst_neg, Prod.snd_neg]; ring
  · simp only [Prod.snd_neg]; ring

/-- N は w について偶。 -/
theorem N_even (w v : ℝ) : N (-w) v = N w v := by
  simp only [N]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; ring
  · simp only; ring
  · simp only; ring

/-- 左右対称（鏡映は v を π ずらす）。 -/
theorem G_mirror (w v : ℝ) : G (-w) (v + π) = mirror (G w v) := by
  simp only [G, D_neg, mirror, cos_add_pi, sin_add_pi]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only; ring
  · simp only; ring
  · simp only; ring

/-- 鏡映での N の変換。 -/
theorem N_mirror (w v : ℝ) : N (-w) (v + π) = -mirror (N w v) := by
  simp only [N, mirror, cos_add_pi, sin_add_pi]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_neg]; ring
  · simp only [Prod.fst_neg, Prod.snd_neg]; ring
  · simp only [Prod.snd_neg]; ring

end Zeno.Model
