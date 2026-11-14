/-
# ZenoSmale.KleinQuat : 四元数の成分表示と回転作用

定理 K3⁺ の形式解（第 3 版 §3.5 (1)(2)）は、剛な枠の回転 Ψ_rig : A → SO(3) を単位四元数 S³ へ
持ち上げ、S³ の一点 P を避ける明示的な零ホモトピーで縮める。本ファイルはそのための道具である：
四元数を四つの実数の組で表し、積・共役・ノルム・回転作用（Euler–Rodrigues）と、
軸 i, j, k のまわりの回転の持ち上げ E_u(h) = cos h + u sin h の性質を多項式の計算で示す。

規約：q = (q₀, q₁, q₂, q₃) = q₀ + q₁ i + q₂ j + q₃ k、ij = k。
ℝ³ の座標 (q₁, q₂, q₃) を純四元数 q₁ i + q₂ j + q₃ k と同一視する。
rot2 ψ（q₂ 軸まわりの回転）の持ち上げは E_j(ψ/2)、R₁ θ（q₁ 軸まわり）は E_i(θ/2)、
R₃ θ（q₃ 軸まわり）は E_k(θ/2) である。
-/
import Zeno.KleinBase

noncomputable section

namespace Zeno.Model

open Real
open scoped ContDiff

/-! ### 四元数の成分表示 -/

/-- 四元数の成分表示 (q₀, q₁, q₂, q₃)。 -/
abbrev Q4 := ℝ × ℝ × ℝ × ℝ

/-- 四元数の積（ij = k）。 -/
def qmul (p q : Q4) : Q4 :=
  (p.1 * q.1 - p.2.1 * q.2.1 - p.2.2.1 * q.2.2.1 - p.2.2.2 * q.2.2.2,
   p.1 * q.2.1 + p.2.1 * q.1 + p.2.2.1 * q.2.2.2 - p.2.2.2 * q.2.2.1,
   p.1 * q.2.2.1 - p.2.1 * q.2.2.2 + p.2.2.1 * q.1 + p.2.2.2 * q.2.1,
   p.1 * q.2.2.2 + p.2.1 * q.2.2.1 - p.2.2.1 * q.2.1 + p.2.2.2 * q.1)

/-- 共役。 -/
def qconj (q : Q4) : Q4 := (q.1, -q.2.1, -q.2.2.1, -q.2.2.2)

/-- ノルムの 2 乗。 -/
def qnsq (q : Q4) : ℝ := q.1 ^ 2 + q.2.1 ^ 2 + q.2.2.1 ^ 2 + q.2.2.2 ^ 2

/-- 単位元。 -/
def qone : Q4 := (1, 0, 0, 0)

/-- ベクトルを純四元数と見る。 -/
def pureQ (x : V3) : Q4 := (0, x.1, x.2.1, x.2.2)

/-- 四元数のベクトル部分。 -/
def vecQ (q : Q4) : V3 := (q.2.1, q.2.2.1, q.2.2.2)

/-- 回転作用 ρ(q) x = q x q̄（Euler–Rodrigues）。|q| = 1 のとき SO(3) の元である。 -/
def rotQ (q : Q4) (x : V3) : V3 := vecQ (qmul (qmul q (pureQ x)) (qconj q))

theorem qmul_assoc (p q r : Q4) : qmul (qmul p q) r = qmul p (qmul q r) := by
  simp only [qmul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

theorem qconj_mul (p q : Q4) : qconj (qmul p q) = qmul (qconj q) (qconj p) := by
  simp only [qmul, qconj]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

theorem qmul_one (q : Q4) : qmul q qone = q := by
  simp only [qmul, qone]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

theorem one_qmul (q : Q4) : qmul qone q = q := by
  simp only [qmul, qone]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

theorem qconj_one : qconj qone = qone := by
  simp [qconj, qone]

theorem qnsq_mul (p q : Q4) : qnsq (qmul p q) = qnsq p * qnsq q := by
  simp only [qmul, qnsq]
  ring

theorem qnsq_conj (q : Q4) : qnsq (qconj q) = qnsq q := by
  simp only [qconj, qnsq]
  ring

theorem qnsq_one : qnsq qone = 1 := by
  simp [qnsq, qone]

theorem qnsq_nonneg (q : Q4) : 0 ≤ qnsq q := by
  simp only [qnsq]; positivity

theorem qnsq_eq_zero {q : Q4} (h : qnsq q = 0) : q = 0 := by
  simp only [qnsq] at h
  have h1 : q.1 = 0 := by nlinarith [sq_nonneg q.1, sq_nonneg q.2.1, sq_nonneg q.2.2.1, sq_nonneg q.2.2.2]
  have h2 : q.2.1 = 0 := by nlinarith [sq_nonneg q.1, sq_nonneg q.2.1, sq_nonneg q.2.2.1, sq_nonneg q.2.2.2]
  have h3 : q.2.2.1 = 0 := by nlinarith [sq_nonneg q.1, sq_nonneg q.2.1, sq_nonneg q.2.2.1, sq_nonneg q.2.2.2]
  have h4 : q.2.2.2 = 0 := by nlinarith [sq_nonneg q.1, sq_nonneg q.2.1, sq_nonneg q.2.2.1, sq_nonneg q.2.2.2]
  exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

theorem qnsq_smul (c : ℝ) (q : Q4) : qnsq (c • q) = c ^ 2 * qnsq q := by
  simp only [qnsq, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- q̄ q = |q|²。 -/
theorem qconj_mul_self (q : Q4) : qmul (qconj q) q = (qnsq q, 0, 0, 0) := by
  simp only [qmul, qconj, qnsq]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

/-- q q̄ = |q|²。 -/
theorem qmul_conj_self (q : Q4) : qmul q (qconj q) = (qnsq q, 0, 0, 0) := by
  simp only [qmul, qconj, qnsq]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only <;> ring

theorem qmul_smul_left (c : ℝ) (p q : Q4) : qmul (c • p) q = c • qmul p q := by
  simp only [qmul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem qmul_smul_right (c : ℝ) (p q : Q4) : qmul p (c • q) = c • qmul p q := by
  simp only [qmul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem qconj_smul (c : ℝ) (q : Q4) : qconj (c • q) = c • qconj q := by
  simp only [qconj]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-! ### 回転作用 -/

/-- 純四元数の共役作用の実部は 0 である。 -/
theorem re_qmul_pure (q : Q4) (x : V3) : (qmul (qmul q (pureQ x)) (qconj q)).1 = 0 := by
  simp only [qmul, pureQ, qconj]
  ring

theorem pureQ_vecQ {a : Q4} (h : a.1 = 0) : pureQ (vecQ a) = a := by
  obtain ⟨a0, a1, a2, a3⟩ := a
  simp only at h
  simp [pureQ, vecQ, h]

theorem rotQ_one (x : V3) : rotQ qone x = x := by
  simp only [rotQ, qmul, pureQ, qconj, vecQ, qone]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- 回転作用は積を保つ：ρ(pq) = ρ(p) ∘ ρ(q)。 -/
theorem rotQ_mul (p q : Q4) (x : V3) : rotQ (qmul p q) x = rotQ p (rotQ q x) := by
  simp only [rotQ]
  rw [pureQ_vecQ (re_qmul_pure q x), qconj_mul]
  congr 1
  simp only [qmul_assoc]

theorem rotQ_smul (c : ℝ) (q : Q4) (x : V3) : rotQ (c • q) x = c ^ 2 • rotQ q x := by
  simp only [rotQ, qmul, pureQ, qconj, vecQ]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem rotQ_add (q : Q4) (x y : V3) : rotQ q (x + y) = rotQ q x + rotQ q y := by
  simp only [rotQ, qmul, pureQ, qconj, vecQ, Prod.fst_add, Prod.snd_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring

theorem rotQ_smul_vec (q : Q4) (c : ℝ) (x : V3) : rotQ q (c • x) = c • rotQ q x := by
  simp only [rotQ, qmul, pureQ, qconj, vecQ, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    ring

theorem rotQ_neg_vec (q : Q4) (x : V3) : rotQ q (-x) = -rotQ q x := by
  simp only [rotQ, qmul, pureQ, qconj, vecQ, Prod.fst_neg, Prod.snd_neg]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring

/-- 回転作用は内積を |q|⁴ 倍する。 -/
theorem dot_rotQ (q : Q4) (x y : V3) : dot (rotQ q x) (rotQ q y) = qnsq q ^ 2 * dot x y := by
  simp only [rotQ, qmul, pureQ, qconj, vecQ, dot, qnsq]
  ring

theorem nsq_rotQ (q : Q4) (x : V3) : nsq (rotQ q x) = qnsq q ^ 2 * nsq x :=
  dot_rotQ q x x

/-- 外積のノルムの Lagrange 恒等式。 -/
theorem nsq_cross (x y : V3) : nsq (cross x y) = nsq x * nsq y - dot x y ^ 2 := by
  simp only [nsq, dot, cross]
  ring

/-! ### 軸のまわりの回転の持ち上げ -/

/-- E_i(h) = cos h + i sin h。 -/
def Ei (h : ℝ) : Q4 := (cos h, sin h, 0, 0)

/-- E_j(h) = cos h + j sin h。 -/
def Ej (h : ℝ) : Q4 := (cos h, 0, sin h, 0)

/-- E_k(h) = cos h + k sin h。 -/
def Ek (h : ℝ) : Q4 := (cos h, 0, 0, sin h)

theorem qnsq_Ei (h : ℝ) : qnsq (Ei h) = 1 := by
  simp only [qnsq, Ei]; linear_combination sin_sq_add_cos_sq h

theorem qnsq_Ej (h : ℝ) : qnsq (Ej h) = 1 := by
  simp only [qnsq, Ej]; linear_combination sin_sq_add_cos_sq h

theorem qnsq_Ek (h : ℝ) : qnsq (Ek h) = 1 := by
  simp only [qnsq, Ek]; linear_combination sin_sq_add_cos_sq h

theorem Ej_zero : Ej 0 = qone := by simp [Ej, qone]

theorem Ei_zero : Ei 0 = qone := by simp [Ei, qone]

theorem Ek_zero : Ek 0 = qone := by simp [Ek, qone]

/-- q₁ 軸のまわりの角 θ の回転。 -/
def R1 (θ : ℝ) (x : V3) : V3 := (x.1, x.2.1 * cos θ - x.2.2 * sin θ, x.2.1 * sin θ + x.2.2 * cos θ)

/-- q₃ 軸のまわりの角 θ の回転。 -/
def R3 (θ : ℝ) (x : V3) : V3 := (x.1 * cos θ - x.2.1 * sin θ, x.1 * sin θ + x.2.1 * cos θ, x.2.2)

/-- ρ(E_j(h)) = rot2(2h)。 -/
theorem rotQ_Ej (h : ℝ) (x : V3) : rotQ (Ej h) x = rot2 (2 * h) x := by
  have hs := sin_sq_add_cos_sq h
  simp only [rotQ, qmul, pureQ, qconj, vecQ, Ej, rot2, cos_two_mul', sin_two_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only
  · ring
  · linear_combination x.2.1 * hs
  · ring

/-- ρ(E_i(h)) = R₁(2h)。 -/
theorem rotQ_Ei (h : ℝ) (x : V3) : rotQ (Ei h) x = R1 (2 * h) x := by
  have hs := sin_sq_add_cos_sq h
  simp only [rotQ, qmul, pureQ, qconj, vecQ, Ei, R1, cos_two_mul', sin_two_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only
  · linear_combination x.1 * hs
  · ring
  · ring

/-- ρ(E_k(h)) = R₃(2h)。 -/
theorem rotQ_Ek (h : ℝ) (x : V3) : rotQ (Ek h) x = R3 (2 * h) x := by
  have hs := sin_sq_add_cos_sq h
  simp only [rotQ, qmul, pureQ, qconj, vecQ, Ek, R3, cos_two_mul', sin_two_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only
  · ring
  · ring
  · linear_combination x.2.2 * hs

theorem R1_add (a b : ℝ) (x : V3) : R1 (a + b) x = R1 a (R1 b x) := by
  simp only [R1, cos_add, sin_add]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem R1_neg_self (a : ℝ) (x : V3) : R1 (-a) (R1 a x) = x := by
  rw [← R1_add]
  simp [R1]

theorem R1_zero (x : V3) : R1 0 x = x := by simp [R1]

theorem R1_apply_axis (v a b : ℝ) : R1 v (a, b, 0) = (a, b * cos v, b * sin v) := by
  simp [R1]

theorem R1_apply_e3 (v c : ℝ) : R1 v (0, 0, c) = (0, -(c * sin v), c * cos v) := by
  simp only [R1]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem R3_e3 (θ c : ℝ) : R3 θ (0, 0, c) = (0, 0, c) := by simp [R3]

/-! ### 正規化 -/

/-- 正規化 N(q) = q/|q|。 -/
def qnorm (q : Q4) : Q4 := (1 / √(qnsq q)) • q

theorem qnsq_qnorm {q : Q4} (h : qnsq q ≠ 0) : qnsq (qnorm q) = 1 := by
  have hpos : 0 < qnsq q := lt_of_le_of_ne (qnsq_nonneg q) (Ne.symm h)
  simp only [qnorm, qnsq_smul]
  rw [div_pow, one_pow, sq_sqrt hpos.le]
  field_simp

theorem qnorm_of_unit {q : Q4} (h : qnsq q = 1) : qnorm q = q := by
  simp [qnorm, h]

theorem qnorm_smul_pos {c : ℝ} (hc : 0 < c) (q : Q4) : qnorm (c • q) = qnorm q := by
  simp only [qnorm, qnsq_smul, smul_smul]
  congr 1
  rw [sqrt_mul (sq_nonneg c), sqrt_sq hc.le]
  field_simp

/-! ### 滑らかさ -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem _root_.ContDiff.qmul {p q : E → Q4} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun x => Zeno.Model.qmul (p x) (q x)) := by
  have p0 : ContDiff ℝ ∞ (fun x => (p x).1) := contDiff_fst.comp hp
  have p1 : ContDiff ℝ ∞ (fun x => (p x).2.1) := contDiff_fst.comp (contDiff_snd.comp hp)
  have p2 : ContDiff ℝ ∞ (fun x => (p x).2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp hp))
  have p3 : ContDiff ℝ ∞ (fun x => (p x).2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp hp))
  have q0 : ContDiff ℝ ∞ (fun x => (q x).1) := contDiff_fst.comp hq
  have q1 : ContDiff ℝ ∞ (fun x => (q x).2.1) := contDiff_fst.comp (contDiff_snd.comp hq)
  have q2 : ContDiff ℝ ∞ (fun x => (q x).2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp hq))
  have q3 : ContDiff ℝ ∞ (fun x => (q x).2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp hq))
  unfold Zeno.Model.qmul
  fun_prop

theorem _root_.ContDiff.qconj {q : E → Q4} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun x => Zeno.Model.qconj (q x)) := by
  have q0 : ContDiff ℝ ∞ (fun x => (q x).1) := contDiff_fst.comp hq
  have q1 : ContDiff ℝ ∞ (fun x => (q x).2.1) := contDiff_fst.comp (contDiff_snd.comp hq)
  have q2 : ContDiff ℝ ∞ (fun x => (q x).2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp hq))
  have q3 : ContDiff ℝ ∞ (fun x => (q x).2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp hq))
  unfold Zeno.Model.qconj
  fun_prop

theorem _root_.ContDiff.qnsq {q : E → Q4} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun x => Zeno.Model.qnsq (q x)) := by
  have q0 : ContDiff ℝ ∞ (fun x => (q x).1) := contDiff_fst.comp hq
  have q1 : ContDiff ℝ ∞ (fun x => (q x).2.1) := contDiff_fst.comp (contDiff_snd.comp hq)
  have q2 : ContDiff ℝ ∞ (fun x => (q x).2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp hq))
  have q3 : ContDiff ℝ ∞ (fun x => (q x).2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp hq))
  unfold Zeno.Model.qnsq
  fun_prop

theorem _root_.ContDiff.pureQ {x : E → V3} (hx : ContDiff ℝ ∞ x) :
    ContDiff ℝ ∞ (fun t => Zeno.Model.pureQ (x t)) := by
  have x0 : ContDiff ℝ ∞ (fun t => (x t).1) := contDiff_fst.comp hx
  have x1 : ContDiff ℝ ∞ (fun t => (x t).2.1) := contDiff_fst.comp (contDiff_snd.comp hx)
  have x2 : ContDiff ℝ ∞ (fun t => (x t).2.2) := contDiff_snd.comp (contDiff_snd.comp hx)
  unfold Zeno.Model.pureQ
  fun_prop

theorem _root_.ContDiff.vecQ {q : E → Q4} (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun x => Zeno.Model.vecQ (q x)) := by
  have q1 : ContDiff ℝ ∞ (fun x => (q x).2.1) := contDiff_fst.comp (contDiff_snd.comp hq)
  have q2 : ContDiff ℝ ∞ (fun x => (q x).2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp (contDiff_snd.comp hq))
  have q3 : ContDiff ℝ ∞ (fun x => (q x).2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp (contDiff_snd.comp hq))
  unfold Zeno.Model.vecQ
  fun_prop

theorem _root_.ContDiff.rotQ {q : E → Q4} {x : E → V3} (hq : ContDiff ℝ ∞ q) (hx : ContDiff ℝ ∞ x) :
    ContDiff ℝ ∞ (fun t => Zeno.Model.rotQ (q t) (x t)) :=
  ((hq.qmul hx.pureQ).qmul hq.qconj).vecQ

theorem _root_.ContDiff.Ei {h : E → ℝ} (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (fun x => Zeno.Model.Ei (h x)) := by
  unfold Zeno.Model.Ei; fun_prop

theorem _root_.ContDiff.Ej {h : E → ℝ} (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (fun x => Zeno.Model.Ej (h x)) := by
  unfold Zeno.Model.Ej; fun_prop

theorem _root_.ContDiff.Ek {h : E → ℝ} (hh : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (fun x => Zeno.Model.Ek (h x)) := by
  unfold Zeno.Model.Ek; fun_prop

theorem _root_.ContDiff.qnorm {q : E → Q4} (hq : ContDiff ℝ ∞ q) (hne : ∀ x, Zeno.Model.qnsq (q x) ≠ 0) :
    ContDiff ℝ ∞ (fun x => Zeno.Model.qnorm (q x)) := by
  have hn : ContDiff ℝ ∞ (fun x => Zeno.Model.qnsq (q x)) := hq.qnsq
  have hs : ContDiff ℝ ∞ (fun x => √(Zeno.Model.qnsq (q x))) := hn.sqrt hne
  have hinv : ContDiff ℝ ∞ (fun x => 1 / √(Zeno.Model.qnsq (q x))) := by
    refine contDiff_const.div hs fun x => ?_
    exact (sqrt_pos.mpr (lt_of_le_of_ne (qnsq_nonneg _) (Ne.symm (hne x)))).ne'
  unfold Zeno.Model.qnorm
  exact hinv.smul hq

end Smooth

end Zeno.Model
