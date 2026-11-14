/-
# ZenoSmale.KleinRotor : D7 — 回転子（単位四元数）を未知数に加えた出会いの方程式

構想の記録の「実数解を持たない」「非実数解で交叉」（第 3.1 版 付録 C.3、C.4）について、複素数の形に
限らない読みを判定するための命題を加える。既存のファイルの定理の文と証明は変えない。新しい模型は
作らない。使うのは、走者の位置（`runT`、`runA`、`dynT`、`dynA`、`idealT`、`idealA`）と、`KleinQuat` の
四元数の回転作用 `rotQ` だけである。

以下で「実数の解」「非実数の解」は、回転子 u が実数（u = ±1）であるか否かをいう。時刻 t はつねに実数で
ある。各定理は、同じ形の方程式を、異なる模型と導線（理想形、通過の条件を満たす導線、衝突する導線）に
当てはめた結果であり、一つの固定した構成が複数の条件を同時に満たすことを述べるものではない。回転による
対応 A = u T u⁻¹ は、位置の一致でも経路の交わりでもなく、構想の記録の「交叉」の意味を確定するものでは
ない。

1. **実ベクトル空間の上の一次方程式（指定した元 e についての解）**。𝔸 を実ベクトル空間、e ∈ 𝔸 を指定
   した元とする。位置の一次方程式 d₀·e + vₜ·τ = vₐ·τ の解は τ = t∗·e だけである。複素助変数の方程式
   z = r z の解は z = 0 だけである。形成後の方程式の斉次の一次式 g(τ) = r g(τ)（g(τ) = e − τ/t∗）の解は
   τ = t∗·e だけである（`catchup_module_iff`、`parameter_module_iff`、`formed_module_iff`）。解は 𝔸 の
   ベクトルであり、一般には実数ではない（𝔸 = ℂ、e = i なら τ = t∗·i である）。e = 0 なら τ = 0 であり、
   解から時刻 t∗ は復元できない。単位元をもつ実代数（複素数、四元数、八元数、クリフォード代数、テンソル
   代数など）で e = 1 と指定した場合に限り、解は実スカラー t∗·1 である。`formed_module_iff` は一次式の
   同値であり、逆数や射影直線の点の等式を一般の 𝔸 について述べるものではない。
2. **回転子の方程式**。二人の位置 T、A ∈ ℝ³ を純四元数と見て、単位四元数 u を未知数に加えた出会いの
   方程式 A = u T u⁻¹（`rotQ u T = A`）を考える。実数の解（u = ±1）があることは、位置の一致 T = A と
   同値である（`rotor_real_solution_iff`、`rotQ_real_unit`）。本文の方程式 (R) は T ≠ ℘ を定義域に含む
   ので、(R) については T = A ≠ ℘ と同値である。非実数の解があることだけでは、T ≠ A は従わない
   （T = A = i、u = i）。解では二人の ℘ からの距離が等しい（`rotor_solution_nsq`）。その逆（距離が
   等しければ解がある）は、このファイルでは一般には証明していない。方程式は反転 ι と両立する
   （`inv3_rotQ`、`rotor_solution_inv3`）。
3. **静的な面**。どの導線についても、競走の時間の中の解の時刻は t∗ だけである（`static_rotor_time`）。
   t∗ には、軸のまわりの回転子 E_i(−Δ/2)（Δ = V_A(0) − V_T(0)）が解である（`static_rotor_solution`）。
   解ける時刻は、形成後の方程式の解の時刻と同じである（`static_rotor_solvable_iff`）。実数の解がある
   ことは、中央での角度が 2π を法として等しいことと同値である（`static_rotor_real_iff`）。E_i(h) が
   実数であることは、h が π の整数倍であることと同値である（`Ei_real_iff`）。
4. **主定理の導線**。Δ = π + 2πn₁ であり、回転子 E_i(−Δ/2) の実部は 0 である（`main_rotor_re`）。それは
   −1 の平方根であり（`main_rotor_sq`、`qmul_self_of_pure_unit`）、実数でない（`main_rotor_not_real`、
   `not_real_of_pure_unit`）。静的な面の上で、回転子の方程式は t∗ にこの解をもち、実数の解をもたない
   （`klein_rotor_crossing`、`main_centre_angle_not_int`）。宣言の名前の crossing は、構想の記録の
   「交叉」と同じものであることを主張しない。
5. **動く面**。通過の条件を満たす族の上では、実数の解はない（`dyn_rotor_no_real`）。非実数の解が
   その族の上にあることは、証明していない。v について 2π 周期的な族の上で、亀の助変数の角度を 2π の
   整数倍だけ回した点にアキレスがいることは、位置の一致と同値であり（`dyn_parameter_rotor_real_iff`）、
   t∗ には、角度を Δ だけ回した点にアキレスがいる（`dyn_parameter_rotor_solution`）。動的な基底では、
   t∗ の二人の位置は、実部が 0 の単位四元数 k による回転で移り合う（`base_rotor_solution`、
   `rotQ_k_half_turn`）。これは基底についての命題であり、族そのものについての命題ではない。
6. **理想形**。理想形の走者について、回転子の方程式は、亀が ℘ にいない時刻には解をもたない
   （`ideal_rotor_no_solution`）。亀が ℘ にいるのは t∗ だけであり、そのとき二人はともに ℘ にいる
   （`formed_solution_positions`）。
-/
import ZenoSmale.KleinReadings

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open Zeno.Model

/-! ### 実ベクトル空間の上の一次方程式（指定した元 e についての解） -/

/-- **位置の一次方程式の解は τ = t∗·e だけである**：𝔸 を実ベクトル空間、e ∈ 𝔸 を指定した元とする。τ ∈ 𝔸 に
ついて d₀·e + vₜ·τ = vₐ·τ ⟺ τ = t∗·e である。解は 𝔸 のベクトルであり、一般には実数ではない。e = 0 なら
τ = 0 であり、解から t∗ は復元できない。単位元をもつ実代数（複素数、四元数、八元数、クリフォード代数、
テンソル代数など）で e = 1 と指定した場合には、解は実スカラー t∗·1 である。 -/
theorem catchup_module_iff (R : Race) {𝔸 : Type*} [AddCommGroup 𝔸] [Module ℝ 𝔸] (e τ : 𝔸) :
    R.d0 • e + R.vt • τ = R.va • τ ↔ τ = R.tstar • e := by
  have hgap : R.va - R.vt ≠ 0 := R.gap_pos.ne'
  have ht : R.tstar * (R.va - R.vt) = R.d0 := by
    rw [Race.tstar, div_mul_cancel₀ _ hgap]
  constructor
  · intro h
    have h1 : (R.va - R.vt) • τ = R.d0 • e := by
      rw [sub_smul, ← h, add_sub_cancel_right]
    have hc : (R.va - R.vt)⁻¹ * R.d0 = R.tstar := by
      rw [← ht, mul_comm R.tstar, ← mul_assoc, inv_mul_cancel₀ hgap, one_mul]
    calc τ = (R.va - R.vt)⁻¹ • ((R.va - R.vt) • τ) := by
          rw [smul_smul, inv_mul_cancel₀ hgap, one_smul]
      _ = R.tstar • e := by rw [h1, smul_smul, hc]
  · intro h
    have key : R.d0 + R.vt * R.tstar = R.va * R.tstar := by
      linear_combination (-1 : ℝ) * ht
    subst h
    rw [smul_smul, smul_smul, ← add_smul, key]

/-- **複素助変数の方程式の解は 0 だけである**：𝔸 を実ベクトル空間とする。z ∈ 𝔸 について z = r z ⟺ z = 0。 -/
theorem parameter_module_iff (R : Race) {𝔸 : Type*} [AddCommGroup 𝔸] [Module ℝ 𝔸] (z : 𝔸) :
    z = R.r • z ↔ z = 0 := by
  have hr : (1 : ℝ) - R.r ≠ 0 := by
    have := R.r_lt_one
    intro h0
    linarith
  constructor
  · intro h
    have h1 : ((1 : ℝ) - R.r) • z = 0 := by
      rw [sub_smul, one_smul, ← h, sub_self]
    calc z = ((1 : ℝ) - R.r)⁻¹ • (((1 : ℝ) - R.r) • z) := by
          rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
      _ = 0 := by rw [h1, smul_zero]
  · intro h
    rw [h, smul_zero]

/-- **形成後の方程式の斉次の一次式の解は τ = t∗·e だけである**：g(τ) = e − τ/t∗ とおく。g(τ) = r g(τ) ⟺
τ = t∗·e である。これは実ベクトル空間の中の一次式の同値であり、逆数や射影直線を含まない。𝔸 = ℂ、e = 1 の
場合には、形成後の方程式 1/g(τ) = 1/(r g(τ)) を、リーマン球面の点 [1 : g(τ)] と [1 : r g(τ)] の一致と
読んだものにあたり、解 τ = t∗ での共通の点は ∞ = [1 : 0] である。一般の 𝔸 と e（とくに e = 0）については、
この射影的な読みは定義していない。 -/
theorem formed_module_iff (R : Race) {𝔸 : Type*} [AddCommGroup 𝔸] [Module ℝ 𝔸] (e τ : 𝔸) :
    e - R.tstar⁻¹ • τ = R.r • (e - R.tstar⁻¹ • τ) ↔ τ = R.tstar • e := by
  have hT : R.tstar ≠ 0 := R.tstar_pos.ne'
  rw [parameter_module_iff R (e - R.tstar⁻¹ • τ)]
  constructor
  · intro h
    have h1 : R.tstar⁻¹ • τ = e := (sub_eq_zero.mp h).symm
    calc τ = R.tstar • (R.tstar⁻¹ • τ) := by
          rw [smul_smul, mul_inv_cancel₀ hT, one_smul]
      _ = R.tstar • e := by rw [h1]
  · intro h
    subst h
    rw [smul_smul, inv_mul_cancel₀ hT, one_smul, sub_self]

/-! ### 回転子の方程式：実数の解があることは、位置の一致と同値である -/

/-- 実四元数 (a, 0, 0, 0) の回転作用は a² 倍である。 -/
theorem rotQ_real (a : ℝ) (x : V3) : rotQ (a, 0, 0, 0) x = a ^ 2 • x := by
  simp only [rotQ, qmul, pureQ, qconj, vecQ]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

/-- 単位の実四元数（±1）は恒等回転である。 -/
theorem rotQ_real_unit {q : Q4} (hre : q.2.1 = 0 ∧ q.2.2.1 = 0 ∧ q.2.2.2 = 0) (hq : qnsq q = 1)
    (x : V3) : rotQ q x = x := by
  obtain ⟨a, b, c, d⟩ := q
  obtain ⟨hb, hc, hd⟩ := hre
  simp only at hb hc hd
  subst hb hc hd
  have ha : a ^ 2 = 1 := by
    simp only [qnsq] at hq
    linear_combination hq
  rw [rotQ_real, ha, one_smul]

/-- **実数の解があることは、位置の一致と同値である**：単位四元数 u を未知数とする方程式 u x u⁻¹ = y が、
実数の解 u（u = ±1）をもつことは、x = y と同値である。ここでの「実数」は回転子 u についての語である。
非実数の解があることだけでは、x ≠ y は従わない。 -/
theorem rotor_real_solution_iff {x y : V3} :
    (∃ q : Q4, qnsq q = 1 ∧ (q.2.1 = 0 ∧ q.2.2.1 = 0 ∧ q.2.2.2 = 0) ∧ rotQ q x = y) ↔ x = y := by
  constructor
  · rintro ⟨q, hq, hre, h⟩
    rw [← h, rotQ_real_unit hre hq]
  · intro h
    exact ⟨qone, qnsq_one, ⟨rfl, rfl, rfl⟩, by rw [rotQ_one, h]⟩

/-- 回転子の方程式の解では、二人の ℘ からの距離が等しい。 -/
theorem rotor_solution_nsq {q : Q4} (hq : qnsq q = 1) {x y : V3} (h : rotQ q x = y) :
    nsq y = nsq x := by
  rw [← h, nsq_rotQ, hq]
  ring

/-- 単位四元数による回転は、反転 ι(q) = q/|q|² と可換である。 -/
theorem inv3_rotQ {q : Q4} (hq : qnsq q = 1) (x : V3) : inv3 (rotQ q x) = rotQ q (inv3 x) := by
  have hn : nsq (rotQ q x) = nsq x := by
    rw [nsq_rotQ, hq]
    ring
  have e : inv3 x = (1 / nsq x) • x := by
    simp only [inv3]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  have e' : inv3 (rotQ q x) = (1 / nsq x) • rotQ q x := by
    simp only [inv3, hn]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
      simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring
  rw [e', e, rotQ_smul_vec]

/-- 回転子の方程式は反転と両立する：℘ の側の座標での解は、ホーンの側の座標（反転 ι の像）での解である。 -/
theorem rotor_solution_inv3 {q : Q4} (hq : qnsq q = 1) {x y : V3} (h : rotQ q x = y) :
    rotQ q (inv3 x) = inv3 y := by
  rw [← inv3_rotQ hq, h]

/-! ### 実部が 0 の単位四元数 -/

/-- 実部が 0 の単位四元数は、−1 の平方根である。 -/
theorem qmul_self_of_pure_unit {q : Q4} (h0 : q.1 = 0) (hq : qnsq q = 1) :
    qmul q q = (-1, 0, 0, 0) := by
  obtain ⟨a, b, c, d⟩ := q
  simp only at h0
  subst h0
  simp only [qnsq] at hq
  simp only [qmul]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp only
  · linear_combination (-1 : ℝ) * hq
  · ring
  · ring
  · ring

/-- 実部が 0 の単位四元数は、実数でない。 -/
theorem not_real_of_pure_unit {q : Q4} (h0 : q.1 = 0) (hq : qnsq q = 1) :
    ¬ (q.2.1 = 0 ∧ q.2.2.1 = 0 ∧ q.2.2.2 = 0) := by
  rintro ⟨hb, hc, hd⟩
  have h : qnsq q = 0 := by
    simp only [qnsq, h0, hb, hc, hd]
    ring
  rw [h] at hq
  exact zero_ne_one hq

/-- 軸のまわりの回転子 E_i(h) = cos h + i sin h が実数であることは、h が π の整数倍であることと同値で
ある。回転の角度 2h でいえば、2π の整数倍、すなわち恒等回転であることと同値である。 -/
theorem Ei_real_iff (h : ℝ) :
    ((Ei h).2.1 = 0 ∧ (Ei h).2.2.1 = 0 ∧ (Ei h).2.2.2 = 0) ↔ ∃ m : ℤ, h = m * π := by
  constructor
  · rintro ⟨hs, -, -⟩
    have hs' : sin h = 0 := hs
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hs'
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨?_, rfl, rfl⟩
    exact Real.sin_int_mul_pi m

/-! ### 静的な面 -/

/-- 軸のまわりの回転と中央の円：R₁(θ) Σ(0, v) = Σ(0, v − θ)。 -/
theorem R1_Sig_zero {w₀ : ℝ} (h0 : 0 < w₀) (θ v : ℝ) :
    R1 θ (Sig w₀ 0 v) = Sig w₀ 0 (v - θ) := by
  rw [Sig_zero h0, Sig_zero h0, cos_sub, sin_sub]
  simp only [R1]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- **静的な面：回転子の方程式の解の時刻は t∗ だけである**。どの導線（任意の関数）についても、競走の
時間の中で、単位四元数 u が u T(t) u⁻¹ = A(t) を満たせば、t = t∗ である。 -/
theorem static_rotor_time (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (Vt Va : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) {q : Q4} (hq : qnsq q = 1)
    (h : rotQ q (R.runT (Shat w₀) Vt t) = R.runA (Shat w₀) Va t) : t = R.tstar := by
  by_contra htne
  have hn := rotor_solution_nsq hq h
  rw [runT_Shat_eq R h0 h1 _ ht, runA_Shat_eq R h0 h1 _ ht] at hn
  have hlt := nsq_Sig_lt h0.ne' (by nlinarith) (R.abs_r_g_lt htne) (R.abs_g_le ht.1 ht.2)
    (Vt (R.r * R.g t)) (Va (R.g t))
  simp only [Race.runT, Race.runA] at hn
  rw [hn] at hlt
  exact lt_irrefl _ hlt

/-- **静的な面：軸のまわりの回転子は、t∗ に方程式を解く**。Δ = V_A(0) − V_T(0) とおくと、単位四元数
u = E_i(−Δ/2) = cos(Δ/2) − i sin(Δ/2) は、t∗ の亀の位置を t∗ のアキレスの位置に回す。 -/
theorem static_rotor_solution (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (Vt Va : ℝ → ℝ) :
    rotQ (Ei (-((Va 0 - Vt 0) / 2))) (R.runT (Shat w₀) Vt R.tstar) =
      R.runA (Shat w₀) Va R.tstar := by
  have e : Vt 0 - 2 * -((Va 0 - Vt 0) / 2) = Va 0 := by ring
  rw [runT_Shat_eq R h0 h1 _ R.tstar_mem, runA_Shat_eq R h0 h1 _ R.tstar_mem, rotQ_Ei]
  simp only [Race.runT, Race.runA, R.g_tstar, mul_zero]
  rw [R1_Sig_zero h0, e]

/-- **静的な面：回転子の方程式が解ける時刻は、形成後の方程式の解の時刻である**。競走の時間の t について、
u T(t) u⁻¹ = A(t) を満たす単位四元数 u があることは、形成後の方程式 X_A(t) = X_T(t) と同値である。 -/
theorem static_rotor_solvable_iff (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (Vt Va : ℝ → ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    (∃ q : Q4, qnsq q = 1 ∧ rotQ q (R.runT (Shat w₀) Vt t) = R.runA (Shat w₀) Va t) ↔
      invOP (R.g t) = invOP (R.r * R.g t) := by
  rw [formed_meeting_iff]
  constructor
  · rintro ⟨q, hq, h⟩
    exact static_rotor_time R h0 h1 Vt Va ht hq h
  · intro h
    subst h
    exact ⟨Ei (-((Va 0 - Vt 0) / 2)), qnsq_Ei _, static_rotor_solution R h0 h1 Vt Va⟩

/-- **静的な面：実数の解と中央の角度**。どの導線についても、回転子の方程式が競走の時間に実数の解（回転子
u = ±1 の解）をもつことは、中央での二人の角度が 2π を法として等しいことと同値である。 -/
theorem static_rotor_real_iff (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (Vt Va : ℝ → ℝ) :
    (∃ t ∈ Icc 0 (2 * R.tstar), ∃ q : Q4, qnsq q = 1 ∧
        (q.2.1 = 0 ∧ q.2.2.1 = 0 ∧ q.2.2.2 = 0) ∧
        rotQ q (R.runT (Shat w₀) Vt t) = R.runA (Shat w₀) Va t) ↔
      ∃ m : ℤ, Va 0 = Vt 0 + m * (2 * π) := by
  obtain ⟨hne, hiff⟩ := static_collision_iff R h0 h1 Vt Va
  constructor
  · rintro ⟨t, ht, q, hq, hre, h⟩
    have he : R.runT (Shat w₀) Vt t = R.runA (Shat w₀) Va t :=
      rotor_real_solution_iff.mp ⟨q, hq, hre, h⟩
    by_cases htt : t = R.tstar
    · rw [htt] at he
      exact hiff.mp he
    · exact absurd he (hne t ht htt)
  · intro hm
    exact ⟨R.tstar, R.tstar_mem, qone, qnsq_one, ⟨rfl, rfl, rfl⟩, by
      rw [rotQ_one]
      exact hiff.mpr hm⟩

/-! ### 主定理の導線 -/

/-- 主定理の導線では Δ = π + 2πn₁ であり、軸のまわりの回転子 E_i(−Δ/2) の実部は 0 である。 -/
theorem main_rotor_re (n₁ : ℕ) : (Ei (-((π + n₁ * (2 * π)) / 2))).1 = 0 := by
  have e : -((π + n₁ * (2 * π)) / 2) = -(π / 2 + n₁ * π) := by ring
  simp only [Ei]
  rw [e, cos_neg, cos_add, cos_pi_div_two, sin_pi_div_two, sin_nat_mul_pi]
  ring

/-- 主定理の導線での回転子は、−1 の平方根である。 -/
theorem main_rotor_sq (n₁ : ℕ) :
    qmul (Ei (-((π + n₁ * (2 * π)) / 2))) (Ei (-((π + n₁ * (2 * π)) / 2))) = (-1, 0, 0, 0) :=
  qmul_self_of_pure_unit (main_rotor_re n₁) (qnsq_Ei _)

/-- 主定理の導線での回転子は、実数でない。 -/
theorem main_rotor_not_real (n₁ : ℕ) :
    ¬ ((Ei (-((π + n₁ * (2 * π)) / 2))).2.1 = 0 ∧ (Ei (-((π + n₁ * (2 * π)) / 2))).2.2.1 = 0 ∧
        (Ei (-((π + n₁ * (2 * π)) / 2))).2.2.2 = 0) :=
  not_real_of_pure_unit (main_rotor_re n₁) (qnsq_Ei _)

/-- 主定理の導線では、中央での二人の角度は、2π を法として等しくない。 -/
theorem main_centre_angle_not_int (R : Race) (w₀ : ℝ) (n₁ : ℕ) (m : ℤ) :
    VaR R.r w₀ (R.r ^ n₁) n₁ 0 ≠ VtR (R.r ^ n₁) 0 + m * (2 * π) := by
  intro hm
  have hd := centre_angle_diff R w₀ n₁
  have h3 : π * ((1 : ℝ) + 2 * (n₁ : ℝ) - 2 * (m : ℝ)) = 0 := by
    linear_combination hm - hd
  have h4 : (1 : ℝ) + 2 * (n₁ : ℝ) - 2 * (m : ℝ) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h Real.pi_ne_zero
    · exact h
  have h5 : (1 : ℤ) + 2 * (n₁ : ℤ) - 2 * m = 0 := by exact_mod_cast h4
  omega

/-- **主定理の導線（静的な面）：非実数の解があり、実数の解はない**。回転子の方程式 u T(t) u⁻¹ = A(t) は、
t∗ に、実部が 0 の単位四元数（−1 の平方根）を解にもつ。競走の時間に、実数の解はない。二つを合わせると、
t∗ の二人は ℘ から等しい距離の異なる点にいる。これは回転による対応であり、位置の一致でも経路の交わり
でもない。宣言の名前の crossing は、構想の記録の「交叉」と同じものであることを主張しない。 -/
theorem klein_rotor_crossing (R : Race) (n₁ : ℕ) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) :
    (∃ q : Q4, qnsq q = 1 ∧ q.1 = 0 ∧ qmul q q = (-1, 0, 0, 0) ∧
        rotQ q (R.runT (Shat w₀) (VtR (R.r ^ n₁)) R.tstar) =
          R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) R.tstar) ∧
      ¬ ∃ t ∈ Icc 0 (2 * R.tstar), ∃ q : Q4, qnsq q = 1 ∧
        (q.2.1 = 0 ∧ q.2.2.1 = 0 ∧ q.2.2.2 = 0) ∧
        rotQ q (R.runT (Shat w₀) (VtR (R.r ^ n₁)) t) =
          R.runA (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁) t := by
  have hd := centre_angle_diff R w₀ n₁
  refine ⟨?_, ?_⟩
  · have hs := static_rotor_solution R h0 h1 (VtR (R.r ^ n₁)) (VaR R.r w₀ (R.r ^ n₁) n₁)
    rw [hd] at hs
    exact ⟨Ei (-((π + n₁ * (2 * π)) / 2)), qnsq_Ei _, main_rotor_re n₁, main_rotor_sq n₁, hs⟩
  · intro h
    obtain ⟨m, hm⟩ := (static_rotor_real_iff R h0 h1 _ _).mp h
    exact main_centre_angle_not_int R w₀ n₁ m hm

/-! ### 動く面 -/

/-- **動く面：実数の解はない**。通過の条件を満たす族の上では、回転子の方程式は、競走の時間に実数の解を
もたない。非実数の解がその族の上にあることは、この定理は述べない。 -/
theorem dyn_rotor_no_real {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3}
    {F : ℝ → ℝ → ℝ → V3} {Vt Va : ℝ → ℝ} (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va) :
    ¬ ∃ t ∈ Icc 0 (2 * R.tstar), ∃ q : Q4, qnsq q = 1 ∧
        (q.2.1 = 0 ∧ q.2.2.1 = 0 ∧ q.2.2.2 = 0) ∧
        rotQ q (dynT R w₀ F Vt t) = dynA R w₀ F Va t := by
  rintro ⟨t, ht, q, hq, hre, h⟩
  exact P.no_collision t ht (rotor_real_solution_iff.mp ⟨q, hq, hre, h⟩)

/-- **助変数の回転による形：2π の整数倍の解は、位置の一致である**。v について 2π 周期的な族の上で、亀の
助変数の角度を 2π の整数倍だけ回した点にアキレスがいることは、二人が同じ点にいることと同値である。 -/
theorem dyn_parameter_rotor_real_iff (R : Race) (w₀ : ℝ) {F : ℝ → ℝ → ℝ → V3}
    (hper : ∀ s w v : ℝ, F s w (v + 2 * π) = F s w v) (Vt Va : ℝ → ℝ) (t : ℝ) :
    (∃ m : ℤ, dynA R w₀ F Va t =
        F (sched R w₀ t) (R.r * R.g t) (Vt (R.r * R.g t) + m * (2 * π))) ↔
      dynT R w₀ F Vt t = dynA R w₀ F Va t := by
  have hp : Function.Periodic (fun v => F (sched R w₀ t) (R.r * R.g t) v) (2 * π) :=
    fun v => hper _ _ v
  constructor
  · rintro ⟨m, hm⟩
    rw [hm]
    simp only [dynT]
    exact ((hp.int_mul m) (Vt (R.r * R.g t))).symm
  · intro h
    refine ⟨0, ?_⟩
    rw [← h]
    simp only [dynT, Int.cast_zero, zero_mul, add_zero]

/-- **助変数の回転による形：t∗ での解**。t∗ に、アキレスは、亀の助変数の角度を Δ = V_A(0) − V_T(0) だけ
回した点にいる。 -/
theorem dyn_parameter_rotor_solution (R : Race) (w₀ : ℝ) (F : ℝ → ℝ → ℝ → V3) (Vt Va : ℝ → ℝ) :
    dynA R w₀ F Va R.tstar =
      F (sched R w₀ R.tstar) (R.r * R.g R.tstar) (Vt (R.r * R.g R.tstar) + (Va 0 - Vt 0)) := by
  have e : Vt 0 + (Va 0 - Vt 0) = Va 0 := by ring
  simp only [dynA, R.g_tstar, mul_zero]
  rw [e]

/-- q₃ 軸のまわりの半回転：単位四元数 k は (b, 0, a) を (−b, 0, a) に回す。 -/
theorem rotQ_k_half_turn (a b : ℝ) : rotQ (0, 0, 0, 1) (b, 0, a) = (-b, 0, a) := by
  simp only [rotQ, qmul, pureQ, qconj, vecQ]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- **動的な基底：実部が 0 の単位四元数による対応**。動的な基底では、t∗ のアキレスの位置は、t∗ の亀の
位置を単位四元数 k（k² = −1）で回したものである。これは基底についての命題であり、族そのものについての
命題ではない。 -/
theorem base_rotor_solution (R : Race) {w₀ c : ℝ} (h0 : 0 < w₀) (hc : 0 < c) (n₁ : ℕ) :
    rotQ (0, 0, 0, 1) (baseT R w₀ c R.tstar) = baseA R w₀ c n₁ R.tstar := by
  obtain ⟨hT, hA⟩ := Model.base_tstar h0 R hc n₁
  rw [hT, hA, rotQ_k_half_turn]

/-! ### 理想形 -/

/-- **理想形：有限の領域に解はない**。理想形の走者について、回転子の方程式は、亀が ℘ にいない時刻には
解をもたない。亀が ℘ にいる時刻は t∗ だけであり、そのとき二人はともに ℘（ホーンの側の座標では理想点
∞）にいる（`formed_solution_positions`）。 -/
theorem ideal_rotor_no_solution (R : Race) :
    ¬ ∃ t ∈ Icc 0 (2 * R.tstar), ∃ q : Q4, qnsq q = 1 ∧ R.idealT t ≠ wp ∧
        rotQ q (R.idealT t) = R.idealA t := by
  rintro ⟨t, ht, q, hq, hne, h⟩
  by_cases htt : t = R.tstar
  · apply hne
    rw [htt]
    simp only [Race.idealT, R.g_tstar, mul_zero, G_zero]
  · have hn := rotor_solution_nsq hq h
    have hlt := nsq_G_lt (R.abs_r_g_lt htt) (R.abs_g_le ht.1 ht.2) 0 (theta R.r (R.g t))
    simp only [Race.idealT, Race.idealA] at hn
    rw [hn] at hlt
    exact lt_irrefl _ hlt

end Zeno.Smale
