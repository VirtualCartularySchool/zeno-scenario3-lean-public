/-
# Zeno.Mobius : 読み M2 の部品（無限遠直線のまわりのメビウスの帯）

平面 α の助変数 y = e^{iv}/w（w ≠ 0 は符号つき）は、円柱 ℝ × S¹ の対合
τ(w, v) = (−w, v + π) による商である（`Ypp_deck`）。w = 0 の円を加えると、
α は射影平面になり、w = 0 の円は無限遠直線である。

無限遠直線の近くの明示的なはめ込み（芯の模型）は
  C(w, v) = (−w cos v, (k + w sin v) cos 2v, (k + w sin v) sin 2v)
で、τ で不変であり（`mobC_deck`）、すべての (w, v) ではめ込みである（`mobC_cross_ne`）。
芯 C(0, v) は半径 k の円を二周し、帯の幅の向きは一周で半回転する。
-/
import Zeno.Uniform

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### 芯の模型 -/

/-- 芯の模型 C(w, v)。k は芯の円の半径。 -/
def mobC (k w v : ℝ) : V3 :=
  (-(w * cos v), (k + w * sin v) * cos (2 * v), (k + w * sin v) * sin (2 * v))

/-- ∂C/∂w（帯の幅の向き。単位ベクトル）。 -/
def mobCw (v : ℝ) : V3 := (-cos v, sin v * cos (2 * v), sin v * sin (2 * v))

/-- ∂C/∂v -/
def mobCv (k w v : ℝ) : V3 :=
  (w * sin v,
   w * cos v * cos (2 * v) - 2 * (k + w * sin v) * sin (2 * v),
   w * cos v * sin (2 * v) + 2 * (k + w * sin v) * cos (2 * v))

theorem cos_two_mul_add_pi (v : ℝ) : cos (2 * (v + π)) = cos (2 * v) := by
  rw [show 2 * (v + π) = 2 * v + 2 * π by ring, cos_add_two_pi]

theorem sin_two_mul_add_pi (v : ℝ) : sin (2 * (v + π)) = sin (2 * v) := by
  rw [show 2 * (v + π) = 2 * v + 2 * π by ring, sin_add_two_pi]

/-- **τ 不変性**：C(−w, v + π) = C(w, v)。 -/
theorem mobC_deck (k w v : ℝ) : mobC k (-w) (v + π) = mobC k w v := by
  simp only [mobC, cos_add_pi, sin_add_pi, cos_two_mul_add_pi, sin_two_mul_add_pi]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem mobC_periodic (k w v : ℝ) : mobC k w (v + 2 * π) = mobC k w v := by
  have h1 : cos (2 * (v + 2 * π)) = cos (2 * v) := by
    rw [show 2 * (v + 2 * π) = 2 * v + 2 * π + 2 * π by ring, cos_add_two_pi, cos_add_two_pi]
  have h2 : sin (2 * (v + 2 * π)) = sin (2 * v) := by
    rw [show 2 * (v + 2 * π) = 2 * v + 2 * π + 2 * π by ring, sin_add_two_pi, sin_add_two_pi]
  simp only [mobC, cos_add_two_pi, sin_add_two_pi, h1, h2]

theorem hasDerivAt_mobC_w (k w v : ℝ) : HasDerivAt (fun w => mobC k w v) (mobCw v) w := by
  have h1 : HasDerivAt (fun w : ℝ => -(w * cos v)) (-cos v) w := by
    have h := ((hasDerivAt_id' w).mul_const (cos v)).neg
    convert h using 1; ring
  have hK : HasDerivAt (fun w : ℝ => k + w * sin v) (sin v) w := by
    simpa using ((hasDerivAt_id' w).mul_const (sin v)).const_add k
  exact h1.prodMk ((hK.mul_const (cos (2 * v))).prodMk (hK.mul_const (sin (2 * v))))

theorem hasDerivAt_mobC_v (k w v : ℝ) : HasDerivAt (fun v => mobC k w v) (mobCv k w v) v := by
  have hc2 : HasDerivAt (fun v : ℝ => cos (2 * v)) (-(sin (2 * v)) * 2) v := by
    have h := ((hasDerivAt_id' v).const_mul (2 : ℝ)).cos
    convert h using 1; ring
  have hs2 : HasDerivAt (fun v : ℝ => sin (2 * v)) (cos (2 * v) * 2) v := by
    have h := ((hasDerivAt_id' v).const_mul (2 : ℝ)).sin
    convert h using 1; ring
  have h1 : HasDerivAt (fun v : ℝ => -(w * cos v)) (w * sin v) v := by
    have := ((hasDerivAt_cos v).const_mul w).neg
    convert this using 1; ring
  have hK : HasDerivAt (fun v : ℝ => k + w * sin v) (w * cos v) v :=
    ((hasDerivAt_sin v).const_mul w).const_add k
  refine h1.prodMk ((hK.mul hc2).prodMk (hK.mul hs2)) |>.congr_deriv ?_
  simp only [mobCv]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem dot_mobCw_self (v : ℝ) : dot (mobCw v) (mobCw v) = 1 := by
  simp only [dot, mobCw]
  have h1 := sin_sq_add_cos_sq v
  have h2 := sin_sq_add_cos_sq (2 * v)
  linear_combination (sin v ^ 2) * h2 + h1

theorem dot_mobCv_mobCw (k w v : ℝ) : dot (mobCv k w v) (mobCw v) = 0 := by
  simp only [dot, mobCw, mobCv]
  have h2 := sin_sq_add_cos_sq (2 * v)
  linear_combination (w * cos v * sin v) * h2

theorem dot_mobCv_self (k w v : ℝ) :
    dot (mobCv k w v) (mobCv k w v) = w ^ 2 + 4 * (k + w * sin v) ^ 2 := by
  simp only [dot, mobCv]
  have h1 := sin_sq_add_cos_sq v
  have h2 := sin_sq_add_cos_sq (2 * v)
  linear_combination (w ^ 2 * cos v ^ 2 + 4 * (k + w * sin v) ^ 2) * h2 + w ^ 2 * h1

/-- ラグランジュの恒等式。 -/
theorem dot_cross_self (u v : V3) :
    dot (cross u v) (cross u v) = dot u u * dot v v - dot u v ^ 2 := by
  simp only [dot, cross]; ring

theorem cross_ne_of_perp {u v : V3} (hu : dot u u ≠ 0) (hv : dot v v ≠ 0) (h : dot u v = 0) :
    cross u v ≠ wp := by
  intro hc
  have h0 : dot (cross u v) (cross u v) = 0 := by rw [hc]; simp [dot, wp]
  rw [dot_cross_self, h] at h0
  have h1 : dot u u * dot v v = 0 := by linarith
  rcases mul_eq_zero.mp h1 with h' | h'
  · exact hu h'
  · exact hv h'

/-- **芯の模型ははめ込み**（k ≠ 0）：すべての (w, v) で ∂C/∂v × ∂C/∂w ≠ 0。 -/
theorem mobC_cross_ne {k : ℝ} (hk : k ≠ 0) (w v : ℝ) : cross (mobCv k w v) (mobCw v) ≠ wp := by
  refine cross_ne_of_perp ?_ (by rw [dot_mobCw_self]; norm_num) (dot_mobCv_mobCw k w v)
  rw [dot_mobCv_self]
  intro h0
  have hw : w = 0 := by nlinarith [sq_nonneg w, sq_nonneg (k + w * sin v)]
  subst hw
  have : k ^ 2 = 0 := by nlinarith [sq_nonneg k]
  exact hk (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)

theorem contDiff_mobC (k : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × ℝ => mobC k p.1 p.2) := by
  unfold mobC; fun_prop

/-- 芯の円 C(0, v) は半径 k の円を二周する。 -/
theorem mobC_zero (k v : ℝ) : mobC k 0 v = (0, k * cos (2 * v), k * sin (2 * v)) := by
  simp [mobC]

/-! ### 平面の座標 y = e^{iv}/w -/

/-- 助変数の写像 (w, v) ↦ y = (cos v / w, sin v / w)。 -/
def Ypp (p : ℝ × ℝ) : ℝ × ℝ := (cos p.2 / p.1, sin p.2 / p.1)

/-- y は τ で不変：(w, v) と (−w, v + π) は同じ y を与える。 -/
theorem Ypp_deck (w v : ℝ) : Ypp (-w, v + π) = Ypp (w, v) := by
  simp only [Ypp, cos_add_pi, sin_add_pi]
  refine Prod.ext ?_ ?_ <;> simp only <;> rw [neg_div_neg_eq]

theorem tau_Ypp {w : ℝ} (hw : w ≠ 0) (v : ℝ) : tau (Ypp (w, v)) = 1 / w ^ 2 := by
  simp only [tau, Ypp]
  field_simp
  linear_combination sin_sq_add_cos_sq v

/-- 芯の模型を y で書いたもの。y ≠ 0 で滑らかである。 -/
def mobCy (k : ℝ) (y : ℝ × ℝ) : V3 :=
  (-(y.1 / tau y),
   (k + y.2 / tau y) * ((y.1 ^ 2 - y.2 ^ 2) / tau y),
   (k + y.2 / tau y) * (2 * y.1 * y.2 / tau y))

theorem mobCy_Ypp (k : ℝ) {w : ℝ} (hw : w ≠ 0) (v : ℝ) : mobCy k (Ypp (w, v)) = mobC k w v := by
  have ht := tau_Ypp hw v
  have e1 : (Ypp (w, v)).1 / tau (Ypp (w, v)) = w * cos v := by
    rw [ht]; simp only [Ypp]; field_simp
  have e2 : (Ypp (w, v)).2 / tau (Ypp (w, v)) = w * sin v := by
    rw [ht]; simp only [Ypp]; field_simp
  have e3 : ((Ypp (w, v)).1 ^ 2 - (Ypp (w, v)).2 ^ 2) / tau (Ypp (w, v)) = cos (2 * v) := by
    rw [ht, cos_two_mul]; simp only [Ypp]; field_simp
    linear_combination (-1 : ℝ) * sin_sq_add_cos_sq v
  have e4 : 2 * (Ypp (w, v)).1 * (Ypp (w, v)).2 / tau (Ypp (w, v)) = sin (2 * v) := by
    rw [ht, sin_two_mul]; simp only [Ypp]; field_simp
  simp only [mobCy, mobC, e1, e2, e3, e4]

theorem contDiffAt_mobCy (k : ℝ) {y : ℝ × ℝ} (hy : tau y ≠ 0) :
    ContDiffAt ℝ ∞ (mobCy k) y := by
  have ht : ContDiffAt ℝ ∞ tau y := contDiff_tau.contDiffAt
  have h1 : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => y.1 / tau y) y :=
    contDiffAt_fst.div ht hy
  have h2 : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => y.2 / tau y) y :=
    contDiffAt_snd.div ht hy
  have h3 : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => (y.1 ^ 2 - y.2 ^ 2) / tau y) y :=
    ((contDiffAt_fst.pow 2).sub (contDiffAt_snd.pow 2)).div ht hy
  have h4 : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => 2 * y.1 * y.2 / tau y) y :=
    ((contDiffAt_const.mul contDiffAt_fst).mul contDiffAt_snd).div ht hy
  exact h1.neg.prodMk (((contDiffAt_const.add h2).mul h3).prodMk ((contDiffAt_const.add h2).mul h4))

/-- 折り返したホーン：w ≥ 0 で G、w ≤ 0 で G の鏡像。 -/
def foldG (w v : ℝ) : V3 := (|w| / D w, w ^ 3 * cos v / D w, w ^ 3 * sin v / D w)

theorem foldG_of_pos {w : ℝ} (hw : 0 ≤ w) (v : ℝ) : foldG w v = G w v := by
  simp [foldG, G, abs_of_nonneg hw]

theorem foldG_of_neg {w : ℝ} (hw : w ≤ 0) (v : ℝ) : foldG w v = mirror (G w v) := by
  simp only [foldG, G, mirror, abs_of_nonpos hw]
  refine Prod.ext ?_ rfl
  simp only; ring

theorem foldG_deck (w v : ℝ) : foldG (-w) (v + π) = foldG w v := by
  simp only [foldG, abs_neg, D_neg, cos_add_pi, sin_add_pi]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- 平面 α（§8 の γ）は、ホーンの部分で折り返したホーンに等しい。 -/
theorem planeG_Ypp {w : ℝ} (hw : w ≠ 0) (h2 : w ^ 2 ≤ 2) (v : ℝ) :
    planeG (Ypp (w, v)) = foldG w v := by
  have ht := tau_Ypp hw v
  have hw2 : 0 < w ^ 2 := by positivity
  have hτ : 1 / 2 ≤ tau (Ypp (w, v)) := by
    rw [ht, div_le_div_iff₀ (by norm_num) hw2]; linarith
  have hsq : √(tau (Ypp (w, v))) = 1 / |w| := by
    rw [ht, show (1 : ℝ) / w ^ 2 = (1 / |w|) ^ 2 by rw [div_pow, sq_abs, one_pow]]
    exact Real.sqrt_sq (by positivity)
  have hD : D w = 1 + w ^ 4 := rfl
  have habs : 0 < |w| := abs_pos.mpr hw
  have hw2' : w ^ 2 = |w| ^ 2 := (sq_abs w).symm
  have hq : qC (tau (Ypp (w, v))) = |w| / D w := by
    simp only [qC, chiC_of_ge hτ, one_mul]
    rw [hsq, ht, hD, show w ^ 4 = (w ^ 2) ^ 2 by ring, hw2']
    field_simp
    ring
  have hh : hC (tau (Ypp (w, v))) = w ^ 4 / D w := by
    simp only [hC]; rw [ht, hD]; field_simp; ring
  simp only [planeG, foldG, hq, hh]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only [Ypp] <;> field_simp

/-! ### y の座標の微分 -/

/-- ∂y/∂w -/
def dYw (w v : ℝ) : ℝ × ℝ := (-(cos v / w ^ 2), -(sin v / w ^ 2))

/-- ∂y/∂v -/
def dYv (w v : ℝ) : ℝ × ℝ := (-(sin v / w), cos v / w)

theorem hasDerivAt_Ypp_w {w : ℝ} (hw : w ≠ 0) (v : ℝ) :
    HasDerivAt (fun w => Ypp (w, v)) (dYw w v) w := by
  have hi := hasDerivAt_inv hw
  have h1 : HasDerivAt (fun w : ℝ => cos v / w) (-(cos v / w ^ 2)) w := by
    have h := hi.const_mul (cos v)
    convert h using 1
    · ext x; simp [div_eq_mul_inv]
    · field_simp
  have h2 : HasDerivAt (fun w : ℝ => sin v / w) (-(sin v / w ^ 2)) w := by
    have h := hi.const_mul (sin v)
    convert h using 1
    · ext x; simp [div_eq_mul_inv]
    · field_simp
  exact h1.prodMk h2

theorem hasDerivAt_Ypp_v (w v : ℝ) : HasDerivAt (fun v => Ypp (w, v)) (dYv w v) v := by
  have h1 : HasDerivAt (fun v : ℝ => cos v / w) (-(sin v / w)) v := by
    have h := (hasDerivAt_cos v).div_const w
    convert h using 1; ring
  exact h1.prodMk ((hasDerivAt_sin v).div_const w)

theorem contDiffAt_Ypp {p : ℝ × ℝ} (hp : p.1 ≠ 0) : ContDiffAt ℝ ∞ Ypp p := by
  unfold Ypp
  exact ((contDiff_cos.contDiffAt.comp p contDiffAt_snd).div contDiffAt_fst hp).prodMk
    ((contDiff_sin.contDiffAt.comp p contDiffAt_snd).div contDiffAt_fst hp)

/-- **ホーンでの連鎖律**：0 < w、w² < 2 なら dγ(y)(∂y/∂w) = ∂G/∂w、dγ(y)(∂y/∂v) = ∂G/∂v。 -/
theorem planeG_chain {w : ℝ} (hw : 0 < w) (h2 : w ^ 2 < 2) (v : ℝ) :
    fderiv ℝ planeG (Ypp (w, v)) (dYw w v) = Tw w v ∧
      fderiv ℝ planeG (Ypp (w, v)) (dYv w v) = Tv w v := by
  have hd : DifferentiableAt ℝ planeG (Ypp (w, v)) :=
    contDiff_planeG.differentiable (by simp) _
  constructor
  · have hc := hd.hasFDerivAt.comp_hasDerivAt w (hasDerivAt_Ypp_w hw.ne' v)
    have heq : (fun w' => planeG (Ypp (w', v))) =ᶠ[𝓝 w] fun w' => G w' v := by
      have hop : ∀ᶠ w' in 𝓝 w, 0 < w' ∧ w' ^ 2 < 2 := by
        have h1 : ∀ᶠ w' in 𝓝 w, 0 < w' := lt_mem_nhds hw
        have h2' : ∀ᶠ w' in 𝓝 w, w' ^ 2 < 2 :=
          (continuous_pow 2).continuousAt.eventually (gt_mem_nhds h2)
        exact h1.and h2'
      filter_upwards [hop] with w' hw'
      rw [planeG_Ypp hw'.1.ne' hw'.2.le, foldG_of_pos hw'.1.le]
    exact (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_G_w w v) |>.symm ▸ rfl
  · have hc := hd.hasFDerivAt.comp_hasDerivAt v (hasDerivAt_Ypp_v w v)
    have heq : (fun v' => planeG (Ypp (w, v'))) = fun v' => G w v' := by
      funext v'; rw [planeG_Ypp hw.ne' h2.le, foldG_of_pos hw.le]
    have hc' : HasDerivAt (fun v' => G w v') (fderiv ℝ planeG (Ypp (w, v)) (dYv w v)) v := by
      rw [← heq]; exact hc
    exact hc'.unique (hasDerivAt_G_v w v)

/-- **芯での連鎖律**：w ≠ 0 なら d(C∘y⁻¹)(y)(∂y/∂w) = ∂C/∂w、(∂y/∂v) = ∂C/∂v。 -/
theorem mobCy_chain (k : ℝ) {w : ℝ} (hw : w ≠ 0) (v : ℝ) :
    fderiv ℝ (mobCy k) (Ypp (w, v)) (dYw w v) = mobCw v ∧
      fderiv ℝ (mobCy k) (Ypp (w, v)) (dYv w v) = mobCv k w v := by
  have ht : tau (Ypp (w, v)) ≠ 0 := by rw [tau_Ypp hw]; positivity
  have hd : DifferentiableAt ℝ (mobCy k) (Ypp (w, v)) :=
    (contDiffAt_mobCy k ht).differentiableAt (by simp)
  constructor
  · have hc := hd.hasFDerivAt.comp_hasDerivAt w (hasDerivAt_Ypp_w hw v)
    have heq : (fun w' => mobCy k (Ypp (w', v))) =ᶠ[𝓝 w] fun w' => mobC k w' v := by
      filter_upwards [isOpen_ne.mem_nhds hw] with w' hw'
      exact mobCy_Ypp k hw' v
    exact (hc.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_mobC_w k w v)
  · have hc := hd.hasFDerivAt.comp_hasDerivAt v (hasDerivAt_Ypp_v w v)
    have heq : (fun v' => mobCy k (Ypp (w, v'))) = fun v' => mobC k w v' := by
      funext v'; exact mobCy_Ypp k hw v'
    have hc' : HasDerivAt (fun v' => mobC k w v') (fderiv ℝ (mobCy k) (Ypp (w, v)) (dYv w v)) v := by
      rw [← heq]; exact hc
    exact hc'.unique (hasDerivAt_mobC_v k w v)

/-- y ≠ 0 は y = Ypp(1/√τ, v) と書ける。 -/
theorem exists_Ypp {y : ℝ × ℝ} (hy : tau y ≠ 0) :
    ∃ v : ℝ, Ypp (1 / √(tau y), v) = y := by
  set z : ℂ := ⟨y.1, y.2⟩ with hz
  have hz0 : z ≠ 0 := by
    intro h0
    apply hy
    have h1 : y.1 = 0 := by simpa [hz] using congrArg Complex.re h0
    have h2 : y.2 = 0 := by simpa [hz] using congrArg Complex.im h0
    simp [tau, h1, h2]
  have hn : ‖z‖ = √(tau y) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [hz, tau]
    ring_nf
  have hpos : 0 < √(tau y) := by rw [← hn]; exact norm_pos_iff.mpr hz0
  refine ⟨Complex.arg z, ?_⟩
  have hc : cos (Complex.arg z) = y.1 / √(tau y) := by rw [Complex.cos_arg hz0, hn]
  have hs : sin (Complex.arg z) = y.2 / √(tau y) := by rw [Complex.sin_arg, hn]
  simp only [Ypp, hc, hs]
  refine Prod.ext ?_ ?_ <;> simp only <;> field_simp

theorem one_div_sqrt_pos {y : ℝ × ℝ} (hy : tau y ≠ 0) : 0 < 1 / √(tau y) := by
  have := tau_nonneg y
  have : 0 < tau y := lt_of_le_of_ne this (Ne.symm hy)
  positivity

/-! ### 回転 -/

/-- e₁ 軸のまわりの回転（cos = c、sin = s）。 -/
def rotX (c s : ℝ) (u : V3) : V3 := (u.1, c * u.2.1 - s * u.2.2, s * u.2.1 + c * u.2.2)

/-- e₃ 軸のまわりの回転。 -/
def rotZ (c s : ℝ) (u : V3) : V3 := (c * u.1 - s * u.2.1, s * u.1 + c * u.2.1, u.2.2)

/-- 軸 (a₁, 0, a₃) のまわりの回転（ロドリゲスの式）。 -/
def rotA (a₁ a₃ c s : ℝ) (u : V3) : V3 :=
  (c * u.1 - s * a₃ * u.2.1 + (1 - c) * (a₁ * u.1 + a₃ * u.2.2) * a₁,
   c * u.2.1 + s * (a₃ * u.1 - a₁ * u.2.2),
   c * u.2.2 + s * a₁ * u.2.1 + (1 - c) * (a₁ * u.1 + a₃ * u.2.2) * a₃)

theorem rotA_one_zero (c s : ℝ) (u : V3) : rotA 1 0 c s u = rotX c s u := by
  simp only [rotA, rotX]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem rotA_zero_one (c s : ℝ) (u : V3) : rotA 0 1 c s u = rotZ c s u := by
  simp only [rotA, rotZ]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem dot_rotX (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (u : V3) :
    dot (rotX c s u) (rotX c s u) = dot u u := by
  simp only [dot, rotX]
  linear_combination (u.2.1 ^ 2 + u.2.2 ^ 2) * h

theorem dot_rotA (a₁ a₃ c s : ℝ) (ha : a₁ ^ 2 + a₃ ^ 2 = 1) (h : c ^ 2 + s ^ 2 = 1) (u : V3) :
    dot (rotA a₁ a₃ c s u) (rotA a₁ a₃ c s u) = dot u u := by
  simp only [dot, rotA]
  linear_combination (a₁^4*u.1^2 + 2*a₁^3*a₃*u.1*u.2.2 + a₁^2*a₃^2*u.1^2 + a₁^2*a₃^2*u.2.2^2 - 2*a₁^2*u.1^2 + 2*a₁*a₃^3*u.1*u.2.2 - 4*a₁*a₃*u.1*u.2.2 + a₃^4*u.2.2^2 - 2*a₃^2*u.2.2^2 + u.1^2 + u.2.1^2 + u.2.2^2) * h + (-2*a₁^2*c*u.1^2 - a₁^2*s^2*u.1^2 + 2*a₁^2*u.1^2 - 4*a₁*a₃*c*u.1*u.2.2 - 2*a₁*a₃*s^2*u.1*u.2.2 + 4*a₁*a₃*u.1*u.2.2 - 2*a₃^2*c*u.2.2^2 - a₃^2*s^2*u.2.2^2 + 2*a₃^2*u.2.2^2 + s^2*u.1^2 + s^2*u.2.1^2 + s^2*u.2.2^2) * ha

theorem rotX_eq_zero {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) {u : V3} (hu : rotX c s u = 0) : u = 0 := by
  have h0 := dot_rotX c s h u
  rw [hu] at h0
  have : dot u u = 0 := by rw [← h0]; simp [dot]
  by_contra hne
  exact dot_self_ne (u := u) (fun h' => hne (by rw [h']; rfl)) this

theorem rotA_eq_zero {a₁ a₃ c s : ℝ} (ha : a₁ ^ 2 + a₃ ^ 2 = 1) (h : c ^ 2 + s ^ 2 = 1) {u : V3}
    (hu : rotA a₁ a₃ c s u = 0) : u = 0 := by
  have h0 := dot_rotA a₁ a₃ c s ha h u
  rw [hu] at h0
  have : dot u u = 0 := by rw [← h0]; simp [dot]
  by_contra hne
  exact dot_self_ne (u := u) (fun h' => hne (by rw [h']; rfl)) this

theorem rotZ_eq_zero {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) {u : V3} (hu : rotZ c s u = 0) : u = 0 := by
  rw [← rotA_zero_one] at hu
  exact rotA_eq_zero (by norm_num) h hu

/-! ### 形式解の枠（(w, v) の座標） -/

/-- 段の関数：t ≤ T で 0、t ≥ T + Δ で 1。 -/
def stg (T Δ t : ℝ) : ℝ := s₀ ((t - T) / Δ)

theorem stg_nonneg (T Δ t : ℝ) : 0 ≤ stg T Δ t := Real.smoothTransition.nonneg _
theorem stg_le_one (T Δ t : ℝ) : stg T Δ t ≤ 1 := Real.smoothTransition.le_one _

theorem stg_zero {T Δ t : ℝ} (hΔ : 0 < Δ) (ht : t ≤ T) : stg T Δ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hΔ.le)

theorem stg_one {T Δ t : ℝ} (hΔ : 0 < Δ) (ht : T + Δ ≤ t) : stg T Δ t = 1 :=
  Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hΔ]; linarith)

theorem lt_of_stg_ne {T Δ t : ℝ} (hΔ : 0 < Δ) (h : stg T Δ t ≠ 0) : T < t := by
  by_contra hc; exact h (stg_zero hΔ (not_lt.mp hc))

theorem contDiff_stg (T Δ : ℝ) : ContDiff ℝ ∞ (stg T Δ) := by
  unfold stg
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

/-- 中間の領域の端：T₀ = 1/w₀²（ホーンの側）、幅 Δ = (1/δ² − 1/w₀²)/5。 -/
def mT0 (w₀ : ℝ) : ℝ := 1 / w₀ ^ 2
def mDl (δ w₀ : ℝ) : ℝ := (1 / δ ^ 2 - 1 / w₀ ^ 2) / 5

/-- 三つの段：基底の向きの回転 σα、回転軸の移動 σβ、形の補間 σγ。 -/
def sgA (δ w₀ t : ℝ) : ℝ := stg (mT0 w₀ + mDl δ w₀) (mDl δ w₀) t
def sgB (δ w₀ t : ℝ) : ℝ := stg (mT0 w₀ + 2 * mDl δ w₀) (mDl δ w₀) t
def sgC (δ w₀ t : ℝ) : ℝ := stg (mT0 w₀ + 3 * mDl δ w₀) (mDl δ w₀) t

/-- ホーンの側の形：ξ_w ∂G/∂w(w, 0) + ξ_v ∂G/∂v(w, 0)。 -/
def A0 (w : ℝ) (ξ : ℝ × ℝ) : V3 :=
  (ξ.1 * ((1 - 3 * w ^ 4) / D w ^ 2), ξ.1 * (w ^ 2 * (3 - w ^ 4) / D w ^ 2), ξ.2 * (w ^ 3 / D w))

/-- 芯の側の形。 -/
def Bm (k w s : ℝ) (ξ : ℝ × ℝ) : V3 := (-ξ.1, ξ.2 * w, ξ.2 * (2 * k + 2 * w * s))

/-- **形式解の枠**。c = cos v、s = sin v、t = 1/w²。 -/
def fr (k δ w₀ w c s t : ℝ) (ξ : ℝ × ℝ) : V3 :=
  rotX (c ^ 2 - s ^ 2) (2 * c * s)
    (rotA (cos (π * sgB δ w₀ t / 2)) (sin (π * sgB δ w₀ t / 2)) c (-s)
      ((1 - sgC δ w₀ t) • rotZ (cos (π * sgA δ w₀ t)) (sin (π * sgA δ w₀ t)) (A0 w ξ)
        + sgC δ w₀ t • Bm k w s ξ))

theorem fr_linear (k δ w₀ w c s t : ℝ) (ξ : ℝ × ℝ) :
    fr k δ w₀ w c s t ξ = ξ.1 • fr k δ w₀ w c s t (1, 0) + ξ.2 • fr k δ w₀ w c s t (0, 1) := by
  simp only [fr, rotX, rotA, rotZ, A0, Bm, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- 段の順序：σγ ≠ 0 なら σα = σβ = 1。 -/
theorem sg_order {δ w₀ t : ℝ} (hΔ : 0 < mDl δ w₀) (h : sgC δ w₀ t ≠ 0) :
    sgA δ w₀ t = 1 ∧ sgB δ w₀ t = 1 := by
  have ht := lt_of_stg_ne hΔ h
  exact ⟨stg_one hΔ (by linarith), stg_one hΔ (by linarith)⟩

theorem sg_zero {δ w₀ t : ℝ} (hΔ : 0 < mDl δ w₀) (ht : t ≤ mT0 w₀ + mDl δ w₀) :
    sgA δ w₀ t = 0 ∧ sgB δ w₀ t = 0 ∧ sgC δ w₀ t = 0 :=
  ⟨stg_zero hΔ ht, stg_zero hΔ (by linarith), stg_zero hΔ (by linarith)⟩

theorem sg_one {δ w₀ t : ℝ} (hΔ : 0 < mDl δ w₀) (ht : mT0 w₀ + 4 * mDl δ w₀ ≤ t) :
    sgA δ w₀ t = 1 ∧ sgB δ w₀ t = 1 ∧ sgC δ w₀ t = 1 :=
  ⟨stg_one hΔ (by linarith), stg_one hΔ (by linarith), stg_one hΔ (by linarith)⟩

theorem rotX_double {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (u : V3) :
    rotX (c ^ 2 - s ^ 2) (2 * c * s) (rotX c (-s) u) = rotX c s u := by
  simp only [rotX]
  refine Prod.ext rfl (Prod.ext ?_ ?_) <;> simp only
  · linear_combination (c * u.2.1 - s * u.2.2) * h
  · linear_combination (s * u.2.1 + c * u.2.2) * h

/-- ホーンの側（すべての段が 0）では、枠は ∂G の組である。 -/
theorem fr_horn {k δ w₀ t : ℝ} (hΔ : 0 < mDl δ w₀) (ht : t ≤ mT0 w₀ + mDl δ w₀) (w v : ℝ)
    (ξ : ℝ × ℝ) : fr k δ w₀ w (cos v) (sin v) t ξ = ξ.1 • Tw w v + ξ.2 • Tv w v := by
  obtain ⟨hA, hB, hC'⟩ := sg_zero (t := t) hΔ ht
  have hcs : cos v ^ 2 + sin v ^ 2 = 1 := by rw [add_comm]; exact sin_sq_add_cos_sq v
  simp only [fr, hA, hB, hC', mul_zero, zero_div, cos_zero, sin_zero, sub_zero, one_smul,
    zero_smul, add_zero, rotA_one_zero, rotX_double hcs]
  simp only [rotX, rotZ, A0, Tw, Tv, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- 芯の側（すべての段が 1）では、枠は ∂C の組である。 -/
theorem fr_core {k δ w₀ t : ℝ} (hΔ : 0 < mDl δ w₀) (ht : mT0 w₀ + 4 * mDl δ w₀ ≤ t) (w v : ℝ)
    (ξ : ℝ × ℝ) : fr k δ w₀ w (cos v) (sin v) t ξ = ξ.1 • mobCw v + ξ.2 • mobCv k w v := by
  obtain ⟨hA, hB, hC'⟩ := sg_one (t := t) hΔ ht
  have hcs : sin v ^ 2 + cos v ^ 2 = 1 := sin_sq_add_cos_sq v
  have h2c : cos (2 * v) = cos v ^ 2 - sin v ^ 2 := by rw [cos_two_mul]; linear_combination hcs
  have h2s : sin (2 * v) = 2 * cos v * sin v := by rw [sin_two_mul]; ring
  have hpi : π * 1 / 2 = π / 2 := by ring
  simp only [fr, hA, hB, hC', hpi, cos_pi_div_two, sin_pi_div_two, sub_self, zero_smul, one_smul,
    zero_add, rotA_zero_one]
  simp only [rotX, rotZ, Bm, mobCw, mobCv, h2c, h2s, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

/-- A0 は単射（w ≠ 0）。 -/
theorem A0_eq_zero {w : ℝ} (hw : w ≠ 0) {ξ : ℝ × ℝ} (h : A0 w ξ = 0) : ξ = 0 := by
  have hD := D_pos w
  have h1 : ξ.1 * ((1 - 3 * w ^ 4) / D w ^ 2) = 0 := congrArg Prod.fst h
  have h2 : ξ.1 * (w ^ 2 * (3 - w ^ 4) / D w ^ 2) = 0 := congrArg (fun z : V3 => z.2.1) h
  have h3 : ξ.2 * (w ^ 3 / D w) = 0 := congrArg (fun z : V3 => z.2.2) h
  have hb : w ^ 3 / D w ≠ 0 := div_ne_zero (pow_ne_zero 3 hw) hD.ne'
  have e2 : ξ.2 = 0 := (mul_eq_zero.mp h3).resolve_right hb
  have e1 : ξ.1 = 0 := by
    by_contra hne
    have ha : (1 - 3 * w ^ 4) / D w ^ 2 = 0 := (mul_eq_zero.mp h1).resolve_left hne
    have hb' : w ^ 2 * (3 - w ^ 4) / D w ^ 2 = 0 := (mul_eq_zero.mp h2).resolve_left hne
    have hD2 : D w ^ 2 ≠ 0 := by positivity
    rw [div_eq_zero_iff] at ha hb'
    rcases ha with ha | ha
    · rcases hb' with hb' | hb'
      · have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
        have h3' : 3 - w ^ 4 = 0 := (mul_eq_zero.mp hb').resolve_left hw2
        nlinarith
      · exact hD2 hb'
    · exact hD2 ha
  exact Prod.ext e1 e2

theorem quad_pos {α β γ X Y : ℝ} (hα : 0 < α) (hd : 0 < 4 * α * γ - β ^ 2)
    (hXY : ¬(X = 0 ∧ Y = 0)) : 0 < α * X ^ 2 - β * X * Y + γ * Y ^ 2 := by
  have key : 4 * α * (α * X ^ 2 - β * X * Y + γ * Y ^ 2) =
      (2 * α * X - β * Y) ^ 2 + (4 * α * γ - β ^ 2) * Y ^ 2 := by ring
  by_cases hY : Y = 0
  · have hX : X ≠ 0 := fun hX => hXY ⟨hX, hY⟩
    subst hY
    have : 0 < X ^ 2 := by positivity
    nlinarith
  · have hY2 : 0 < Y ^ 2 := by positivity
    have h4 : 0 < 4 * α * (α * X ^ 2 - β * X * Y + γ * Y ^ 2) := by
      rw [key]; nlinarith [sq_nonneg (2 * α * X - β * Y), mul_pos hd hY2]
    have h4a : 0 < 4 * α := by linarith
    exact pos_of_mul_pos_right h4 h4a.le

theorem shape_disc {k w s : ℝ} (hk : 0 < k) (hk1 : k ≤ 1 / 2) (hw : 0 < w) (hwk : w ≤ k / 2)
    (hs2 : -1 ≤ s) :
    0 < 4 * (1 - 3 * w ^ 4) * (w ^ 3 * D w * (2 * k + 2 * w * s)) - (w ^ 3 * (3 - w ^ 4)) ^ 2 := by
  have hw14 : w ≤ 1 / 4 := by linarith
  have hw4 : w ^ 4 ≤ 1 / 256 := by
    have h4 : w ^ 4 ≤ (1 / 4) ^ 4 := pow_le_pow_left₀ hw.le hw14 4
    norm_num at h4 ⊢; linarith
  have hw3p : 0 < w ^ 3 := by positivity
  have hα : 1 / 2 ≤ 1 - 3 * w ^ 4 := by linarith
  have hDge : 1 ≤ D w := by unfold D; nlinarith [pow_nonneg hw.le 4]
  have hκ : k ≤ 2 * k + 2 * w * s := by nlinarith
  have hγ : w ^ 3 * k ≤ w ^ 3 * D w * (2 * k + 2 * w * s) := by
    have h1 : w ^ 3 * k ≤ w ^ 3 * (2 * k + 2 * w * s) := mul_le_mul_of_nonneg_left hκ hw3p.le
    have h2 : w ^ 3 * (2 * k + 2 * w * s) ≤ w ^ 3 * D w * (2 * k + 2 * w * s) := by
      have hκ0 : 0 ≤ 2 * k + 2 * w * s := by linarith
      have := mul_le_mul_of_nonneg_left hDge (mul_nonneg hw3p.le hκ0)
      nlinarith
    linarith
  have hβ0 : 0 ≤ w ^ 3 * (3 - w ^ 4) := mul_nonneg hw3p.le (by linarith)
  have hβ1 : w ^ 3 * (3 - w ^ 4) ≤ 3 * w ^ 3 := by nlinarith [pow_nonneg hw.le 4]
  have hβsq : (w ^ 3 * (3 - w ^ 4)) ^ 2 ≤ 9 * (w ^ 3 * w ^ 3) := by nlinarith
  have hw3 : w ^ 3 ≤ k / 32 := by
    have : w ^ 3 ≤ (k / 2) ^ 3 := pow_le_pow_left₀ hw.le hwk 3
    have hk2 : k ^ 2 ≤ 1 / 4 := by nlinarith
    nlinarith
  have h4αγ : 2 * (w ^ 3 * k) ≤ 4 * (1 - 3 * w ^ 4) * (w ^ 3 * D w * (2 * k + 2 * w * s)) := by
    have hγ0 : 0 ≤ w ^ 3 * k := by positivity
    nlinarith
  have hww : w ^ 3 * w ^ 3 ≤ w ^ 3 * (k / 32) := mul_le_mul_of_nonneg_left hw3 hw3p.le
  have : 0 < w ^ 3 * k := by positivity
  nlinarith

theorem dot_shape (k w s X Y : ℝ) :
    dot ((-(X * ((1 - 3 * w ^ 4) / D w ^ 2)), -(X * (w ^ 2 * (3 - w ^ 4) / D w ^ 2)),
          Y * (w ^ 3 / D w)) : V3) ((-X, Y * w, Y * (2 * k + 2 * w * s)) : V3) * D w ^ 4 =
      D w ^ 2 * ((1 - 3 * w ^ 4) * X ^ 2 - w ^ 3 * (3 - w ^ 4) * X * Y +
        w ^ 3 * D w * (2 * k + 2 * w * s) * Y ^ 2) := by
  have hD := (D_pos w).ne'
  simp only [dot]
  field_simp
  ring

/-- **形の補間の単射性**（0 < w ≤ k/2 ≤ 1/4）。 -/
theorem shape_inj {k w σ s : ℝ} (hk : 0 < k) (hk1 : k ≤ 1 / 2) (hw : 0 < w) (hwk : w ≤ k / 2)
    (hs2 : -1 ≤ s) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {ξ : ℝ × ℝ}
    (h : (1 - σ) • rotZ (-1) 0 (A0 w ξ) + σ • Bm k w s ξ = 0) : ξ = 0 := by
  obtain ⟨X, Y⟩ := ξ
  have hu : rotZ (-1) 0 (A0 w (X, Y)) = ((-(X * ((1 - 3 * w ^ 4) / D w ^ 2)),
      -(X * (w ^ 2 * (3 - w ^ 4) / D w ^ 2)), Y * (w ^ 3 / D w)) : V3) := by
    simp only [rotZ, A0]; refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring
  have hz : Bm k w s (X, Y) = ((-X, Y * w, Y * (2 * k + 2 * w * s)) : V3) := rfl
  rw [hu, hz] at h
  set u : V3 := ((-(X * ((1 - 3 * w ^ 4) / D w ^ 2)), -(X * (w ^ 2 * (3 - w ^ 4) / D w ^ 2)),
      Y * (w ^ 3 / D w)) : V3) with hu'
  set z : V3 := ((-X, Y * w, Y * (2 * k + 2 * w * s)) : V3) with hz'
  have hdot : dot ((1 - σ) • u + σ • z) (u + z) = (1 - σ) * dot u u + σ * dot z z + dot u z := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    ring
  have h0 : dot ((1 - σ) • u + σ • z) (u + z) = 0 := by rw [h]; simp [dot]
  have huu : 0 ≤ dot u u := by
    simp only [dot]
    exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)
  have hzz : 0 ≤ dot z z := by
    simp only [dot]
    exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)
  by_contra hξ
  have hXY : ¬(X = 0 ∧ Y = 0) := fun h' => hξ (by rw [h'.1, h'.2]; rfl)
  have hα : 0 < 1 - 3 * w ^ 4 := by
    have : w ^ 4 ≤ (1 / 4) ^ 4 := pow_le_pow_left₀ hw.le (by linarith) 4
    norm_num at this; linarith
  have hQ := quad_pos hα (shape_disc hk hk1 hw hwk hs2) hXY
  have hsc := dot_shape k w s X Y
  have hD2 : 0 < D w ^ 2 := by have := D_pos w; positivity
  have hD4 : 0 < D w ^ 4 := by have := D_pos w; positivity
  have hpos : 0 < dot u z := by
    have h1 : 0 < dot u z * D w ^ 4 := by rw [hsc]; exact mul_pos hD2 hQ
    exact pos_of_mul_pos_left h1 hD4.le
  rw [hdot] at h0
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - σ) huu, mul_nonneg hσ0 hzz]

/-- **枠の単射性**。w > 0、t = 1/w² で、t > T₀ なら w ≤ k/2 とする。 -/
theorem fr_inj {k δ w₀ w c s t : ℝ} (hk : 0 < k) (hk1 : k ≤ 1 / 2) (hΔ : 0 < mDl δ w₀)
    (hw : 0 < w) (hcs : c ^ 2 + s ^ 2 = 1) (hwk : mT0 w₀ < t → w ≤ k / 2)
    {ξ : ℝ × ℝ} (h : fr k δ w₀ w c s t ξ = 0) : ξ = 0 := by
  have hcs' : c ^ 2 + (-s) ^ 2 = 1 := by linear_combination hcs
  have h2 : (c ^ 2 - s ^ 2) ^ 2 + (2 * c * s) ^ 2 = 1 := by linear_combination (c ^ 2 + s ^ 2 + 1) * hcs
  have ha : cos (π * sgB δ w₀ t / 2) ^ 2 + sin (π * sgB δ w₀ t / 2) ^ 2 = 1 := by
    rw [add_comm]; exact sin_sq_add_cos_sq _
  have hz : cos (π * sgA δ w₀ t) ^ 2 + sin (π * sgA δ w₀ t) ^ 2 = 1 := by
    rw [add_comm]; exact sin_sq_add_cos_sq _
  have h' := rotA_eq_zero ha hcs' (rotX_eq_zero h2 h)
  by_cases hC : sgC δ w₀ t = 0
  · rw [hC, sub_zero, one_smul, zero_smul, add_zero] at h'
    exact A0_eq_zero hw.ne' (rotZ_eq_zero hz h')
  · obtain ⟨hA, -⟩ := sg_order hΔ hC
    have htT : mT0 w₀ < t := by
      have := lt_of_stg_ne hΔ hC; linarith
    rw [hA, mul_one, cos_pi, sin_pi] at h'
    have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c]
    have hs2 : -1 ≤ s := by nlinarith [sq_nonneg c]
    exact shape_inj hk hk1 hw (hwk htT) hs2 (stg_nonneg _ _ _) (stg_le_one _ _ _) h'

/-! ### 形式解（平面 y の座標） -/

theorem contDiff_coefs :
    ContDiff ℝ ∞ (fun w : ℝ => (1 - 3 * w ^ 4) / D w ^ 2) ∧
    ContDiff ℝ ∞ (fun w : ℝ => w ^ 2 * (3 - w ^ 4) / D w ^ 2) ∧
    ContDiff ℝ ∞ (fun w : ℝ => w ^ 3 / D w) := by
  have hD : ContDiff ℝ ∞ D := by unfold D; fun_prop
  refine ⟨?_, ?_, ?_⟩
  · exact ContDiff.div (by fun_prop) (hD.pow 2) (fun w => pow_ne_zero 2 (D_ne w))
  · exact ContDiff.div (by fun_prop) (hD.pow 2) (fun w => pow_ne_zero 2 (D_ne w))
  · exact ContDiff.div (by fun_prop) hD (fun w => D_ne w)

theorem contDiff_rotX : ContDiff ℝ ∞ (fun q : ℝ × ℝ × V3 => rotX q.1 q.2.1 q.2.2) := by
  unfold rotX; fun_prop

theorem contDiff_rotZ : ContDiff ℝ ∞ (fun q : ℝ × ℝ × V3 => rotZ q.1 q.2.1 q.2.2) := by
  unfold rotZ; fun_prop

theorem contDiff_rotA :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ × ℝ × V3 => rotA q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) := by
  unfold rotA; fun_prop

theorem contDiff_sg (δ w₀ : ℝ) :
    ContDiff ℝ ∞ (sgA δ w₀) ∧ ContDiff ℝ ∞ (sgB δ w₀) ∧ ContDiff ℝ ∞ (sgC δ w₀) :=
  ⟨contDiff_stg _ _, contDiff_stg _ _, contDiff_stg _ _⟩

theorem contDiff_fr (k δ w₀ : ℝ) (ξ : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ × ℝ => fr k δ w₀ q.1 q.2.1 q.2.2.1 q.2.2.2 ξ) := by
  obtain ⟨h1, h2, h3⟩ := contDiff_coefs
  obtain ⟨hA, hB, hC⟩ := contDiff_sg δ w₀
  have hA0 : ContDiff ℝ ∞ (fun w : ℝ => A0 w ξ) := by
    have e : (fun w : ℝ => A0 w ξ) = fun w => (ξ.1 * ((1 - 3 * w ^ 4) / D w ^ 2),
        ξ.1 * (w ^ 2 * (3 - w ^ 4) / D w ^ 2), ξ.2 * (w ^ 3 / D w)) := rfl
    rw [e]
    exact (contDiff_const.mul h1).prodMk ((contDiff_const.mul h2).prodMk (contDiff_const.mul h3))
  have hBm : ContDiff ℝ ∞ (fun q : ℝ × ℝ => Bm k q.1 q.2 ξ) := by unfold Bm; fun_prop
  have hw : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ × ℝ => q.1) := contDiff_fst
  have hc : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ × ℝ => q.2.1) := contDiff_snd.fst
  have hs : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.1) := contDiff_snd.snd.fst
  have ht : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ × ℝ => q.2.2.2) := contDiff_snd.snd.snd
  have hsA := hA.comp ht
  have hsB := hB.comp ht
  have hsC := hC.comp ht
  have hZ : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ × ℝ =>
      rotZ (cos (π * sgA δ w₀ q.2.2.2)) (sin (π * sgA δ w₀ q.2.2.2)) (A0 q.1 ξ)) :=
    contDiff_rotZ.comp ((contDiff_cos.comp (contDiff_const.mul hsA)).prodMk
      ((contDiff_sin.comp (contDiff_const.mul hsA)).prodMk (hA0.comp hw)))
  have hin : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ × ℝ =>
      (1 - sgC δ w₀ q.2.2.2) • rotZ (cos (π * sgA δ w₀ q.2.2.2)) (sin (π * sgA δ w₀ q.2.2.2))
        (A0 q.1 ξ) + sgC δ w₀ q.2.2.2 • Bm k q.1 q.2.2.1 ξ) :=
    ((contDiff_const.sub hsC).smul hZ).add (hsC.smul (hBm.comp (hw.prodMk hs)))
  have hRA : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ × ℝ =>
      rotA (cos (π * sgB δ w₀ q.2.2.2 / 2)) (sin (π * sgB δ w₀ q.2.2.2 / 2)) q.2.1 (-q.2.2.1)
        ((1 - sgC δ w₀ q.2.2.2) • rotZ (cos (π * sgA δ w₀ q.2.2.2)) (sin (π * sgA δ w₀ q.2.2.2))
          (A0 q.1 ξ) + sgC δ w₀ q.2.2.2 • Bm k q.1 q.2.2.1 ξ)) :=
    contDiff_rotA.comp ((contDiff_cos.comp ((contDiff_const.mul hsB).div_const 2)).prodMk
      ((contDiff_sin.comp ((contDiff_const.mul hsB).div_const 2)).prodMk
        (hc.prodMk (hs.neg.prodMk hin))))
  exact contDiff_rotX.comp (((hc.pow 2).sub (hs.pow 2)).prodMk
    (((contDiff_const.mul hc).mul hs).prodMk hRA))

/-- w(y) = 1/|y|。 -/
def wY (y : ℝ × ℝ) : ℝ := 1 / √(tau y)

theorem wY_Ypp {w : ℝ} (hw : 0 < w) (v : ℝ) : wY (Ypp (w, v)) = w := by
  rw [wY, tau_Ypp hw.ne', show (1 : ℝ) / w ^ 2 = (1 / w) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]
  field_simp

theorem cY_Ypp {w : ℝ} (hw : 0 < w) (v : ℝ) : (Ypp (w, v)).1 * wY (Ypp (w, v)) = cos v := by
  rw [wY_Ypp hw]; simp only [Ypp]; field_simp

theorem sY_Ypp {w : ℝ} (hw : 0 < w) (v : ℝ) : (Ypp (w, v)).2 * wY (Ypp (w, v)) = sin v := by
  rw [wY_Ypp hw]; simp only [Ypp]; field_simp

theorem contDiffAt_wY {y : ℝ × ℝ} (hy : tau y ≠ 0) : ContDiffAt ℝ ∞ wY y := by
  have hpos : 0 < tau y := lt_of_le_of_ne (tau_nonneg y) (Ne.symm hy)
  have hs : ContDiffAt ℝ ∞ (fun y => √(tau y)) y :=
    (contDiff_tau.contDiffAt).sqrt hy
  exact contDiffAt_const.div hs (Real.sqrt_pos.mpr hpos).ne'

/-- 枠を y で書いたもの。 -/
def frY (k δ w₀ : ℝ) (y ξ : ℝ × ℝ) : V3 :=
  fr k δ w₀ (wY y) (y.1 * wY y) (y.2 * wY y) (tau y) ξ

theorem frY_Ypp (k δ w₀ : ℝ) {w : ℝ} (hw : 0 < w) (v : ℝ) (ξ : ℝ × ℝ) :
    frY k δ w₀ (Ypp (w, v)) ξ = fr k δ w₀ w (cos v) (sin v) (1 / w ^ 2) ξ := by
  rw [frY, wY_Ypp hw, ← cY_Ypp hw v, ← sY_Ypp hw v, tau_Ypp hw.ne', wY_Ypp hw]

theorem contDiffAt_frY (k δ w₀ : ℝ) (ξ : ℝ × ℝ) {y : ℝ × ℝ} (hy : tau y ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => frY k δ w₀ y ξ) y := by
  have hw := contDiffAt_wY hy
  have hq : ContDiffAt ℝ ∞ (fun y : ℝ × ℝ => (wY y, y.1 * wY y, y.2 * wY y, tau y)) y :=
    hw.prodMk ((contDiffAt_fst.mul hw).prodMk ((contDiffAt_snd.mul hw).prodMk
      contDiff_tau.contDiffAt))
  have e : (fun y => frY k δ w₀ y ξ) =
      (fun q : ℝ × ℝ × ℝ × ℝ => fr k δ w₀ q.1 q.2.1 q.2.2.1 q.2.2.2 ξ) ∘
        (fun y : ℝ × ℝ => (wY y, y.1 * wY y, y.2 * wY y, tau y)) := by
    funext y; simp only [Function.comp, frY]
  rw [e]
  exact (contDiff_fr k δ w₀ ξ).contDiffAt.comp y hq

/-- 第 1 列と第 2 列（dy の逆の行列を掛けたもの）。 -/
def col1 (k δ w₀ : ℝ) (y : ℝ × ℝ) : V3 :=
  (-(wY y ^ 3 * y.1)) • frY k δ w₀ y (1, 0) + (-(wY y ^ 2 * y.2)) • frY k δ w₀ y (0, 1)

def col2 (k δ w₀ : ℝ) (y : ℝ × ℝ) : V3 :=
  (-(wY y ^ 3 * y.2)) • frY k δ w₀ y (1, 0) + (wY y ^ 2 * y.1) • frY k δ w₀ y (0, 1)

/-- 形式微分の y での表示。 -/
def LY (k δ w₀ : ℝ) (y : ℝ × ℝ) : ℝ × ℝ →L[ℝ] V3 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (col1 k δ w₀ y) +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (col2 k δ w₀ y)

theorem LY_apply (k δ w₀ : ℝ) (y ξ : ℝ × ℝ) :
    LY k δ w₀ y ξ = ξ.1 • col1 k δ w₀ y + ξ.2 • col2 k δ w₀ y := by
  simp [LY]

theorem contDiffAt_LY (k δ w₀ : ℝ) {y : ℝ × ℝ} (hy : tau y ≠ 0) :
    ContDiffAt ℝ ∞ (LY k δ w₀) y := by
  have hw := contDiffAt_wY hy
  have hf1 := contDiffAt_frY k δ w₀ (1, 0) hy
  have hf2 := contDiffAt_frY k δ w₀ (0, 1) hy
  have hc1 : ContDiffAt ℝ ∞ (col1 k δ w₀) y := by
    unfold col1
    exact (((hw.pow 3).mul contDiffAt_fst).neg.smul hf1).add
      (((hw.pow 2).mul contDiffAt_snd).neg.smul hf2)
  have hc2 : ContDiffAt ℝ ∞ (col2 k δ w₀) y := by
    unfold col2
    exact (((hw.pow 3).mul contDiffAt_snd).neg.smul hf1).add
      (((hw.pow 2).mul contDiffAt_fst).smul hf2)
  unfold LY
  exact (contDiffAt_const.smulRight hc1).add (contDiffAt_const.smulRight hc2)

/-- dy の基底での値。 -/
theorem LY_dYw (k δ w₀ : ℝ) {w : ℝ} (hw : 0 < w) (v : ℝ) :
    LY k δ w₀ (Ypp (w, v)) (dYw w v) = frY k δ w₀ (Ypp (w, v)) (1, 0) := by
  rw [LY_apply]
  simp only [col1, col2]
  rw [wY_Ypp hw]
  simp only [Ypp, dYw, smul_add, smul_smul]
  have hcs := sin_sq_add_cos_sq v
  have e1 : -(cos v / w ^ 2) * -(w ^ 3 * (cos v / w)) + -(sin v / w ^ 2) * -(w ^ 3 * (sin v / w))
      = 1 := by field_simp; linear_combination hcs
  have e2 : -(cos v / w ^ 2) * -(w ^ 2 * (sin v / w)) + -(sin v / w ^ 2) * (w ^ 2 * (cos v / w))
      = 0 := by field_simp; ring
  rw [show ∀ a b c d : ℝ, ∀ F₁ F₂ : V3, a • F₁ + b • F₂ + (c • F₁ + d • F₂) =
      (a + c) • F₁ + (b + d) • F₂ from fun a b c d F₁ F₂ => by
        simp only [add_smul]; abel, e1, e2, one_smul, zero_smul, add_zero]

theorem LY_dYv (k δ w₀ : ℝ) {w : ℝ} (hw : 0 < w) (v : ℝ) :
    LY k δ w₀ (Ypp (w, v)) (dYv w v) = frY k δ w₀ (Ypp (w, v)) (0, 1) := by
  rw [LY_apply]
  simp only [col1, col2]
  rw [wY_Ypp hw]
  simp only [Ypp, dYv, smul_add, smul_smul]
  have hcs := sin_sq_add_cos_sq v
  have e1 : -(sin v / w) * -(w ^ 3 * (cos v / w)) + cos v / w * -(w ^ 3 * (sin v / w)) = 0 := by
    field_simp; ring
  have e2 : -(sin v / w) * -(w ^ 2 * (sin v / w)) + cos v / w * (w ^ 2 * (cos v / w)) = 1 := by
    field_simp; linear_combination hcs
  rw [show ∀ a b c d : ℝ, ∀ F₁ F₂ : V3, a • F₁ + b • F₂ + (c • F₁ + d • F₂) =
      (a + c) • F₁ + (b + d) • F₂ from fun a b c d F₁ F₂ => by
        simp only [add_smul]; abel, e1, e2, one_smul, zero_smul, zero_add]

/-- 基底の分解：ξ = a ∂y/∂w + b ∂y/∂v。 -/
theorem decomp_dY {w : ℝ} (hw : w ≠ 0) (v : ℝ) (ξ : ℝ × ℝ) :
    ξ = (-(w * (cos v * ξ.1 + sin v * ξ.2) * w)) • dYw w v
      + (w * (-(sin v * ξ.1) + cos v * ξ.2)) • dYv w v := by
  have hcs := sin_sq_add_cos_sq v
  simp only [dYw, dYv, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine Prod.ext ?_ ?_ <;> simp only <;> field_simp
  · linear_combination (-ξ.1) * hcs
  · linear_combination (-ξ.2) * hcs

/-- 二つの線形写像が ∂y/∂w、∂y/∂v で一致すれば等しい。 -/
theorem clm_ext_dY {w : ℝ} (hw : w ≠ 0) (v : ℝ) {L₁ L₂ : ℝ × ℝ →L[ℝ] V3}
    (h1 : L₁ (dYw w v) = L₂ (dYw w v)) (h2 : L₁ (dYv w v) = L₂ (dYv w v)) : L₁ = L₂ := by
  refine ContinuousLinearMap.ext fun ξ => ?_
  rw [decomp_dY hw v ξ, map_add, map_smul, map_smul, map_add, map_smul, map_smul, h1, h2]

/-- dy は単射。 -/
theorem dY_indep {w : ℝ} (hw : w ≠ 0) (v : ℝ) {a b : ℝ}
    (h : a • dYw w v + b • dYv w v = 0) : a = 0 ∧ b = 0 := by
  have h1 : -(a * (cos v / w ^ 2)) + -(b * (sin v / w)) = 0 := by
    have := congrArg Prod.fst h
    simp only [dYw, dYv, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.fst_zero] at this
    linarith
  have h2 : -(a * (sin v / w ^ 2)) + b * (cos v / w) = 0 := by
    have := congrArg Prod.snd h
    simp only [dYw, dYv, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, Prod.snd_zero] at this
    linarith
  have hcs := sin_sq_add_cos_sq v
  have ha : a / w ^ 2 = 0 := by
    linear_combination (-cos v) * h1 + (-sin v) * h2 + (-(a / w ^ 2)) * hcs
  have hb : b / w = 0 := by
    linear_combination (-sin v) * h1 + cos v * h2 + (-(b / w)) * hcs
  exact ⟨(div_eq_zero_iff.mp ha).resolve_right (pow_ne_zero 2 hw),
    (div_eq_zero_iff.mp hb).resolve_right hw⟩

/-! ### 形式解の全体（ℝ² の上） -/

/-- 中間の領域の条件：0 < k ≤ 1/2、0 < δ < w₀ ≤ k/2。 -/
structure MobOK (k δ w₀ : ℝ) : Prop where
  k_pos : 0 < k
  k_le : k ≤ 1 / 2
  δ_pos : 0 < δ
  δ_lt : δ < w₀
  w₀_le : w₀ ≤ k / 2

namespace MobOK

variable {k δ w₀ : ℝ} (h : MobOK k δ w₀)
include h

theorem w₀_pos : 0 < w₀ := h.δ_pos.trans h.δ_lt

theorem dl_pos : 0 < mDl δ w₀ := by
  unfold mDl
  have h1 : 1 / w₀ ^ 2 < 1 / δ ^ 2 := by
    apply one_div_lt_one_div_of_lt (by have := h.δ_pos; positivity)
    exact pow_lt_pow_left₀ h.δ_lt h.δ_pos.le (by norm_num)
  linarith

theorem T0_ge : 16 ≤ mT0 w₀ := by
  unfold mT0
  have hw := h.w₀_pos
  have h1 : w₀ ≤ 1 / 4 := by linarith [h.w₀_le, h.k_le]
  have h2 : w₀ ^ 2 ≤ 1 / 16 := by nlinarith
  rw [le_div_iff₀ (by positivity)]; linarith

omit h in
theorem T5_eq : mT0 w₀ + 5 * mDl δ w₀ = 1 / δ ^ 2 := by unfold mT0 mDl; ring

end MobOK

/-- 形式微分（全体）。|y| ≤ 1 では dγ、|y|² ≥ 2 では LY。 -/
def Lfull (k δ w₀ : ℝ) (y : ℝ × ℝ) : ℝ × ℝ →L[ℝ] V3 :=
  fderiv ℝ planeG y + s₀ (tau y - 1) • (LY k δ w₀ y - fderiv ℝ planeG y)

/-- 基底の写像（全体）。 -/
def bsM (k δ w₀ : ℝ) (y : ℝ × ℝ) : V3 := planeG y + sgC δ w₀ (tau y) • (mobCy k y - planeG y)

theorem tau_pos_of {y : ℝ × ℝ} {a : ℝ} (ha : 0 < a) (h : a ≤ tau y) : tau y ≠ 0 := by
  intro h0; rw [h0] at h; linarith

/-- ホーンの側で LY = dγ。 -/
theorem LY_eq_planeG {k δ w₀ : ℝ} (hok : MobOK k δ w₀) {y : ℝ × ℝ} (h1 : 1 / 2 < tau y)
    (h2 : tau y ≤ mT0 w₀ + mDl δ w₀) : LY k δ w₀ y = fderiv ℝ planeG y := by
  have hy : tau y ≠ 0 := tau_pos_of (by norm_num : (0:ℝ) < 1/2) h1.le
  obtain ⟨v, hv⟩ := exists_Ypp hy
  set w := 1 / √(tau y)
  have hw : 0 < w := one_div_sqrt_pos hy
  have ht : tau y = 1 / w ^ 2 := by rw [← hv, tau_Ypp hw.ne']
  have hw2 : w ^ 2 < 2 := by
    have : 1 / 2 < 1 / w ^ 2 := ht ▸ h1
    have hw2p : 0 < w ^ 2 := by positivity
    rw [div_lt_div_iff₀ (by norm_num) hw2p] at this; linarith
  rw [← hv]
  obtain ⟨c1, c2⟩ := planeG_chain hw hw2 v
  refine clm_ext_dY hw.ne' v ?_ ?_
  · rw [LY_dYw k δ w₀ hw v, frY_Ypp k δ w₀ hw v, fr_horn hok.dl_pos (by rw [← ht]; exact h2),
      c1]; simp
  · rw [LY_dYv k δ w₀ hw v, frY_Ypp k δ w₀ hw v, fr_horn hok.dl_pos (by rw [← ht]; exact h2),
      c2]; simp

/-- 芯の側で LY = d(C∘y⁻¹)。 -/
theorem LY_eq_mobCy {k δ w₀ : ℝ} (hok : MobOK k δ w₀) {y : ℝ × ℝ}
    (h2 : mT0 w₀ + 4 * mDl δ w₀ ≤ tau y) : LY k δ w₀ y = fderiv ℝ (mobCy k) y := by
  have hy : tau y ≠ 0 :=
    tau_pos_of (by linarith [hok.T0_ge, hok.dl_pos] : (0:ℝ) < mT0 w₀ + 4 * mDl δ w₀) h2
  obtain ⟨v, hv⟩ := exists_Ypp hy
  set w := 1 / √(tau y)
  have hw : 0 < w := one_div_sqrt_pos hy
  have ht : tau y = 1 / w ^ 2 := by rw [← hv, tau_Ypp hw.ne']
  rw [← hv]
  obtain ⟨c1, c2⟩ := mobCy_chain k hw.ne' v
  refine clm_ext_dY hw.ne' v ?_ ?_
  · rw [LY_dYw k δ w₀ hw v, frY_Ypp k δ w₀ hw v, fr_core hok.dl_pos (by rw [← ht]; exact h2),
      c1]; simp
  · rw [LY_dYv k δ w₀ hw v, frY_Ypp k δ w₀ hw v, fr_core hok.dl_pos (by rw [← ht]; exact h2),
      c2]; simp

theorem Lfull_eq_planeG {k δ w₀ : ℝ} (hok : MobOK k δ w₀) {y : ℝ × ℝ}
    (h2 : tau y ≤ mT0 w₀ + mDl δ w₀) : Lfull k δ w₀ y = fderiv ℝ planeG y := by
  unfold Lfull
  by_cases h1 : tau y ≤ 1
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_smul, add_zero]
  · rw [LY_eq_planeG hok (by linarith) h2, sub_self, smul_zero, add_zero]

theorem Lfull_eq_LY {k δ w₀ : ℝ} {y : ℝ × ℝ} (h2 : 2 ≤ tau y) : Lfull k δ w₀ y = LY k δ w₀ y := by
  unfold Lfull
  rw [Real.smoothTransition.one_of_one_le (by linarith), one_smul, add_sub_cancel]

/-- **形式微分は至るところ単射**。 -/
theorem Lfull_inj {k δ w₀ : ℝ} (hok : MobOK k δ w₀) (y : ℝ × ℝ) :
    Function.Injective (Lfull k δ w₀ y) := by
  by_cases h2 : tau y ≤ mT0 w₀ + mDl δ w₀
  · rw [Lfull_eq_planeG hok h2]; exact planeG_immersion y
  · rw [not_le] at h2
    have hT := hok.T0_ge
    have hdl := hok.dl_pos
    rw [Lfull_eq_LY (by linarith)]
    have hy : tau y ≠ 0 := tau_pos_of (by linarith : (0:ℝ) < 1) (by linarith)
    obtain ⟨v, hv⟩ := exists_Ypp hy
    set w := 1 / √(tau y)
    have hw : 0 < w := one_div_sqrt_pos hy
    have ht : tau y = 1 / w ^ 2 := by rw [← hv, tau_Ypp hw.ne']
    rw [← hv]
    refine (injective_iff_map_eq_zero _).mpr fun ξ hξ' => ?_
    set a := -(w * (cos v * ξ.1 + sin v * ξ.2) * w)
    set b := w * (-(sin v * ξ.1) + cos v * ξ.2)
    have hd := decomp_dY hw.ne' v ξ
    rw [hd, map_add, map_smul, map_smul, LY_dYw k δ w₀ hw v, LY_dYv k δ w₀ hw v,
      frY_Ypp k δ w₀ hw v, frY_Ypp k δ w₀ hw v] at hξ'
    have hfr : fr k δ w₀ w (cos v) (sin v) (1 / w ^ 2) (a, b) = 0 := by
      rw [fr_linear]; exact hξ'
    have hcs : cos v ^ 2 + sin v ^ 2 = 1 := by rw [add_comm]; exact sin_sq_add_cos_sq v
    have hwk : mT0 w₀ < 1 / w ^ 2 → w ≤ k / 2 := by
      intro hlt
      have hw0 := hok.w₀_pos
      unfold mT0 at hlt
      have : w < w₀ := by
        by_contra hc; rw [not_lt] at hc
        have : 1 / w ^ 2 ≤ 1 / w₀ ^ 2 :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hw0.le hc 2)
        linarith
      linarith [hok.w₀_le]
    have hab := fr_inj hok.k_pos hok.k_le hok.dl_pos hw hcs hwk hfr
    have ha : a = 0 := congrArg Prod.fst hab
    have hb : b = 0 := congrArg Prod.snd hab
    rw [hd]
    have ha' : -(w * (cos v * ξ.1 + sin v * ξ.2) * w) = 0 := ha
    have hb' : w * (-(sin v * ξ.1) + cos v * ξ.2) = 0 := hb
    rw [ha', hb', zero_smul, zero_smul, add_zero]

theorem contDiff_Lfull {k δ w₀ : ℝ} : ContDiff ℝ ∞ (Lfull k δ w₀) := by
  have hP : ContDiff ℝ ∞ (fderiv ℝ planeG) := contDiff_planeG.fderiv_right (m := ∞) (by simp)
  refine contDiff_iff_contDiffAt.mpr fun y => ?_
  by_cases h1 : tau y < 1
  · have heq : Lfull k δ w₀ =ᶠ[𝓝 y] fderiv ℝ planeG := by
      have hop : ∀ᶠ y' in 𝓝 y, tau y' < 1 :=
        contDiff_tau.continuous.continuousAt.eventually (gt_mem_nhds h1)
      filter_upwards [hop] with y' hy'
      unfold Lfull
      rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_smul, add_zero]
    exact hP.contDiffAt.congr_of_eventuallyEq heq
  · rw [not_lt] at h1
    have hy : tau y ≠ 0 := tau_pos_of one_pos h1
    have hs : ContDiffAt ℝ ∞ (fun y => s₀ (tau y - 1)) y :=
      (Real.smoothTransition.contDiff.comp (contDiff_tau.sub contDiff_const)).contDiffAt
    unfold Lfull
    exact hP.contDiffAt.add (hs.smul ((contDiffAt_LY k δ w₀ hy).sub hP.contDiffAt))

theorem contDiff_bsM {k δ w₀ : ℝ} (hok : MobOK k δ w₀) : ContDiff ℝ ∞ (bsM k δ w₀) := by
  refine contDiff_iff_contDiffAt.mpr fun y => ?_
  have hdl := hok.dl_pos
  have hT := hok.T0_ge
  by_cases h1 : tau y < mT0 w₀ + 3 * mDl δ w₀
  · have heq : bsM k δ w₀ =ᶠ[𝓝 y] planeG := by
      have hop : ∀ᶠ y' in 𝓝 y, tau y' < mT0 w₀ + 3 * mDl δ w₀ :=
        contDiff_tau.continuous.continuousAt.eventually (gt_mem_nhds h1)
      filter_upwards [hop] with y' hy'
      unfold bsM sgC
      rw [stg_zero hdl hy'.le, zero_smul, add_zero]
    exact contDiff_planeG.contDiffAt.congr_of_eventuallyEq heq
  · rw [not_lt] at h1
    have hy : tau y ≠ 0 := tau_pos_of (by linarith : (0:ℝ) < mT0 w₀ + 3 * mDl δ w₀) h1
    have hs : ContDiffAt ℝ ∞ (fun y => sgC δ w₀ (tau y)) y :=
      ((contDiff_stg _ _).comp contDiff_tau).contDiffAt
    unfold bsM
    exact contDiff_planeG.contDiffAt.add (hs.smul ((contDiffAt_mobCy k hy).sub
      contDiff_planeG.contDiffAt))

theorem bsM_eq_planeG {k δ w₀ : ℝ} (hok : MobOK k δ w₀) {y : ℝ × ℝ}
    (h : tau y ≤ mT0 w₀ + 3 * mDl δ w₀) : bsM k δ w₀ y = planeG y := by
  unfold bsM sgC; rw [stg_zero hok.dl_pos h, zero_smul, add_zero]

theorem bsM_eq_mobCy {k δ w₀ : ℝ} (hok : MobOK k δ w₀) {y : ℝ × ℝ}
    (h : mT0 w₀ + 4 * mDl δ w₀ ≤ tau y) : bsM k δ w₀ y = mobCy k y := by
  unfold bsM sgC
  rw [stg_one hok.dl_pos (by linarith), one_smul, add_sub_cancel]

/-- **ホロノミー**：固定する集合の開近傍で、基底の写像の微分は形式微分に等しい。 -/
theorem bsM_holonomic {k δ w₀ : ℝ} (hok : MobOK k δ w₀) {y : ℝ × ℝ}
    (h : tau y < mT0 w₀ + mDl δ w₀ ∨ mT0 w₀ + 4 * mDl δ w₀ < tau y) :
    fderiv ℝ (bsM k δ w₀) y = Lfull k δ w₀ y := by
  have hdl := hok.dl_pos
  have hT := hok.T0_ge
  rcases h with h | h
  · have heq : bsM k δ w₀ =ᶠ[𝓝 y] planeG := by
      have hop : ∀ᶠ y' in 𝓝 y, tau y' < mT0 w₀ + mDl δ w₀ :=
        contDiff_tau.continuous.continuousAt.eventually (gt_mem_nhds h)
      filter_upwards [hop] with y' hy'
      exact bsM_eq_planeG hok (by linarith)
    rw [heq.fderiv_eq, Lfull_eq_planeG hok h.le]
  · have heq : bsM k δ w₀ =ᶠ[𝓝 y] mobCy k := by
      have hop : ∀ᶠ y' in 𝓝 y, mT0 w₀ + 4 * mDl δ w₀ < tau y' :=
        contDiff_tau.continuous.continuousAt.eventually (lt_mem_nhds h)
      filter_upwards [hop] with y' hy'
      exact bsM_eq_mobCy hok hy'.le
    rw [heq.fderiv_eq, Lfull_eq_LY (by linarith), LY_eq_mobCy hok h.le]

end Zeno.Model
