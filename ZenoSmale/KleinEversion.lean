/-
# ZenoSmale.KleinEversion : 首の裏返し（h 原理の適用と Γ による延長）

第 3 版 §2.7・§3.5 (3)(4) の実現。

多様体は穿孔平面 U = ℝ² ∖ {0}（Mathlib の `Opens`）、座標 y = eʷ(cos v, sin v) である。
v について 2π 周期的な滑らかな関数 F(w, v) は、F(log|y|, arg y) として U の上の滑らかな関数になる
（`contDiffAt_polar_param`：arg の枝は slitPlane とその鏡像で切り替える）。

形式解は、基底 B̃(s, y) = B(s, log|y|, arg y)（`Bfam`）と形式微分 L̃(s, y) = L(s, log|y|, arg y)
（`Lform`）の組で、`familyJoin`・`familyTwist` により `HtpyFormalSol` に組む。
単射性とホロノミーは、(w, v) 座標の `Lform_comp_inj`・`klein_hol_identity` を、
座標変換 y = expU(w, v) の微分（全射）で U の上へ移して得る。

sphere-eversion の `immersionRel_satisfiesHPrincipleWith` の出力 f : ℝ → U → ℝ³ を
F(s, w, v) := f s (expU(w − 4k, (−1)ᵏ v)) で被覆平面へ Γ 同変に延ばし、`NeckEversion` を得る。
-/
import SphereEversion.Main
import ZenoSmale.KleinFormal

noncomputable section

namespace Zeno.Smale

open Metric Module Set Function Filter ContinuousLinearMap Topology Real
open scoped Manifold
open Zeno.Model

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### 極座標 -/

/-- 穿孔平面 U = ℝ² ∖ {0}。 -/
def U : TopologicalSpace.Opens (ℝ × ℝ) := ⟨{y | y ≠ 0}, isOpen_ne⟩

theorem mem_U {y : ℝ × ℝ} : y ∈ U ↔ y ≠ 0 := Iff.rfl

/-- 座標 y = eʷ(cos v, sin v)。 -/
def expMap (p : ℝ × ℝ) : ℝ × ℝ := (Real.exp p.1 * Real.cos p.2, Real.exp p.1 * Real.sin p.2)

theorem contDiff_expMap : ContDiff ℝ ∞ expMap := by
  unfold expMap; fun_prop

theorem expMap_ne_zero (p : ℝ × ℝ) : expMap p ≠ 0 := by
  intro h
  have h1 : Real.exp p.1 * Real.cos p.2 = 0 := congrArg Prod.fst h
  have h2 : Real.exp p.1 * Real.sin p.2 = 0 := congrArg Prod.snd h
  have he := (Real.exp_pos p.1).ne'
  have hc : Real.cos p.2 = 0 := (mul_eq_zero.mp h1).resolve_left he
  have hs : Real.sin p.2 = 0 := (mul_eq_zero.mp h2).resolve_left he
  have := Real.sin_sq_add_cos_sq p.2
  rw [hc, hs] at this
  norm_num at this

/-- ℝ² の点を複素数と見る。 -/
def toC (y : ℝ × ℝ) : ℂ := ⟨y.1, y.2⟩

theorem toC_eq (y : ℝ × ℝ) : toC y = Complex.equivRealProdCLM.symm y := by
  apply Complex.ext <;> simp [toC]

theorem contDiff_toC : ContDiff ℝ ∞ toC := by
  have : toC = fun y => Complex.equivRealProdCLM.symm y := funext toC_eq
  rw [this]
  exact (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).contDiff

theorem toC_ne_zero {y : ℝ × ℝ} (hy : y ≠ 0) : toC y ≠ 0 := by
  intro h
  apply hy
  have h1 : y.1 = 0 := congrArg Complex.re h
  have h2 : y.2 = 0 := congrArg Complex.im h
  exact Prod.ext h1 h2

theorem toC_neg (y : ℝ × ℝ) : toC (-y) = -toC y := by
  apply Complex.ext <;> simp [toC]

/-- 逆座標 (log|y|, arg y)。 -/
def logArg (y : ℝ × ℝ) : ℝ × ℝ := ((Complex.log (toC y)).re, (Complex.log (toC y)).im)

theorem logArg_fst (y : ℝ × ℝ) : (logArg y).1 = Real.log ‖toC y‖ := by
  simp [logArg, Complex.log_re]

theorem logArg_snd (y : ℝ × ℝ) : (logArg y).2 = Complex.arg (toC y) := by
  simp [logArg, Complex.log_im]

theorem toC_expMap (p : ℝ × ℝ) :
    toC (expMap p) = (Real.exp p.1 : ℂ) * (Complex.cos p.2 + Complex.sin p.2 * Complex.I) := by
  apply Complex.ext <;>
    simp only [toC, expMap, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.cos_ofReal_re,
      Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im] <;> ring

theorem norm_toC_expMap (p : ℝ × ℝ) : ‖toC (expMap p)‖ = Real.exp p.1 := by
  rw [toC_expMap, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cos_add_sin_mul_I, mul_one]

theorem logArg_expMap_fst (p : ℝ × ℝ) : (logArg (expMap p)).1 = p.1 := by
  rw [logArg_fst, norm_toC_expMap, Real.log_exp]

theorem logArg_expMap_snd (p : ℝ × ℝ) :
    ∃ k : ℤ, (logArg (expMap p)).2 = p.2 - k * (2 * π) := by
  rw [logArg_snd, toC_expMap, Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod (Real.exp_pos p.1)]
  refine ⟨toIocDiv Real.two_pi_pos (-π) p.2, ?_⟩
  have := self_sub_toIocMod Real.two_pi_pos (-π) p.2
  rw [zsmul_eq_mul] at this
  linarith

theorem expMap_logArg {y : ℝ × ℝ} (hy : y ≠ 0) : expMap (logArg y) = y := by
  have hz := toC_ne_zero hy
  have hn : 0 < ‖toC y‖ := norm_pos_iff.mpr hz
  simp only [expMap, logArg_fst, logArg_snd, Real.exp_log hn, Complex.cos_arg hz, Complex.sin_arg]
  refine Prod.ext ?_ ?_
  · show ‖toC y‖ * ((toC y).re / ‖toC y‖) = (toC y).re
    field_simp
  · show ‖toC y‖ * ((toC y).im / ‖toC y‖) = (toC y).im
    field_simp

/-! ### 周期関数の極座標表示 -/

section Polar

variable {X : Type*}

theorem periodic_int {F : ℝ × ℝ → X} (hper : ∀ w v, F (w, v + 2 * π) = F (w, v)) (w v : ℝ)
    (k : ℤ) : F (w, v + k * (2 * π)) = F (w, v) := by
  have hp : Function.Periodic (fun v => F (w, v)) (2 * π) := fun v => hper w v
  exact hp.int_mul k v

theorem polar_exp {F : ℝ × ℝ → X} (hper : ∀ w v, F (w, v + 2 * π) = F (w, v)) (p : ℝ × ℝ) :
    F (logArg (expMap p)) = F p := by
  obtain ⟨k, hk⟩ := logArg_expMap_snd p
  have e : logArg (expMap p) = (p.1, p.2 + (-k : ℤ) * (2 * π)) := by
    refine Prod.ext (logArg_expMap_fst p) ?_
    rw [hk]; push_cast; ring
  rw [e, periodic_int hper]

theorem contDiffAt_logArg {y : ℝ × ℝ} (hy : toC y ∈ Complex.slitPlane) :
    ContDiffAt ℝ ∞ logArg y := by
  have hlog : ContDiffAt ℝ ∞ Complex.log (toC y) :=
    ContDiffAt.restrict_scalars ℝ (Complex.contDiffAt_log hy (n := ∞))
  have h : ContDiffAt ℝ ∞ (fun y => Complex.log (toC y)) y :=
    hlog.comp y contDiff_toC.contDiffAt
  have hre : ContDiffAt ℝ ∞ (fun y => (Complex.log (toC y)).re) y :=
    (Complex.reCLM.contDiff.contDiffAt).comp y h
  have him : ContDiffAt ℝ ∞ (fun y => (Complex.log (toC y)).im) y :=
    (Complex.imCLM.contDiff.contDiffAt).comp y h
  exact hre.prodMk him

/-- arg の鏡像の枝：(log|−y|, arg(−y) + π)。 -/
def shiftArg (y : ℝ × ℝ) : ℝ × ℝ := ((logArg (-y)).1, (logArg (-y)).2 + π)

theorem polar_shift {F : ℝ × ℝ → X} (hper : ∀ w v, F (w, v + 2 * π) = F (w, v)) {y : ℝ × ℝ}
    (hy : y ≠ 0) : F (logArg y) = F (shiftArg y) := by
  have hz := toC_ne_zero hy
  have hang := Complex.arg_neg_coe_angle hz
  rw [← Real.Angle.coe_add, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at hang
  obtain ⟨k, hk⟩ := hang
  have e1 : (logArg (-y)).1 = (logArg y).1 := by
    rw [logArg_fst, logArg_fst, toC_neg, norm_neg]
  have e2 : (logArg y).2 = ((logArg (-y)).2 + π) + (-(k + 1) : ℤ) * (2 * π) := by
    rw [logArg_snd, logArg_snd, toC_neg]
    push_cast
    linarith
  have e : logArg y = ((shiftArg y).1, (shiftArg y).2 + (-(k + 1) : ℤ) * (2 * π)) := by
    refine Prod.ext ?_ e2
    simp only [shiftArg, e1]
  rw [e, periodic_int hper]

theorem slit_or_neg {y : ℝ × ℝ} (hy : y ≠ 0) :
    toC y ∈ Complex.slitPlane ∨ toC (-y) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff, Complex.mem_slitPlane_iff, toC_neg]
  simp only [toC, Complex.neg_re, Complex.neg_im, neg_ne_zero]
  by_cases h1 : 0 < y.1
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : y.2 = 0
    · right; left
      have : y.1 ≠ 0 := fun h => hy (Prod.ext h h2)
      push Not at h1
      have : y.1 < 0 := lt_of_le_of_ne h1 this
      linarith
    · exact Or.inl (Or.inr h2)

/-- **周期関数の極座標表示は穿孔平面の上で滑らかである**（助変数つき）。 -/
theorem contDiffAt_polar_param [NormedAddCommGroup X] [NormedSpace ℝ X] {F : ℝ × ℝ × ℝ → X}
    (hF : ContDiff ℝ ∞ F)
    (hper : ∀ s w v, F (s, w, v + 2 * π) = F (s, w, v)) {q : ℝ × (ℝ × ℝ)} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => F (q.1, logArg q.2)) q := by
  rcases slit_or_neg hq with hs | hs
  · exact hF.contDiffAt.comp q (contDiffAt_fst.prodMk ((contDiffAt_logArg hs).comp q contDiffAt_snd))
  · have hopen : IsOpen {q : ℝ × (ℝ × ℝ) | q.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
    have e : (fun q : ℝ × (ℝ × ℝ) => F (q.1, logArg q.2)) =ᶠ[𝓝 q]
        fun q => F (q.1, shiftArg q.2) := by
      filter_upwards [hopen.mem_nhds hq] with z hz
      exact polar_shift (F := fun p => F (z.1, p)) (fun w v => hper z.1 w v) hz
    have hsh : ContDiffAt ℝ ∞ shiftArg q.2 := by
      have hl : ContDiffAt ℝ ∞ (fun y => logArg (-y)) q.2 :=
        (contDiffAt_logArg hs).comp q.2 contDiff_neg.contDiffAt
      exact (contDiffAt_fst.comp q.2 hl).prodMk ((contDiffAt_snd.comp q.2 hl).add contDiffAt_const)
    exact (hF.contDiffAt.comp q (contDiffAt_fst.prodMk (hsh.comp q contDiffAt_snd))).congr_of_eventuallyEq e

end Polar

/-! ### 穿孔平面の多様体構造 -/

instance : LocallyCompactSpace U := U.isOpen.locallyCompactSpace

/-- U → ℝ² の包含は滑らかである。 -/
theorem contMDiff_val : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (Subtype.val : U → ℝ × ℝ) :=
  contMDiff_subtype_val

/-- 座標 (w, v) ↦ eʷ(cos v, sin v) ∈ U。 -/
def expU (p : ℝ × ℝ) : U := ⟨expMap p, expMap_ne_zero p⟩

theorem val_expU (p : ℝ × ℝ) : (expU p : ℝ × ℝ) = expMap p := rfl

theorem contMDiff_expU : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ expU := by
  rw [← ContMDiff.subtypeVal_comp_iff]
  exact contDiff_expMap.contMDiff

theorem expU_logArg (y : U) : expU (logArg (y : ℝ × ℝ)) = y :=
  Subtype.ext (expMap_logArg y.2)

/-- 一般の空間に値をもつ写像の偏導関数と全微分。 -/
theorem fderiv_apply_of_partials_gen {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {w v : ℝ} {W V : F}
    (hf : DifferentiableAt ℝ f (w, v))
    (hw : HasDerivAt (fun w => f (w, v)) W w) (hv : HasDerivAt (fun v => f (w, v)) V v)
    (ξ : ℝ × ℝ) : fderiv ℝ f (w, v) ξ = ξ.1 • W + ξ.2 • V := by
  have h1 : fderiv ℝ f (w, v) (1, 0) = W := by
    have hl : HasDerivAt (fun x : ℝ => ((x, v) : ℝ × ℝ)) (1, 0) w :=
      (hasDerivAt_id' w).prodMk (hasDerivAt_const w v)
    have := hf.hasFDerivAt.comp_hasDerivAt w hl
    exact this.unique hw
  have h2 : fderiv ℝ f (w, v) (0, 1) = V := by
    have hl : HasDerivAt (fun x : ℝ => ((w, x) : ℝ × ℝ)) (0, 1) v :=
      (hasDerivAt_const v w).prodMk (hasDerivAt_id' v)
    have := hf.hasFDerivAt.comp_hasDerivAt v hl
    exact this.unique hv
  have e : ξ = ξ.1 • ((1, 0) : ℝ × ℝ) + ξ.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul, h1, h2]

theorem hasDerivAt_expMap_w (w v : ℝ) :
    HasDerivAt (fun w => expMap (w, v)) (Real.exp w * Real.cos v, Real.exp w * Real.sin v) w := by
  have e : (fun w => expMap (w, v)) = fun w => (Real.exp w * Real.cos v, Real.exp w * Real.sin v) :=
    rfl
  rw [e]
  exact ((Real.hasDerivAt_exp w).mul_const (Real.cos v)).prodMk
    ((Real.hasDerivAt_exp w).mul_const (Real.sin v))

theorem hasDerivAt_expMap_v (w v : ℝ) :
    HasDerivAt (fun v => expMap (w, v))
      (-(Real.exp w * Real.sin v), Real.exp w * Real.cos v) v := by
  have e : (fun v => expMap (w, v)) = fun v => (Real.exp w * Real.cos v, Real.exp w * Real.sin v) :=
    rfl
  rw [e]
  refine (((Real.hasDerivAt_cos v).const_mul (Real.exp w)).prodMk
    ((Real.hasDerivAt_sin v).const_mul (Real.exp w))).congr_deriv ?_
  refine Prod.ext ?_ rfl
  simp only
  ring

/-- 座標変換の微分は単射である。 -/
theorem fderiv_expMap_injective (p : ℝ × ℝ) : Injective (fderiv ℝ expMap p) := by
  obtain ⟨w, v⟩ := p
  refine (injective_iff_map_eq_zero _).mpr fun ξ hξ => ?_
  rw [fderiv_apply_of_partials_gen (contDiff_expMap.differentiable (by simp) _)
    (hasDerivAt_expMap_w w v) (hasDerivAt_expMap_v w v)] at hξ
  have h1 : ξ.1 * (Real.exp w * Real.cos v) + ξ.2 * (-(Real.exp w * Real.sin v)) = 0 := by
    have := congrArg Prod.fst hξ
    simpa using this
  have h2 : ξ.1 * (Real.exp w * Real.sin v) + ξ.2 * (Real.exp w * Real.cos v) = 0 := by
    have := congrArg Prod.snd hξ
    simpa using this
  have he := (Real.exp_pos w).ne'
  have hcs := Real.sin_sq_add_cos_sq v
  have e1 : ξ.1 * Real.exp w = 0 := by
    linear_combination Real.cos v * h1 + Real.sin v * h2 - ξ.1 * Real.exp w * hcs
  have e2 : ξ.2 * Real.exp w = 0 := by
    linear_combination (-(Real.sin v)) * h1 + Real.cos v * h2 - ξ.2 * Real.exp w * hcs
  exact Prod.ext ((mul_eq_zero.mp e1).resolve_right he) ((mul_eq_zero.mp e2).resolve_right he)

theorem mf_eq' {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] (f : E → E') (x : E) (ξ : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E') f x ξ = fderiv ℝ f x ξ := by
  rw [mfderiv_eq_fderiv]
  rfl

/-- expU の微分は単射である（包含との合成が expMap）。 -/
theorem mfderiv_expU_injective (p : ℝ × ℝ) :
    Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p) := by
  have hval : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (Subtype.val : U → ℝ × ℝ) (expU p) :=
    contMDiff_val.mdifferentiableAt (by simp)
  have hexp : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p :=
    contMDiff_expU.mdifferentiableAt (by simp)
  have hchain : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expMap p =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (Subtype.val : U → ℝ × ℝ) (expU p)).comp
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p) :=
    mfderiv_comp p hval hexp
  intro ξ η h
  have hξ : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expMap p ξ =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (Subtype.val : U → ℝ × ℝ) (expU p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p ξ) :=
    congrArg (fun L => L ξ) hchain
  have hη : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expMap p η =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (Subtype.val : U → ℝ × ℝ) (expU p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p η) :=
    congrArg (fun L => L η) hchain
  rw [h] at hξ
  exact fderiv_expMap_injective p
    ((mf_eq' expMap p ξ).symm.trans ((hξ.trans hη.symm).trans (mf_eq' expMap p η)))

theorem mfderiv_expU_surjective (p : ℝ × ℝ) :
    Surjective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p) := by
  have hinj := mfderiv_expU_injective p
  let f : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ :=
    { toFun := fun ξ => mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p ξ
      map_add' := fun ξ η => map_add (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p) ξ η
      map_smul' := fun c ξ => map_smul (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p) c ξ }
  have hf : Injective f := hinj
  exact LinearMap.injective_iff_surjective.mp hf

/-! ### 極座標表示した源曲面・基底・形式微分 -/

section Sol

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

/-- Ŝ の極座標表示 Ŝ̃(y) = Ŝ(log|y|, arg y)。 -/
def ShatP (w₀ : ℝ) (y : ℝ × ℝ) : V3 := Shat w₀ (logArg y).1 (logArg y).2

/-- 基底の極座標表示 B̃(s, y) = B(s, log|y|, arg y)。 -/
def BfamP (w₀ s : ℝ) (y : ℝ × ℝ) : V3 := Bfam w₀ s (logArg y).1 (logArg y).2

/-- 形式微分の極座標表示 L̃(s, y) = L(s, log|y|, arg y)。 -/
def LformP (w₀ s : ℝ) (y : ℝ × ℝ) : V3 →L[ℝ] V3 := Lform w₀ s (logArg y).1 (logArg y).2

theorem ShatP_expMap (p : ℝ × ℝ) : ShatP w₀ (expMap p) = Shat w₀ p.1 p.2 :=
  polar_exp (F := fun p : ℝ × ℝ => Shat w₀ p.1 p.2) (fun w v => Shat_periodic w₀ w v) p

theorem BfamP_expMap (s : ℝ) (p : ℝ × ℝ) : BfamP w₀ s (expMap p) = Bfam w₀ s p.1 p.2 :=
  polar_exp (F := fun p : ℝ × ℝ => Bfam w₀ s p.1 p.2) (fun w v => Bfam_periodic s w v) p

theorem LformP_expMap (s : ℝ) (p : ℝ × ℝ) : LformP w₀ s (expMap p) = Lform w₀ s p.1 p.2 :=
  polar_exp (F := fun p : ℝ × ℝ => Lform w₀ s p.1 p.2) (fun w v => Lform_periodic s w v) p

include h0 h1 in
theorem contDiffAt_ShatP {y : ℝ × ℝ} (hy : y ≠ 0) : ContDiffAt ℝ ∞ (ShatP w₀) y := by
  have hF : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Shat w₀ q.2.1 q.2.2) := by
    have h := (contDiff_Shat h0 h1).comp (contDiff_snd (E := ℝ) (F := ℝ × ℝ))
    exact h
  have h := contDiffAt_polar_param hF (fun _ w v => Shat_periodic w₀ w v) (q := ((0 : ℝ), y)) hy
  have h' := h.comp y (contDiffAt_const.prodMk contDiffAt_id)
  exact h'

include h0 h1 in
theorem contDiffAt_BfamP {q : ℝ × (ℝ × ℝ)} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => BfamP w₀ q.1 q.2) q :=
  contDiffAt_polar_param (F := fun q : ℝ × ℝ × ℝ => Bfam w₀ q.1 q.2.1 q.2.2) (contDiff_Bfam h0 h1)
    (fun s w v => Bfam_periodic s w v) hq

include h0 h1 in
theorem contDiffAt_LformP {q : ℝ × (ℝ × ℝ)} (hq : q.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (ℝ × ℝ) => LformP w₀ q.1 q.2) q :=
  contDiffAt_polar_param (F := fun q : ℝ × ℝ × ℝ => Lform w₀ q.1 q.2.1 q.2.2) (contDiff_Lform h0 h1)
    (fun s w v => Lform_periodic s w v) hq

/-! ### U の上の 1 ジェットの土台と形式解 -/

include h0 h1 in
theorem contMDiff_ShatU : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (fun y : U => ShatP w₀ y) := by
  intro y
  rw [contMDiffAt_subtype_iff]
  exact contMDiffAt_iff_contDiffAt.mpr (contDiffAt_ShatP h0 h1 y.2)

/-- 1 ジェットの土台 Ŝ̃ : U → ℝ³。 -/
def gU : C^∞⟮𝓘(ℝ, ℝ × ℝ), U; 𝓘(ℝ, V3), V3⟯ := ⟨fun y => ShatP w₀ y, contMDiff_ShatU h0 h1⟩

/-- 基底の族 B̃(s, y)。 -/
def bsK (w₀ : ℝ) (q : ℝ × U) : V3 := BfamP w₀ q.1 q.2

theorem contMDiff_incl :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ × (ℝ × ℝ)) ∞
      (fun q : ℝ × U => ((q.1, (q.2 : ℝ × ℝ)) : ℝ × (ℝ × ℝ))) :=
  contMDiff_fst.prodMk_space (contMDiff_val.comp contMDiff_snd)

include h0 h1 in
theorem bsK_smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3) ∞ (bsK w₀) := by
  intro q
  have hG : ContMDiffAt 𝓘(ℝ, ℝ × (ℝ × ℝ)) 𝓘(ℝ, V3) ∞
      (fun q : ℝ × (ℝ × ℝ) => BfamP w₀ q.1 q.2) (q.1, (q.2 : ℝ × ℝ)) :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_BfamP h0 h1 q.2.2)
  have h := hG.comp q (contMDiff_incl q)
  exact h

include h0 h1 in
theorem LK_smooth (q : ℝ × U) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3 →L[ℝ] V3) ∞
      (fun q : ℝ × U => LformP w₀ q.1 q.2) q := by
  have hG : ContMDiffAt 𝓘(ℝ, ℝ × (ℝ × ℝ)) 𝓘(ℝ, V3 →L[ℝ] V3) ∞
      (fun q : ℝ × (ℝ × ℝ) => LformP w₀ q.1 q.2) (q.1, (q.2 : ℝ × ℝ)) :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_LformP h0 h1 q.2.2)
  have h := hG.comp q (contMDiff_incl q)
  exact h

/-- 形式解の土台（基底 B̃ と形式微分 L̃∘dŜ̃）。 -/
def kleinAux : FamilyOneJetSec 𝓘(ℝ, ℝ × ℝ) U 𝓘(ℝ, V3) V3 𝓘(ℝ, ℝ) ℝ :=
  familyJoin (bsK_smooth h0 h1) <|
    familyTwist (drop (oneJetExtSec (gU h0 h1))) (fun q : ℝ × U => LformP w₀ q.1 q.2)
      (LK_smooth h0 h1)

include h0 h1 in
/-- Ŝ̃∘expU = Ŝ の連鎖律。 -/
theorem mfderiv_gU_chain (p : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) p =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (gU h0 h1) (expU p)).comp
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p) := by
  have hg : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (gU h0 h1) (expU p) :=
    (gU h0 h1).contMDiff.mdifferentiableAt (by simp)
  have hexp : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p :=
    contMDiff_expU.mdifferentiableAt (by simp)
  have e : ((gU h0 h1 : U → V3) ∘ expU) = fun p : ℝ × ℝ => Shat w₀ p.1 p.2 :=
    funext fun p => ShatP_expMap p
  rw [← e]
  exact mfderiv_comp p hg hexp

include h0 h1 in
/-- **形式解は単射である**（(w, v) 座標の `Lform_comp_inj` を U へ移す）。 -/
theorem kleinSol_inj (t : ℝ) (y : U) :
    Injective ((LformP w₀ t y).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (gU h0 h1) y)) := by
  have hexp : expU (logArg (y : ℝ × ℝ)) = y := expU_logArg y
  rw [← hexp, val_expU, LformP_expMap]
  set p := logArg (y : ℝ × ℝ) with hp
  have hchain := mfderiv_gU_chain h0 h1 p
  have hsurj := mfderiv_expU_surjective p
  have hkey := Lform_comp_inj h0 h1 t p.1 p.2
  have hpt : ∀ ζ, (Lform w₀ t p.1 p.2).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (gU h0 h1) (expU p))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p ζ) =
      (Lform w₀ t p.1 p.2).comp (fderiv ℝ (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) (p.1, p.2)) ζ := by
    intro ζ
    have e : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) p ζ =
        mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (gU h0 h1) (expU p)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p ζ) := congrArg (fun L => L ζ) hchain
    have e' := mf_eq' (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) p ζ
    exact congrArg (Lform w₀ t p.1 p.2) (e.symm.trans e')
  intro ξ η h
  obtain ⟨ξ', rfl⟩ := hsurj ξ
  obtain ⟨η', rfl⟩ := hsurj η
  rw [hpt, hpt] at h
  exact congrArg _ (hkey h)

/-- **形式解**。 -/
def kleinSol : HtpyFormalSol (immersionRel 𝓘(ℝ, ℝ × ℝ) U 𝓘(ℝ, V3) V3) :=
  { kleinAux h0 h1 with
    is_sol' := fun t y => kleinSol_inj h0 h1 t y }

include h0 h1 in
theorem contMDiff_bsU (s : ℝ) : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (fun y : U => bsK w₀ (s, y)) :=
  (bsK_smooth h0 h1).comp (contMDiff_const.prodMk contMDiff_id)

include h0 h1 in
/-- B̃_s∘expU = B_s の連鎖律。 -/
theorem mfderiv_bsU_chain (s : ℝ) (p : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Bfam w₀ s p.1 p.2) p =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun y : U => bsK w₀ (s, y)) (expU p)).comp
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p) := by
  have hb : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun y : U => bsK w₀ (s, y)) (expU p) :=
    (contMDiff_bsU h0 h1 s).mdifferentiableAt (by simp)
  have hexp : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p :=
    contMDiff_expU.mdifferentiableAt (by simp)
  have e : ((fun y : U => bsK w₀ (s, y)) ∘ expU) = fun p : ℝ × ℝ => Bfam w₀ s p.1 p.2 :=
    funext fun p => BfamP_expMap s p
  rw [← e]
  exact mfderiv_comp p hb hexp

set_option backward.isDefEq.respectTransparency false in
include h0 h1 in
/-- **ホロノミー**：s < ¼、s > ¾、|log|y|| > 4w₀/5 で形式解は基底の 1 ジェットに一致する。 -/
theorem kleinSol_hol {q : ℝ × U}
    (hp : q.1 < 1 / 4 ∨ 3 / 4 < q.1 ∨ w₀ * (4 / 5) < |(logArg (q.2 : ℝ × ℝ)).1|) :
    (kleinSol h0 h1 q.1).toOneJetSec.IsHolonomicAt q.2 := by
  change
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun y : U ↦ bsK w₀ (q.1, y)) q.2 =
      (LformP w₀ q.1 q.2).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (gU h0 h1) q.2)
  obtain ⟨s, y⟩ := q
  simp only at hp ⊢
  have hexp : expU (logArg (y : ℝ × ℝ)) = y := expU_logArg y
  rw [← hexp, val_expU, LformP_expMap]
  set p := logArg (y : ℝ × ℝ) with hp'
  have hchainB := mfderiv_bsU_chain h0 h1 s p
  have hchainS := mfderiv_gU_chain h0 h1 p
  have hsurj := mfderiv_expU_surjective p
  have hhol := klein_hol_identity h0 h1 (s := s) (w := p.1) hp p.2
  refine ContinuousLinearMap.ext fun ζ => ?_
  obtain ⟨ξ, rfl⟩ := hsurj ζ
  have e1 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Bfam w₀ s p.1 p.2) p ξ =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun y : U => bsK w₀ (s, y)) (expU p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p ξ) := congrArg (fun L => L ξ) hchainB
  have e2 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Shat w₀ p.1 p.2) p ξ =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (gU h0 h1) (expU p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p ξ) := congrArg (fun L => L ξ) hchainS
  have e3 := congrArg (fun L => L ξ) hhol
  show mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun y : U => bsK w₀ (s, y)) (expU p)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p ξ) =
    (Lform w₀ s p.1 p.2) (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (gU h0 h1) (expU p)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p ξ))
  rw [← e1, ← e2, mf_eq', mf_eq']
  exact e3

/-- 固定する閉集合：端の時刻と首の外。 -/
def fixedK (w₀ : ℝ) : Set (ℝ × U) :=
  {q | q.1 ≤ 0 ∨ 1 ≤ q.1 ∨ w₀ * (9 / 10) ≤ |(logArg (q.2 : ℝ × ℝ)).1|}

theorem continuous_wU : Continuous (fun y : U => (logArg (y : ℝ × ℝ)).1) := by
  have e : (fun y : U => (logArg (y : ℝ × ℝ)).1) = fun y : U => Real.log ‖toC (y : ℝ × ℝ)‖ :=
    funext fun y => logArg_fst _
  rw [e]
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have hz : ‖toC (y : ℝ × ℝ)‖ ≠ 0 := norm_ne_zero_iff.mpr (toC_ne_zero y.2)
  exact ContinuousAt.comp (g := Real.log) (f := fun y : U => ‖toC (y : ℝ × ℝ)‖)
    (Real.continuousAt_log hz)
    ((continuous_norm.comp (contDiff_toC.continuous.comp continuous_subtype_val)).continuousAt)

theorem isClosed_fixedK : IsClosed (fixedK w₀) := by
  have hc : Continuous (fun q : ℝ × U => |(logArg (q.2 : ℝ × ℝ)).1|) :=
    continuous_abs.comp (continuous_wU.comp continuous_snd)
  have h1' : IsClosed {q : ℝ × U | q.1 ≤ 0} := isClosed_le continuous_fst continuous_const
  have h2' : IsClosed {q : ℝ × U | 1 ≤ q.1} := isClosed_le continuous_const continuous_fst
  have h3' : IsClosed {q : ℝ × U | w₀ * (9 / 10) ≤ |(logArg (q.2 : ℝ × ℝ)).1|} :=
    isClosed_le continuous_const hc
  exact h1'.union (h2'.union h3')

include h0 h1 in
theorem kleinSol_hol_near :
    ∀ᶠ q : ℝ × U near fixedK w₀, (kleinSol h0 h1 q.1).toOneJetSec.IsHolonomicAt q.2 := by
  have hc : Continuous (fun q : ℝ × U => |(logArg (q.2 : ℝ × ℝ)).1|) :=
    continuous_abs.comp (continuous_wU.comp continuous_snd)
  have hopen : IsOpen {q : ℝ × U | q.1 < 1 / 4 ∨ 3 / 4 < q.1 ∨
      w₀ * (4 / 5) < |(logArg (q.2 : ℝ × ℝ)).1|} := by
    have h1' : IsOpen {q : ℝ × U | q.1 < 1 / 4} := isOpen_lt continuous_fst continuous_const
    have h2' : IsOpen {q : ℝ × U | 3 / 4 < q.1} := isOpen_lt continuous_const continuous_fst
    have h3' : IsOpen {q : ℝ × U | w₀ * (4 / 5) < |(logArg (q.2 : ℝ × ℝ)).1|} :=
      isOpen_lt continuous_const hc
    exact h1'.union (h2'.union h3')
  have hmem : {q : ℝ × U | q.1 < 1 / 4 ∨ 3 / 4 < q.1 ∨
      w₀ * (4 / 5) < |(logArg (q.2 : ℝ × ℝ)).1|} ∈ 𝓝ˢ (fixedK w₀) := by
    refine hopen.mem_nhdsSet.mpr ?_
    rintro q (hq | hq | hq)
    · left; linarith
    · right; left; linarith
    · right; right; nlinarith
  filter_upwards [hmem] with q hq
  exact kleinSol_hol h0 h1 hq

include h0 h1 in
/-- **h 原理の適用**：U の上の滑らかなはめ込みの族 f(s, ·) で、固定集合の上で基底に一致し、
至るところ基底に ε で近いものが存在する。 -/
theorem klein_hprinciple {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → U → V3,
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3) ∞ (uncurry f) ∧
      (∀ s y, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f s) y)) ∧
      (∀ s (y : U), (s ≤ 0 ∨ 1 ≤ s ∨ w₀ * (9 / 10) ≤ |(logArg (y : ℝ × ℝ)).1|) →
        f s y = BfamP w₀ s y) ∧
      (∀ s (y : U), dist (f s y) (BfamP w₀ s y) ≤ ε) := by
  have ineq_rank : finrank ℝ (ℝ × ℝ) < finrank ℝ V3 := by simp
  rcases (immersionRel_satisfiesHPrincipleWith 𝓘(ℝ, ℝ × ℝ) U 𝓘(ℝ, V3) V3 𝓘(ℝ, ℝ) ℝ
      ineq_rank (isClosed_fixedK (w₀ := w₀)) (ε := fun _ => ε) (fun _ => hε) continuous_const).bs
      (kleinSol h0 h1) (kleinSol_hol_near h0 h1) with ⟨f, h₁, h₂, h₃, h₅⟩
  have hfix := h₂.forall_mem principal_le_nhdsSet
  refine ⟨f, h₁, fun s y => h₅ s y, fun s y hy => hfix (s, y) hy, fun s y => h₃ s y⟩

end Sol

/-! ### ユークリッド距離の道具 -/

section Norm

/-- ユークリッドノルム |q| = √(nsq q)。 -/
def en (q : V3) : ℝ := √(nsq q)

theorem en_nonneg (q : V3) : 0 ≤ en q := Real.sqrt_nonneg _

theorem en_sq (q : V3) : en q ^ 2 = nsq q := Real.sq_sqrt (nsq_nonneg q)

theorem dot_sq_le (a b : V3) : dot a b ^ 2 ≤ nsq a * nsq b := by
  have h := nsq_cross a b
  have := nsq_nonneg (cross a b)
  linarith

theorem dot_le_en_mul_en (a b : V3) : dot a b ≤ en a * en b := by
  have h := dot_sq_le a b
  have hab : 0 ≤ en a * en b := mul_nonneg (en_nonneg a) (en_nonneg b)
  have e : (en a * en b) ^ 2 = nsq a * nsq b := by rw [mul_pow, en_sq, en_sq]
  nlinarith [sq_abs (dot a b), abs_nonneg (dot a b), le_abs_self (dot a b)]

theorem nsq_add (a b : V3) : nsq (a + b) = nsq a + 2 * dot a b + nsq b := by
  simp only [nsq, dot, Prod.fst_add, Prod.snd_add]; ring

theorem en_add_le (a b : V3) : en (a + b) ≤ en a + en b := by
  have h := dot_le_en_mul_en a b
  have hs : nsq (a + b) ≤ (en a + en b) ^ 2 := by
    rw [nsq_add, add_sq, en_sq, en_sq]; linarith
  have hnn : 0 ≤ en a + en b := add_nonneg (en_nonneg a) (en_nonneg b)
  calc en (a + b) = √(nsq (a + b)) := rfl
    _ ≤ √((en a + en b) ^ 2) := Real.sqrt_le_sqrt hs
    _ = en a + en b := Real.sqrt_sq hnn

theorem en_neg (a : V3) : en (-a) = en a := by
  simp only [en, nsq_neg]

theorem en_sub_le (a b c : V3) : en (a - c) ≤ en (a - b) + en (b - c) := by
  have e : a - c = (a - b) + (b - c) := by abel
  rw [e]; exact en_add_le _ _

/-- 逆向きの三角不等式。 -/
theorem en_sub_en_le (a b : V3) : en a - en b ≤ en (a - b) := by
  have e : a = (a - b) + b := by abel
  have := en_add_le (a - b) b
  rw [← e] at this
  linarith

theorem abs_en_sub_en_le (a b : V3) : |en a - en b| ≤ en (a - b) := by
  rw [abs_le]
  constructor
  · have := en_sub_en_le b a
    rw [← en_neg (b - a), neg_sub] at this
    linarith
  · exact en_sub_en_le a b

theorem en_eq_zero_iff (a : V3) : en a = 0 ↔ a = wp := by
  constructor
  · intro h
    have : nsq a = 0 := by
      have := en_sq a; rw [h] at this; linarith
    by_contra hne
    exact (nsq_pos_of_ne hne).ne' this
  · rintro rfl; simp [en, nsq, dot, wp]

theorem en_pos_of_ne {a : V3} (h : a ≠ wp) : 0 < en a :=
  lt_of_le_of_ne (en_nonneg a) (Ne.symm (fun h' => h ((en_eq_zero_iff a).mp h')))

/-- V3 = ℝ × ℝ × ℝ の距離（成分の最大値）からの ユークリッド距離の評価。 -/
theorem nsq_le_of_dist_le {a b : V3} {ε : ℝ} (h : dist a b ≤ ε) : nsq (a - b) ≤ 3 * ε ^ 2 := by
  rw [Prod.dist_eq, Prod.dist_eq] at h
  have h1 : dist a.1 b.1 ≤ ε := (le_max_left _ _).trans h
  have h2 : dist a.2.1 b.2.1 ≤ ε := ((le_max_left _ _).trans (le_max_right _ _)).trans h
  have h3 : dist a.2.2 b.2.2 ≤ ε := ((le_max_right _ _).trans (le_max_right _ _)).trans h
  rw [Real.dist_eq] at h1 h2 h3
  have hε : 0 ≤ ε := (abs_nonneg _).trans h1
  simp only [nsq, dot, Prod.fst_sub, Prod.snd_sub]
  nlinarith [sq_abs (a.1 - b.1), sq_abs (a.2.1 - b.2.1), sq_abs (a.2.2 - b.2.2),
    abs_nonneg (a.1 - b.1), abs_nonneg (a.2.1 - b.2.1), abs_nonneg (a.2.2 - b.2.2)]

theorem en_le_of_dist_le {a b : V3} {ε : ℝ} (hε : 0 ≤ ε) (h : dist a b ≤ ε) :
    en (a - b) ≤ 2 * ε := by
  have h1 := nsq_le_of_dist_le h
  have h2 : nsq (a - b) ≤ (2 * ε) ^ 2 := by nlinarith
  calc en (a - b) = √(nsq (a - b)) := rfl
    _ ≤ √((2 * ε) ^ 2) := Real.sqrt_le_sqrt h2
    _ = 2 * ε := Real.sqrt_sq (by linarith)

end Norm

/-! ### 首の裏返し：被覆平面への Γ 同変な延長 -/

/-- **首の裏返し**（第 3 版 §2.7）：首だけを動かし、端点では Ŝ と −Ŝ∘φ、首の外では Ŝ に等しい
正則ホモトピーで、首の像は ℘ の半径 w₀ + ε の球に入り、基底 B に ε で近い。 -/
structure NeckEversion (w₀ ε : ℝ) (S : ℝ → ℝ → V3) (F : ℝ → ℝ → ℝ → V3) : Prop where
  smooth : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2)
  immersion : ∀ (s : ℝ) (p : ℝ × ℝ), Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => F s p.1 p.2) p)
  periodic : ∀ s w v : ℝ, F s w (v + 2 * π) = F s w v
  glide : ∀ s w v : ℝ, F s (w + 4) (-v) = F s w v
  start : ∀ s w v : ℝ, s ≤ 0 → F s w v = S w v
  finish : ∀ s w v : ℝ, 1 ≤ s → |w| ≤ 1 → F s w v = -S (-w) (π - v)
  support : ∀ s w v : ℝ, (∀ k : ℤ, (9 / 10) * w₀ ≤ |w - 4 * (k : ℝ)|) → F s w v = S w v
  ball : ∀ s w v : ℝ, |w| ≤ w₀ → nsq (F s w v) < (w₀ + ε) ^ 2
  nearBase : ∀ s w v : ℝ, |w| ≤ 1 → √(nsq (F s w v - Bfam w₀ s w v)) ≤ ε

section Eversion

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

theorem sgn_add (a b : ℤ) : sgn (a + b) = sgn a * sgn b := by
  unfold sgn
  by_cases ha : Even a <;> by_cases hb : Even b <;> simp [Int.even_add, ha, hb]

theorem sgn_sub_mul (a b : ℤ) : sgn (a - b) * sgn b = sgn a := by
  rw [← sgn_add, sub_add_cancel]

theorem kk_sub_int (w : ℝ) (k : ℤ) : kk (w - 4 * k) = kk w - k := by
  simp only [kk]
  have e : (w - 4 * k + 1) / 4 = (w + 1) / 4 - k := by ring
  rw [e, Int.floor_sub_intCast]

/-- Ŝ の Γ 不変性（一般の k）。 -/
theorem Shat_shift (w v : ℝ) (k : ℤ) : Shat w₀ (w - 4 * k) (sgn k * v) = Shat w₀ w v := by
  simp only [Shat, kk_sub_int]
  rw [← mul_assoc, sgn_sub_mul]
  congr 1
  push_cast
  ring

/-- 首の帯の上の裏返し：h 原理の出力 f と座標 expU の合成。 -/
def Fneck (f : ℝ → U → V3) (s w v : ℝ) : V3 := f s (expU (w, v))

/-- Γ で被覆平面へ延ばした裏返し F(s, w, v) = Fneck(s, w − 4k, (−1)ᵏ v)。 -/
def Fev (f : ℝ → U → V3) (s w v : ℝ) : V3 := Fneck f s (w - 4 * (kk w : ℝ)) (sgn (kk w) * v)

variable {f : ℝ → U → V3}
  (hsm : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3) ∞ (uncurry f))
  (himm : ∀ s y, Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f s) y))
  (hfix : ∀ s (y : U), (s ≤ 0 ∨ 1 ≤ s ∨ w₀ * (9 / 10) ≤ |(logArg (y : ℝ × ℝ)).1|) →
    f s y = BfamP w₀ s y)

include hfix in
theorem Fneck_eq_Bfam {s w : ℝ} (h : s ≤ 0 ∨ 1 ≤ s ∨ w₀ * (9 / 10) ≤ |w|) (v : ℝ) :
    Fneck f s w v = Bfam w₀ s w v := by
  have h' : s ≤ 0 ∨ 1 ≤ s ∨ w₀ * (9 / 10) ≤ |(logArg ((expU (w, v) : U) : ℝ × ℝ)).1| := by
    rw [val_expU, logArg_expMap_fst]; exact h
  rw [Fneck, hfix s _ h', val_expU, BfamP_expMap]

include h0 h1 hfix in
theorem Fneck_eq_Shat {s w : ℝ} (hw : w₀ * (9 / 10) ≤ |w|) (v : ℝ) : Fneck f s w v = Shat w₀ w v := by
  rw [Fneck_eq_Bfam hfix (Or.inr (Or.inr hw)), Bfam_eq_Shat h0 h1 (by nlinarith)]

include hsm in
theorem contDiff_Fin : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Fneck f q.1 q.2.1 q.2.2) := by
  have hj : ContMDiff 𝓘(ℝ, ℝ × ℝ × ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) ∞
      (fun q : ℝ × ℝ × ℝ => ((q.1, expU (q.2.1, q.2.2)) : ℝ × U)) := by
    refine ContMDiff.prodMk ?_ ?_
    · exact (contDiff_fst (E := ℝ) (F := ℝ × ℝ)).contMDiff
    · exact contMDiff_expU.comp ((contDiff_fst.comp contDiff_snd).prodMk
        (contDiff_snd.comp contDiff_snd)).contMDiff
  have h := (hsm.comp hj).contDiff
  exact h

theorem Fneck_periodic (f : ℝ → U → V3) (s w v : ℝ) :
    Fneck f s w (v + 2 * π) = Fneck f s w v := by
  show f s (expU (w, v + 2 * π)) = f s (expU (w, v))
  congr 1
  exact Subtype.ext (by simp [val_expU, expMap])

include hsm himm in
theorem Fneck_immersion (s : ℝ) (p : ℝ × ℝ) :
    Injective (fderiv ℝ (fun p : ℝ × ℝ => Fneck f s p.1 p.2) p) := by
  have hfs : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (f s) :=
    hsm.comp (contMDiff_const.prodMk contMDiff_id)
  have hg : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f s) (expU p) :=
    hfs.mdifferentiableAt (by simp)
  have hexp : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p :=
    contMDiff_expU.mdifferentiableAt (by simp)
  have hchain : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Fneck f s p.1 p.2) p =
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f s) (expU p)).comp
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p) :=
    mfderiv_comp p hg hexp
  intro ξ η h
  have e1 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Fneck f s p.1 p.2) p ξ =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f s) (expU p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p ξ) := congrArg (fun L => L ξ) hchain
  have e2 : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Fneck f s p.1 p.2) p η =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f s) (expU p)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) expU p η) := congrArg (fun L => L η) hchain
  have h' : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Fneck f s p.1 p.2) p ξ =
      mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun p : ℝ × ℝ => Fneck f s p.1 p.2) p η :=
    (mf_eq' _ p ξ).trans (h.trans (mf_eq' _ p η).symm)
  rw [e1, e2] at h'
  exact mfderiv_expU_injective p (himm s (expU p) h')

include h0 h1 hfix in
/-- 帯 (4k − 2, 4k + 3) の上で F は Fneck∘（アフィン写像）に一致する。 -/
theorem Fev_eq_of {k : ℤ} {w : ℝ} (hw1 : 4 * (k : ℝ) - 2 < w) (hw2 : w < 4 * k + 3) (s v : ℝ) :
    Fev f s w v = Fneck f s (w - 4 * (k : ℝ)) (sgn k * v) := by
  by_cases hk : 4 * (k : ℝ) - 1 ≤ w
  · have e : kk w = k := kk_eq_iff.mpr ⟨hk, hw2⟩
    simp only [Fev, e]
  · push Not at hk
    have e : kk w = k - 1 := by
      rw [kk_eq_iff]; push_cast; constructor <;> linarith
    have hs : sgn (k - 1) = -sgn k := by
      have := sgn_succ (k - 1)
      rw [sub_add_cancel] at this
      rw [this]; ring
    simp only [Fev, e, hs]
    have h9 : w₀ * (9 / 10) ≤ |w - 4 * ((k - 1 : ℤ) : ℝ)| := by
      push_cast
      rw [abs_of_pos (by linarith)]
      linarith
    have h9' : w₀ * (9 / 10) ≤ |w - 4 * (k : ℝ)| := by
      rw [abs_of_neg (by linarith)]
      linarith
    rw [Fneck_eq_Shat h0 h1 hfix h9, Fneck_eq_Shat h0 h1 hfix h9']
    have e2 : w - 4 * ((k - 1 : ℤ) : ℝ) = (w - 4 * (k : ℝ)) + 4 := by push_cast; ring
    rw [e2, neg_mul, Shat_glide]

include h0 h1 hfix in
theorem Fev_eventually (q : ℝ × ℝ × ℝ) :
    (fun q : ℝ × ℝ × ℝ => Fev f q.1 q.2.1 q.2.2) =ᶠ[𝓝 q]
      fun q' => Fneck f q'.1 (q'.2.1 - 4 * (kk q.2.1 : ℝ)) (sgn (kk q.2.1) * q'.2.2) := by
  set k := kk q.2.1 with hk
  have hq := kk_eq_iff.mp hk.symm
  have hopen : IsOpen {q' : ℝ × ℝ × ℝ | 4 * (k : ℝ) - 2 < q'.2.1 ∧ q'.2.1 < 4 * k + 3} :=
    (isOpen_lt continuous_const (continuous_fst.comp continuous_snd)).inter
      (isOpen_lt (continuous_fst.comp continuous_snd) continuous_const)
  have hmem : q ∈ {q' : ℝ × ℝ × ℝ | 4 * (k : ℝ) - 2 < q'.2.1 ∧ q'.2.1 < 4 * k + 3} :=
    ⟨by linarith [hq.1], hq.2⟩
  filter_upwards [hopen.mem_nhds hmem] with q' hq'
  exact Fev_eq_of h0 h1 hfix hq'.1 hq'.2 q'.1 q'.2.2

include h0 h1 hsm hfix in
theorem contDiff_Fev : ContDiff ℝ ∞ (fun q : ℝ × ℝ × ℝ => Fev f q.1 q.2.1 q.2.2) := by
  refine contDiff_iff_contDiffAt.mpr fun q => ?_
  refine ContDiffAt.congr_of_eventuallyEq ?_ (Fev_eventually h0 h1 hfix q)
  have hA : ContDiff ℝ ∞ (fun q' : ℝ × ℝ × ℝ =>
      ((q'.1, q'.2.1 - 4 * (kk q.2.1 : ℝ), sgn (kk q.2.1) * q'.2.2) : ℝ × ℝ × ℝ)) := by
    fun_prop
  have h := (contDiff_Fin hsm).comp hA
  exact h.contDiffAt

theorem fderiv_affine_apply (c s : ℝ) (p ξ : ℝ × ℝ) :
    fderiv ℝ (fun p : ℝ × ℝ => ((p.1 - c, s * p.2) : ℝ × ℝ)) p ξ = (ξ.1, s * ξ.2) := by
  obtain ⟨w, v⟩ := p
  have hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => ((p.1 - c, s * p.2) : ℝ × ℝ)) (w, v) := by
    fun_prop
  have hw : HasDerivAt (fun w : ℝ => ((w - c, s * v) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) w :=
    ((hasDerivAt_id w).sub_const c).prodMk (hasDerivAt_const w (s * v))
  have hv : HasDerivAt (fun v : ℝ => ((w - c, s * v) : ℝ × ℝ)) ((0 : ℝ), s) v := by
    refine (hasDerivAt_const v (w - c)).prodMk ?_
    simpa using (hasDerivAt_id v).const_mul s
  rw [fderiv_apply_of_partials_gen hd hw hv]
  ext <;> simp [mul_comm]

include h0 h1 hsm himm hfix in
theorem Fev_immersion (s : ℝ) (p : ℝ × ℝ) :
    Injective (fderiv ℝ (fun p : ℝ × ℝ => Fev f s p.1 p.2) p) := by
  set k := kk p.1 with hk
  have hq := kk_eq_iff.mp hk.symm
  have hopen : IsOpen {p' : ℝ × ℝ | 4 * (k : ℝ) - 2 < p'.1 ∧ p'.1 < 4 * k + 3} :=
    (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_const)
  have hmem : p ∈ {p' : ℝ × ℝ | 4 * (k : ℝ) - 2 < p'.1 ∧ p'.1 < 4 * k + 3} :=
    ⟨by linarith [hq.1], hq.2⟩
  have e : (fun p : ℝ × ℝ => Fev f s p.1 p.2) =ᶠ[𝓝 p]
      fun p' => Fneck f s (p'.1 - 4 * (k : ℝ)) (sgn k * p'.2) := by
    filter_upwards [hopen.mem_nhds hmem] with p' hp'
    exact Fev_eq_of h0 h1 hfix hp'.1 hp'.2 s p'.2
  rw [e.fderiv_eq]
  have hA : Differentiable ℝ (fun p : ℝ × ℝ => ((p.1 - 4 * (k : ℝ), sgn k * p.2) : ℝ × ℝ)) := by
    fun_prop
  have hF : Differentiable ℝ (fun p : ℝ × ℝ => Fneck f s p.1 p.2) := by
    have h := (contDiff_Fin hsm).comp
      ((contDiff_const (c := s)).prodMk (contDiff_id (E := ℝ × ℝ)))
    exact h.differentiable (by simp)
  have hcomp : (fun p' : ℝ × ℝ => Fneck f s (p'.1 - 4 * (k : ℝ)) (sgn k * p'.2)) =
      (fun p : ℝ × ℝ => Fneck f s p.1 p.2) ∘ fun p : ℝ × ℝ => ((p.1 - 4 * (k : ℝ), sgn k * p.2) : ℝ × ℝ) :=
    rfl
  rw [hcomp, fderiv_comp p (hF _) (hA p)]
  intro ξ η h
  simp only [ContinuousLinearMap.comp_apply] at h
  have h2 := Fneck_immersion hsm himm s _ h
  rw [fderiv_affine_apply, fderiv_affine_apply] at h2
  have hs0 : sgn k ≠ 0 := by
    rcases sgn_eq k with h | h <;> rw [h] <;> norm_num
  rw [Prod.mk.injEq] at h2
  obtain ⟨e1, e2⟩ := h2
  exact Prod.ext e1 (mul_left_cancel₀ hs0 e2)

theorem Fev_periodic (f : ℝ → U → V3) (s w v : ℝ) : Fev f s w (v + 2 * π) = Fev f s w v := by
  simp only [Fev]
  rcases sgn_eq (kk w) with h | h
  · rw [h, one_mul, one_mul, Fneck_periodic]
  · rw [h, neg_one_mul, neg_one_mul, neg_add]
    have := Fneck_periodic f s (w - 4 * (kk w : ℝ)) (-v + -(2 * π))
    rw [neg_add_cancel_right] at this
    exact this.symm

theorem Fev_glide (f : ℝ → U → V3) (s w v : ℝ) : Fev f s (w + 4) (-v) = Fev f s w v := by
  simp only [Fev, kk_add_four, sgn_succ]
  congr 1
  · push_cast; ring
  · ring

include h0 h1 hfix in
theorem Fev_start {s : ℝ} (hs : s ≤ 0) (w v : ℝ) : Fev f s w v = Shat w₀ w v := by
  rw [Fev, Fneck_eq_Bfam hfix (Or.inl hs), Bfam_of_le h0 h1 (by linarith), Shat_shift]

include h0 h1 hfix in
theorem Fev_finish {s : ℝ} (hs : 1 ≤ s) {w : ℝ} (hw : |w| ≤ 1) (v : ℝ) :
    Fev f s w v = -Shat w₀ (-w) (π - v) := by
  have hk : kk w = 0 := kk_of_mem (by linarith [(abs_le.mp hw).1]) (by linarith [(abs_le.mp hw).2])
  simp only [Fev, hk, sgn_zero, Int.cast_zero, mul_zero, sub_zero, one_mul]
  rw [Fneck_eq_Bfam hfix (Or.inr (Or.inl hs)), Bfam_of_ge_neck (by linarith) hw,
    Shat_neck h0 h1 (by rwa [abs_neg])]

include h0 h1 hfix in
theorem Fev_support {w : ℝ} (hw : ∀ k : ℤ, (9 / 10) * w₀ ≤ |w - 4 * (k : ℝ)|) (s v : ℝ) :
    Fev f s w v = Shat w₀ w v := by
  rw [Fev, Fneck_eq_Shat h0 h1 hfix (by have := hw (kk w); linarith), Shat_shift]

theorem Fev_neck {w : ℝ} (hw : |w| ≤ 1) (s v : ℝ) : Fev f s w v = Fneck f s w v := by
  have hk : kk w = 0 := kk_of_mem (by linarith [(abs_le.mp hw).1]) (by linarith [(abs_le.mp hw).2])
  simp only [Fev, hk, sgn_zero, Int.cast_zero, mul_zero, sub_zero, one_mul]

end Eversion

section Main

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
/-- **首の裏返しの存在**（第 3 版 §2.7 の `neck_eversion`）。 -/
theorem neck_eversion {ε : ℝ} (hε : 0 < ε) : ∃ F, NeckEversion w₀ ε (Shat w₀) F := by
  obtain ⟨f, hsm, himm, hfix, hdist⟩ := klein_hprinciple h0 h1 (ε := ε / 2) (by positivity)
  refine ⟨Fev f, ?_, ?_, Fev_periodic f, Fev_glide f, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_Fev h0 h1 hsm hfix
  · exact fun s p => Fev_immersion h0 h1 hsm himm hfix s p
  · exact fun s w v hs => Fev_start h0 h1 hfix hs w v
  · exact fun s w v hs hw => Fev_finish h0 h1 hfix hs hw v
  · exact fun s w v hw => Fev_support h0 h1 hfix hw s v
  · intro s w v hw
    have hw1 : |w| ≤ 1 := hw.trans h1.le
    rw [Fev_neck hw1]
    have hd := hdist s (expU (w, v))
    rw [val_expU, BfamP_expMap] at hd
    have hnear : en (Fneck f s w v - Bfam w₀ s w v) ≤ 2 * (ε / 2) :=
      en_le_of_dist_le (by positivity) hd
    have hB : nsq (Bfam w₀ s w v) < w₀ ^ 2 := nsq_Bfam_lt h0 hw h1.le s v
    have hBe : en (Bfam w₀ s w v) < w₀ := by
      have := en_sq (Bfam w₀ s w v)
      nlinarith [en_nonneg (Bfam w₀ s w v)]
    have htri := en_sub_en_le (Fneck f s w v) (Bfam w₀ s w v)
    have hlt : en (Fneck f s w v) < w₀ + ε := by linarith
    have := en_sq (Fneck f s w v)
    nlinarith [en_nonneg (Fneck f s w v)]
  · intro s w v hw
    rw [Fev_neck hw]
    have hd := hdist s (expU (w, v))
    rw [val_expU, BfamP_expMap] at hd
    have := en_le_of_dist_le (by positivity) hd
    simp only [en] at this
    show √(nsq (f s (expU (w, v)) - Bfam w₀ s w v)) ≤ ε
    linarith

end Main

end Zeno.Smale
