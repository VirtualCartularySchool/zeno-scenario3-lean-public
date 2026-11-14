/-
# ZenoSmale.Basic : 定理 C4（【仮定】2 を球面そのもので扱う）

1. `IsEversion`：`theorem Smale` の結論をそのまま束ねた述語。
2. 端点の作用：f₁ = −f₀ から `Everse`（(q, n) ↦ (−q, n)）が出る。
3. δ で近いスメール：`sphere_eversion` の証明で捨てられていた近さの項を残す。
4. 一点では起きない：定値写像ははめ込みでない。だから「℘ において」は近似でしか読めない。
5. 中間値の定理：t ↦ ⟨f_t x, n_t x⟩ は連続で、符号を変えるので途中で 0 になる。
-/
import SphereEversion.Main
import Zeno.Side

noncomputable section

namespace Zeno.Smale

open Metric Module Set Function Filter ContinuousLinearMap
open scoped Manifold Topology

open Zeno.Model (Everse)

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ### 1. スメールの族 -/

/-- `theorem Smale` の結論。 -/
structure IsEversion (f : ℝ → 𝕊² → ℝ³) : Prop where
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ∞ ↿f
  start : f 0 = fun x : 𝕊² ↦ (x : ℝ³)
  finish : f 1 = fun x : 𝕊² ↦ -(x : ℝ³)
  regular : ∀ t, Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (f t) ∞

theorem exists_isEversion : ∃ f, IsEversion f := by
  obtain ⟨f, h1, h2, h3, h4⟩ := Smale
  exact ⟨f, h1, h2, h3, h4⟩

/-! ### 2. 外積・行列式・枠 -/

/-- 外積（座標） -/
def crs (b c : ℝ³) : ℝ³ :=
  !₂[b 1 * c 2 - b 2 * c 1, b 2 * c 0 - b 0 * c 2, b 0 * c 1 - b 1 * c 0]

/-- 枠の対 ⟨q, n⟩ -/
def pair3 (f : ℝ³ × ℝ³) : ℝ := inner ℝ f.1 f.2

theorem pair3_everse (f : ℝ³ × ℝ³) : pair3 (Everse f) = -pair3 f := by
  simp [pair3, Everse, inner_neg_left]

theorem crs_neg_neg (b c : ℝ³) : crs (-b) (-c) = crs b c := by
  ext i
  fin_cases i <;> simp [crs]

section Frames

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]

/-- 点 x での枠：位置と、二つの接ベクトルの像の外積（α の向きから決まる法線）。 -/
def framePt (F : M → ℝ³) (x : M) (b₀ b₁ : TangentSpace I x) : ℝ³ × ℝ³ :=
  (F x, crs (mfderiv I 𝓘(ℝ, ℝ³) F x b₀) (mfderiv I 𝓘(ℝ, ℝ³) F x b₁))

/-- 端点の作用：−F の枠は F の枠の `Everse` である。微分可能性は要らない。 -/
theorem framePt_neg (F : M → ℝ³) (x : M) (b₀ b₁ : TangentSpace I x) :
    framePt I (-F) x b₀ b₁ = Everse (framePt I F x b₀ b₁) := by
  have h : mfderiv I 𝓘(ℝ, ℝ³) (-F) x = -mfderiv I 𝓘(ℝ, ℝ³) F x := mfderiv_neg
  simp only [framePt, Everse, Pi.neg_apply, h]
  congr 1
  exact crs_neg_neg _ _

end Frames

/-! ### 3. t について連続 -/

section Continuity

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- t ↦ D(f t)(x)(b) は連続である。 -/
theorem continuous_mfderiv_apply {f : ℝ → M → ℝ³}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ³) ∞ ↿f) (x : M) (b : TangentSpace I x) :
    Continuous fun t => mfderiv I 𝓘(ℝ, ℝ³) (f t) x b := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have h := ContMDiffAt.mfderiv (m := 0) (n := ∞) (J := 𝓘(ℝ, ℝ)) (I := I) (I' := 𝓘(ℝ, ℝ³))
    (x₀ := t₀) f (fun _ => x) (hf (t₀, x)) contMDiffAt_const (by simp)
  have hc := h.continuousAt
  have hEq : (fun t => inTangentCoordinates I 𝓘(ℝ, ℝ³) (fun _ => x) (fun t => f t x)
        (fun t => mfderiv I 𝓘(ℝ, ℝ³) (f t) x) t₀ t) =
      fun t => mfderiv I 𝓘(ℝ, ℝ³) (f t) x := by
    funext t
    rw [inTangentCoordinates_eq (fun _ => x) (fun t => f t x) _ (mem_chart_source _ x) (mem_univ _)]
    refine ContinuousLinearMap.ext fun v => ?_
    simp only [ContinuousLinearMap.comp_apply, tangentBundleCore_coordChange_model_space]
    have hself := (tangentBundleCore I M).coordChange_self (achart HM x) x (mem_chart_source HM x) v
    have hL : ∀ L : TangentSpace I x →L[ℝ] TangentSpace 𝓘(ℝ, ℝ³) (f t x),
        L ((tangentBundleCore I M).coordChange (achart HM x) (achart HM x) x v) = L v :=
      fun L => congrArg (fun z : TangentSpace I x => L z) hself
    exact hL _
  let L : ℝ → (EM →L[ℝ] ℝ³) := fun t => mfderiv I 𝓘(ℝ, ℝ³) (f t) x
  have hc' : ContinuousAt L t₀ :=
    ContinuousAt.congr hc (Filter.Eventually.of_forall fun t => congrFun hEq t)
  exact hc'.clm_apply (continuousAt_const (y := (b : EM)))

/-- 外積は連続である。 -/
theorem continuous_crs {g h : ℝ → ℝ³} (hg : Continuous g) (hh : Continuous h) :
    Continuous fun t => crs (g t) (h t) := by
  have coord : ∀ {k : ℝ → ℝ³}, Continuous k → ∀ i, Continuous fun t => k t i := by
    intro k hk i
    exact (PiLp.continuous_apply 2 _ i).comp hk
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · change Continuous fun t => g t 1 * h t 2 - g t 2 * h t 1
    exact ((coord hg 1).mul (coord hh 2)).sub ((coord hg 2).mul (coord hh 1))
  · change Continuous fun t => g t 2 * h t 0 - g t 0 * h t 2
    exact ((coord hg 2).mul (coord hh 0)).sub ((coord hg 0).mul (coord hh 2))
  · change Continuous fun t => g t 0 * h t 1 - g t 1 * h t 0
    exact ((coord hg 0).mul (coord hh 1)).sub ((coord hg 1).mul (coord hh 0))

/-- t ↦ ⟨f_t x, n_t x⟩ は連続である。 -/
theorem continuous_pair3 {f : ℝ → M → ℝ³}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ³) ∞ ↿f) (x : M) (b₀ b₁ : TangentSpace I x) :
    Continuous fun t => pair3 (framePt I (f t) x b₀ b₁) := by
  have h0 := continuous_mfderiv_apply hf x b₀
  have h1 := continuous_mfderiv_apply hf x b₁
  have hp : Continuous fun t => f t x := by
    have : Continuous fun t : ℝ => (↿f) (t, x) :=
      hf.continuous.comp (continuous_id.prodMk continuous_const)
    exact this
  exact hp.inner (continuous_crs h0 h1)

/-- C.f. 中間値の定理：符号が変われば途中に ⟨f_t x, n_t x⟩ = 0 の時刻がある。 -/
theorem ivt_pair3 {f : ℝ → M → ℝ³}
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ³) ∞ ↿f) (x : M) (b₀ b₁ : TangentSpace I x)
    (h0 : pair3 (framePt I (f 0) x b₀ b₁) ≠ 0)
    (h1 : pair3 (framePt I (f 1) x b₀ b₁) = -pair3 (framePt I (f 0) x b₀ b₁)) :
    ∃ t ∈ Ioo (0 : ℝ) 1, pair3 (framePt I (f t) x b₀ b₁) = 0 := by
  have hc := (continuous_pair3 hf x b₀ b₁).continuousOn (s := Icc (0 : ℝ) 1)
  have key : ∃ t ∈ Icc (0 : ℝ) 1, pair3 (framePt I (f t) x b₀ b₁) = 0 := by
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hmem : (0 : ℝ) ∈ Icc (pair3 (framePt I (f 0) x b₀ b₁)) (pair3 (framePt I (f 1) x b₀ b₁)) :=
        ⟨hneg.le, by rw [h1]; linarith⟩
      obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc zero_le_one hc hmem
      exact ⟨t, ht, ht0⟩
    · have hmem : (0 : ℝ) ∈ Icc (pair3 (framePt I (f 1) x b₀ b₁)) (pair3 (framePt I (f 0) x b₀ b₁)) :=
        ⟨by rw [h1]; linarith, hpos.le⟩
      obtain ⟨t, ht, ht0⟩ := intermediate_value_Icc' zero_le_one hc hmem
      exact ⟨t, ht, ht0⟩
  obtain ⟨t, ht, ht0⟩ := key
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, ht0⟩
  · rintro rfl; exact h0 ht0
  · rintro rfl
    rw [h1, neg_eq_zero] at ht0
    exact h0 ht0

end Continuity

/-! ### 4. 外積と内積の座標 -/

theorem inner_eq (a b : ℝ³) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply, conj_trivial]
  ring

/-- ラグランジュの恒等式の形：x ⟂ u, v なら ⟨x, u × v⟩² = |x|²|u × v|²。 -/
theorem inner_crs_sq {x u v : ℝ³} (h1 : inner ℝ x u = 0) (h2 : inner ℝ x v = 0) :
    inner ℝ x (crs u v) ^ 2 = inner ℝ x x * inner ℝ (crs u v) (crs u v) := by
  rw [inner_eq] at h1 h2
  simp only [inner_eq, crs]
  simp
  have e1 := h1
  have e2 := h2
  -- x × (u × v) = u⟨x, v⟩ − v⟨x, u⟩ = 0 の三成分
  have c0 : x 1 * (u 0 * v 1 - u 1 * v 0) - x 2 * (u 2 * v 0 - u 0 * v 2) = 0 := by
    linear_combination (u 0) * e2 - (v 0) * e1
  have c1 : x 2 * (u 1 * v 2 - u 2 * v 1) - x 0 * (u 0 * v 1 - u 1 * v 0) = 0 := by
    linear_combination (u 1) * e2 - (v 1) * e1
  have c2 : x 0 * (u 2 * v 0 - u 0 * v 2) - x 1 * (u 1 * v 2 - u 2 * v 1) = 0 := by
    linear_combination (u 2) * e2 - (v 2) * e1
  linear_combination
    (-(x 1 * (u 0 * v 1 - u 1 * v 0) - x 2 * (u 2 * v 0 - u 0 * v 2))) * c0
    - (x 2 * (u 1 * v 2 - u 2 * v 1) - x 0 * (u 0 * v 1 - u 1 * v 0)) * c1
    - (x 0 * (u 2 * v 0 - u 0 * v 2) - x 1 * (u 1 * v 2 - u 2 * v 1)) * c2

/-- u × v = 0 なら (u·u) v = (u·v) u。 -/
theorem crs_eq_zero_imp {u v : ℝ³} (h : crs u v = 0) :
    (inner ℝ u u) • v = (inner ℝ u v) • u := by
  have c0 : u 1 * v 2 - u 2 * v 1 = 0 := by simpa [crs] using congrFun (congrArg (WithLp.ofLp) h) 0
  have c1 : u 2 * v 0 - u 0 * v 2 = 0 := by simpa [crs] using congrFun (congrArg (WithLp.ofLp) h) 1
  have c2 : u 0 * v 1 - u 1 * v 0 = 0 := by simpa [crs] using congrFun (congrArg (WithLp.ofLp) h) 2
  ext i
  simp only [inner_eq, PiLp.smul_apply, smul_eq_mul]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    linear_combination (-(u 1)) * c2 + (u 2) * c1
  · simp only [Fin.mk_one, Fin.isValue]
    linear_combination (u 0) * c2 - (u 2) * c0
  · simp only [Fin.reduceFinMk, Fin.isValue]
    linear_combination (-(u 0)) * c1 + (u 1) * c0

/-- 線形単射の像の外積は消えない。 -/
theorem crs_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (L : V →ₗ[ℝ] ℝ³)
    (hL : Injective L) {b₀ b₁ : V} (hb0 : b₀ ≠ 0) (hb : ∀ k : ℝ, b₁ ≠ k • b₀) :
    crs (L b₀) (L b₁) ≠ 0 := by
  intro h
  have h1 := crs_eq_zero_imp h
  have hu : L b₀ ≠ 0 := by
    intro h0
    exact hb0 (hL (by rw [h0, map_zero]))
  have huu : inner ℝ (L b₀) (L b₀) ≠ 0 := inner_self_ne_zero.mpr hu
  have h2 : L b₁ = L ((inner ℝ (L b₀) (L b₁) / inner ℝ (L b₀) (L b₀)) • b₀) := by
    rw [map_smul, div_eq_inv_mul, mul_smul, ← h1, smul_smul, inv_mul_cancel₀ huu, one_smul]
  exact hb _ (hL h2)

/-! ### 5. 球面の場合 -/

/-- 球面の接空間の二つの基底ベクトル。 -/
def e0 (x : 𝕊²) : TangentSpace (𝓡 2) x := (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))
def e1 (x : 𝕊²) : TangentSpace (𝓡 2) x := (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))

theorem e0_ne_zero (x : 𝕊²) : e0 x ≠ 0 := by
  intro h
  have h' : (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) = 0 := h
  have := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h'
  simp at this

theorem e1_ne_smul_e0 (x : 𝕊²) (k : ℝ) : e1 x ≠ k • e0 x := by
  intro h
  have h' : (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2)) =
      k • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) := h
  have h1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h'
  simp at h1

/-- 球面の包含 -/
abbrev incl : 𝕊² → ℝ³ := fun x => (x : ℝ³)

theorem inner_self_coe (x : 𝕊²) : inner ℝ (x : ℝ³) (x : ℝ³) = 1 := by
  have h : ‖(x : ℝ³)‖ = 1 := by simp
  rw [real_inner_self_eq_norm_sq, h]; norm_num

theorem inner_coe_mfderiv (x : 𝕊²) (b : TangentSpace (𝓡 2) x) :
    inner ℝ (x : ℝ³) (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) incl x b) = 0 := by
  have hrange := range_mvfderiv_subtypeVal (n := 2) x
  have hmem : (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) incl x b : ℝ³) ∈ (ℝ ∙ (x : ℝ³))ᗮ := by
    rw [← hrange]
    exact ⟨b, rfl⟩
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem

/-- 始点で ⟨q, n⟩ は消えない。 -/
theorem pair3_incl_ne (x : 𝕊²) : pair3 (framePt (𝓡 2) incl x (e0 x) (e1 x)) ≠ 0 := by
  have hu := inner_coe_mfderiv x (e0 x)
  have hv := inner_coe_mfderiv x (e1 x)
  have hsq := inner_crs_sq hu hv
  rw [inner_self_coe, one_mul] at hsq
  have hne : crs (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) incl x (e0 x)) (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) incl x (e1 x)) ≠ 0 :=
    crs_ne_zero (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) incl x).toLinearMap
      (injective_mvfderiv_subtypeVal_sphere x) (e0_ne_zero x) (e1_ne_smul_e0 x)
  have hpos : inner ℝ (crs (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) incl x (e0 x))
      (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) incl x (e1 x)))
      (crs (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) incl x (e0 x)) (mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) incl x (e1 x))) ≠ 0 :=
    inner_self_ne_zero.mpr hne
  intro h0
  unfold pair3 framePt at h0
  simp only at h0
  rw [h0] at hsq
  exact hpos (by simpa using hsq.symm)

/-- 【仮定】2 の内容（球面）：スメールの族の端点は枠に `Everse` として働き、⟨q, n⟩ の符号を反転し、
途中に ⟨q, n⟩ = 0 の時刻がある。 -/
theorem smale_endpoints {f : ℝ → 𝕊² → ℝ³} (hf : IsEversion f) (x : 𝕊²) :
    framePt (𝓡 2) (f 1) x (e0 x) (e1 x) = Everse (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) ∧
    pair3 (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) ≠ 0 ∧
    pair3 (framePt (𝓡 2) (f 1) x (e0 x) (e1 x)) = -pair3 (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) ∧
    ∃ t ∈ Ioo (0 : ℝ) 1, pair3 (framePt (𝓡 2) (f t) x (e0 x) (e1 x)) = 0 := by
  have hneg : f 1 = -f 0 := by
    rw [hf.start, hf.finish]; rfl
  have h1 : framePt (𝓡 2) (f 1) x (e0 x) (e1 x) = Everse (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) := by
    rw [hneg]; exact framePt_neg (𝓡 2) (f 0) x (e0 x) (e1 x)
  have h0 : pair3 (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) ≠ 0 := by
    rw [hf.start]; exact pair3_incl_ne x
  have h2 : pair3 (framePt (𝓡 2) (f 1) x (e0 x) (e1 x)) =
      -pair3 (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) := by
    rw [h1, pair3_everse]
  exact ⟨h1, h0, h2, ivt_pair3 hf.smooth x (e0 x) (e1 x) h0 h2⟩

/-! ### 6. 一点では起きない -/

/-- 定値写像ははめ込みでない。球面を文字どおり一点 ℘ に潰すことは正則でない。 -/
theorem not_immersion_const (q : ℝ³) : ¬ Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (fun _ : 𝕊² => q) ∞ := by
  intro h
  have hne : Nonempty 𝕊² := (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  obtain ⟨x⟩ := hne
  have hinj := h.diff_injective x
  rw [mfderiv_const] at hinj
  exact e0_ne_zero x (hinj (by simp))

/-! ### 7. δ で近いスメール -/

/-- `sphere_eversion` の証明で ε := δ とし、捨てられていた近さの項を残したもの。 -/
theorem sphere_eversion_close {δ : ℝ} (hδ : 0 < δ) :
    ∃ f : ℝ → 𝕊² → ℝ³, IsEversion f ∧
      ∀ t x, dist (f t x)
        ((1 - smoothStep t : ℝ) • (x : ℝ³) + (smoothStep t : ℝ) • (-(x : ℝ³))) ≤ δ := by
  classical
  let ω : Orientation ℝ ℝ³ (Fin 3) :=
    ((stdOrthonormalBasis _ _).reindex <|
          finCongr (Fact.out : finrank ℝ ℝ³ = 3)).toBasis.orientation
  have ineq_rank : finrank ℝ (EuclideanSpace ℝ (Fin 2)) < finrank ℝ ℝ³ := by simp
  let ε : 𝕊² → ℝ := fun _ ↦ δ
  have hε_pos : ∀ x, 0 < ε x := fun _ ↦ hδ
  have hε_cont : Continuous ε := continuous_const
  have : Nonempty (sphere 0 1 : Set ℝ³) :=
    (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  rcases (immersionRel_satisfiesHPrincipleWith (𝓡 2) 𝕊² 𝓘(ℝ, ℝ³) ℝ³ 𝓘(ℝ, ℝ) ℝ ineq_rank
          ((Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ) hε_pos
          hε_cont).bs
      (formalEversion ℝ³ ω) (formalEversion_hol_near_zero_one ℝ³ ω) with
    ⟨f, h₁, h₂, h₃, h₅⟩
  have := h₂.forall_mem principal_le_nhdsSet
  refine ⟨f, ⟨h₁, ?_, ?_, ?_⟩, ?_⟩
  · funext x
    rw [this (0, x) (by simp)]
    convert! formalEversion_zero ℝ³ ω x
  · funext x
    rw [this (1, x) (by simp)]
    convert! formalEversion_one ℝ³ ω x
  · exact fun t ↦ {
      contMDiff := h₁.uncurry_left 𝓘(ℝ, ℝ) (𝓡 2) 𝓘(ℝ, ℝ³) t
      diff_injective := h₅ t
    }
  · intro t x
    have h := h₃ t x
    rw [formalEversion_bs] at h
    exact h

/-- 動径の式：(1 − s)x + s(−x) = (1 − 2s)x。この符号つき半径が競走の差 w に当たる。 -/
theorem radial_collapse (s : ℝ) (x : ℝ³) : (1 - s) • x + s • (-x) = (1 - 2 * s) • x := by
  rw [smul_neg, sub_smul, sub_smul, one_smul, two_mul, add_smul]
  abel

/-! ### 8. 任意の近傍で起きる -/

/-- ℘ の任意の近傍の中で、半径 η/2 の球面が裏返る。枠の作用は `Everse` のままである。 -/
theorem eversion_in_ball {η : ℝ} (hη : 0 < η) :
    ∃ f : ℝ → 𝕊² → ℝ³,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ∞ ↿f ∧
      (f 0 = fun x : 𝕊² => (η / 2) • (x : ℝ³)) ∧
      (f 1 = -f 0) ∧
      (∀ t, Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (f t) ∞) ∧
      (∀ t x, ‖f t x‖ ≤ η) ∧
      ∀ x, framePt (𝓡 2) (f 1) x (e0 x) (e1 x) = Everse (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) := by
  obtain ⟨g, hg, hclose⟩ := sphere_eversion_close (δ := 1) one_pos
  set c : ℝ := η / 2 with hc
  have hcpos : 0 < c := by positivity
  let f : ℝ → 𝕊² → ℝ³ := fun t x => c • g t x
  have hf0 : f 0 = fun x : 𝕊² => (η / 2) • (x : ℝ³) := by
    funext x
    simp only [f, hg.start, hc]
  have hf1 : f 1 = -f 0 := by
    funext x
    simp only [f, hg.start, hg.finish, Pi.neg_apply, smul_neg]
  refine ⟨f, ?_, hf0, hf1, ?_, ?_, ?_⟩
  · have hsm : ContDiff ℝ ∞ (fun q : ℝ³ => c • q) := contDiff_const_smul c
    exact hsm.contMDiff.comp hg.smooth
  · intro t
    have him := hg.regular t
    have hsm : ContDiff ℝ ∞ (fun q : ℝ³ => c • q) := contDiff_const_smul c
    refine ⟨hsm.contMDiff.comp him.contMDiff, fun x => ?_⟩
    have hd : mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (f t) x = c • mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (g t) x :=
      ((him.contMDiff.mdifferentiableAt (by simp)).hasMFDerivAt.const_smul c).mfderiv
    rw [hd]
    intro a b hab
    have hab' : c • mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (g t) x a = c • mfderiv (𝓡 2) 𝓘(ℝ, ℝ³) (g t) x b := hab
    exact him.diff_injective x (smul_right_injective _ hcpos.ne' hab')
  · intro t x
    have h1 := hclose t x
    have hs := smoothStep.mem t
    have hr : ‖(1 - smoothStep t : ℝ) • (x : ℝ³) + (smoothStep t : ℝ) • (-(x : ℝ³))‖ ≤ 1 := by
      rw [radial_collapse, norm_smul]
      have hx : ‖(x : ℝ³)‖ = 1 := by simp
      rw [hx, mul_one, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2]
    have hg1 : ‖g t x‖ ≤ 2 := by
      have := norm_le_norm_add_norm_sub' (g t x)
        ((1 - smoothStep t : ℝ) • (x : ℝ³) + (smoothStep t : ℝ) • (-(x : ℝ³)))
      rw [dist_eq_norm] at h1
      linarith
    have hfn : ‖f t x‖ = c * ‖g t x‖ := by
      simp only [f, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [hfn]
    have h2 : c * ‖g t x‖ ≤ c * 2 := mul_le_mul_of_nonneg_left hg1 hcpos.le
    have h3 : c * 2 = η := by rw [hc]; ring
    linarith
  · intro x
    rw [hf1]
    exact framePt_neg (𝓡 2) (f 0) x (e0 x) (e1 x)

end Zeno.Smale
