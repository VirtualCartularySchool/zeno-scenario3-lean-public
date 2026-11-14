/-
# ZenoSmale.Surface : 向きづけられた曲面の裏返し（C4 の機構）

sphere-eversion の形式的裏返しは、球面に固有の性質を使っていない。
使っているのは「はめ込み g と単位法線 n があり、接平面が n に直交する」ことだけである。
そこで、法線まわりの回転 rot(s, n(x)) で g を −g へ運ぶ形式解を作り、h 原理で正則化する。
-/
import ZenoSmale.Basic

noncomputable section

namespace Zeno.Smale

open Metric Module Set Function Filter ContinuousLinearMap
open scoped Manifold Topology

open Zeno.Model (Everse)

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Surface

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
  {HM : Type*} [TopologicalSpace HM] (I : ModelWithCorners ℝ EM HM)
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]

/-- 向きづけられたはめ込み：はめ込み g と滑らかな単位法線 n。 -/
structure FramedImmersion (g n : M → ℝ³) : Prop where
  g_smooth : ContMDiff I 𝓘(ℝ, ℝ³) ∞ g
  n_smooth : ContMDiff I 𝓘(ℝ, ℝ³) ∞ n
  g_inj : ∀ x, Injective (mfderiv I 𝓘(ℝ, ℝ³) g x)
  n_unit : ∀ x, ‖n x‖ = 1
  n_perp : ∀ x v, inner ℝ (n x) (mfderiv I 𝓘(ℝ, ℝ³) g x v) = 0

variable {I} {g n : M → ℝ³} (h : FramedImmersion I g n) (ω : Orientation ℝ ℝ³ (Fin 3))

omit [FiniteDimensional ℝ EM] [IsManifold I ∞ M] in
include h in
theorem surf_bs_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ³) ∞ fun p : ℝ × M ↦ (1 - p.1) • g p.2 + p.1 • -g p.2 := by
  have hΦ : ContDiff ℝ ∞ (fun y : ℝ × ℝ³ => (1 - y.1) • y.2 + y.1 • -y.2) := by
    fun_prop
  exact hΦ.contMDiff.comp (contMDiff_fst.prodMk_space (h.g_smooth.comp contMDiff_snd))

/-- 形式解の土台：底は (1 − s)g + s(−g)、微分は rot(s, n) ∘ Dg。 -/
def surfAux : FamilyOneJetSec I M 𝓘(ℝ, ℝ³) ℝ³ 𝓘(ℝ, ℝ) ℝ :=
  familyJoin (surf_bs_smooth h) <|
    familyTwist (drop (oneJetExtSec ⟨g, h.g_smooth⟩))
      (fun p : ℝ × M ↦ ω.rot (p.1, n p.2))
      (by
        intro p
        have : ContMDiffAt 𝓘(ℝ, ℝ × ℝ³) 𝓘(ℝ, ℝ³ →L[ℝ] ℝ³) ∞ ω.rot (p.1, n p.2) := by
          refine ((ω.contDiff_rot ?_).of_le le_top).contMDiffAt
          intro h0
          have := h.n_unit p.2
          simp only at h0
          rw [h0, norm_zero] at this
          exact zero_ne_one this
        apply this.comp p (f := fun (p : ℝ × M) ↦ (p.1, n p.2))
        apply contMDiff_fst.prodMk_space (h.n_smooth.comp contMDiff_snd))

/-- 形式解：回転は等長なので微分は単射のまま。 -/
def surfAux2 : HtpyFormalSol (immersionRel I M 𝓘(ℝ, ℝ³) ℝ³) :=
  { surfAux h ω with
    is_sol' := fun t x =>
      (ω.isometry_rot t ⟨n x, by simpa using h.n_unit x⟩).injective.comp (h.g_inj x) }

/-- 形式的な裏返し：時間を smoothStep で引き直す。 -/
def surfEversion : HtpyFormalSol (immersionRel I M 𝓘(ℝ, ℝ³) ℝ³) :=
  (surfAux2 h ω).reindex ⟨smoothStep, contMDiff_iff_contDiff.mpr smoothStep.smooth⟩

omit [FiniteDimensional ℝ EM] in
set_option backward.isDefEq.respectTransparency.types false in
theorem surfHolAtZero {t : ℝ} (ht : t < 1 / 4) :
    (surfEversion h ω t).toOneJetSec.IsHolonomic := by
  intro x
  change
    mfderiv I 𝓘(ℝ, ℝ³) (fun y : M ↦ ((1 : ℝ) - smoothStep t) • g y + smoothStep t • -g y) x =
      (ω.rot (smoothStep t, n x)).comp (mfderiv I 𝓘(ℝ, ℝ³) g x)
  simp_rw [smoothStep.of_lt ht, ω.rot_zero, ContinuousLinearMap.id_comp]
  congr with y
  simp [smoothStep.of_lt ht]

omit [FiniteDimensional ℝ EM] in
set_option backward.isDefEq.respectTransparency false in
theorem surfHolAtOne {t : ℝ} (ht : 3 / 4 < t) :
    (surfEversion h ω t).toOneJetSec.IsHolonomic := by
  intro x
  change
    mfderiv I 𝓘(ℝ, ℝ³) (fun y : M ↦ ((1 : ℝ) - smoothStep t) • g y + smoothStep t • -g y) x =
      (ω.rot (smoothStep t, n x)).comp (mfderiv I 𝓘(ℝ, ℝ³) g x)
  trans mfderiv I 𝓘(ℝ, ℝ³) (-g) x
  · congr 2 with y
    simp [smoothStep.of_gt ht]
  ext v
  erw [mfderiv_neg, ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.neg_apply,
    smoothStep.of_gt ht]
  rw [ω.rot_one]; · rfl
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (h.n_perp x v)

omit [FiniteDimensional ℝ EM] in
theorem surf_hol_near_zero_one :
    ∀ᶠ s : ℝ × M near {0, 1} ×ˢ univ, (surfEversion h ω s.1).toOneJetSec.IsHolonomicAt s.2 := by
  have : (Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4)) ×ˢ (univ : Set M) ∈ 𝓝ˢ (({0, 1} : Set ℝ) ×ˢ univ) := by
    refine ((isOpen_Iio.union isOpen_Ioi).prod isOpen_univ).mem_nhdsSet.mpr ?_
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    refine ⟨?_, mem_univ _⟩
    simp_rw [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · exact Or.inl (show (0 : ℝ) < 1 / 4 by norm_num)
    · exact Or.inr (show (3 / 4 : ℝ) < 1 by norm_num)
  filter_upwards [this]
  rintro ⟨t, x⟩ ⟨ht | ht, _hx⟩
  · exact surfHolAtZero h ω ht x
  · exact surfHolAtOne h ω ht x

end Surface

/-- **向きづけられた曲面の裏返し**。はめ込み g と −g は、放射状の潰れ (1 − 2s)g に ε で近い
正則ホモトピーで結ばれる。球面の場合が Smale の定理である。 -/
theorem surface_eversion
    {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
    {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners ℝ EM HM} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [Nonempty M]
    {g n : M → ℝ³} (h : FramedImmersion I g n) (hdim : finrank ℝ EM < 3)
    {ε : M → ℝ} (hε_pos : ∀ x, 0 < ε x) (hε_cont : Continuous ε) :
    ∃ f : ℝ → M → ℝ³,
      ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ³) ∞ ↿f ∧ f 0 = g ∧ f 1 = -g ∧
      (∀ t, Immersion I 𝓘(ℝ, ℝ³) (f t) ∞) ∧
      ∀ t x, dist (f t x) ((1 - smoothStep t : ℝ) • g x + (smoothStep t : ℝ) • (-g x)) ≤ ε x := by
  classical
  let ω : Orientation ℝ ℝ³ (Fin 3) :=
    ((stdOrthonormalBasis _ _).reindex <|
          finCongr (Fact.out : finrank ℝ ℝ³ = 3)).toBasis.orientation
  have ineq_rank : finrank ℝ EM < finrank ℝ ℝ³ := by simpa using hdim
  rcases (immersionRel_satisfiesHPrincipleWith I M 𝓘(ℝ, ℝ³) ℝ³ 𝓘(ℝ, ℝ) ℝ ineq_rank
          ((Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ) hε_pos
          hε_cont).bs
      (surfEversion h ω) (surf_hol_near_zero_one h ω) with
    ⟨f, h₁, h₂, h₃, h₅⟩
  have := h₂.forall_mem principal_le_nhdsSet
  refine ⟨f, h₁, ?_, ?_, ?_, ?_⟩
  · ext1 x
    rw [this (0, x) (by simp)]
    change (1 - smoothStep 0 : ℝ) • g x + (smoothStep 0 : ℝ) • (-g x) = g x
    simp [smoothStep.zero]
  · ext1 x
    rw [this (1, x) (by simp)]
    change (1 - smoothStep 1 : ℝ) • g x + (smoothStep 1 : ℝ) • (-g x) = (-g) x
    simp [smoothStep.one]
  · intro t
    have hsec : ContMDiff I 𝓘(ℝ, ℝ³) ∞ (f t) :=
      h₁.comp (contMDiff_const.prodMk contMDiff_id : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ fun x => (t, x))
    exact ⟨hsec, h₅ t⟩
  · intro t x
    exact h₃ t x

end Zeno.Smale
