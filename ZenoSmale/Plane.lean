/-
# ZenoSmale.Plane : 定理 C3（Smale–Hirsch による平面 α の裏返し）

形式解 L(s, y) ∘ dg_y を、端の時刻とホーンを固定したまま正則化する。
ホーンでは傘の明示式がそのまま残り、赤道の折り目だけが h 原理で取り除かれる。
-/
import SphereEversion.Main
import Zeno.Plane

noncomputable section

namespace Zeno.Smale

open Metric Module Set Function Filter ContinuousLinearMap
open scoped Manifold Topology
open Zeno.Model

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem mf_eq (f : ℝ × ℝ → V3) (x ξ : ℝ × ℝ) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) f x ξ = fderiv ℝ f x ξ := by
  rw [mfderiv_eq_fderiv]
  rfl

theorem bsP_smooth (κ₀ : ℝ) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3) ∞ fun p : ℝ × (ℝ × ℝ) ↦ bsP κ₀ p.1 p.2 :=
  (contDiff_bsP κ₀).contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)

/-- 形式解の土台。 -/
def planeAux (κ₀ : ℝ) : FamilyOneJetSec 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) 𝓘(ℝ, V3) V3 𝓘(ℝ, ℝ) ℝ :=
  familyJoin (bsP_smooth κ₀) <|
    familyTwist (drop (oneJetExtSec ⟨planeG, contDiff_planeG.contMDiff⟩))
      (fun p : ℝ × (ℝ × ℝ) ↦ LL κ₀ p)
      (by
        intro p
        exact ((contDiff_LL κ₀).contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)) p)

variable {κ₀ : ℝ}

theorem planeSol_inj (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1) (t : ℝ) (x : ℝ × ℝ) :
    Injective ((LL κ₀ (t, x)).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) planeG x)) := by
  have hinj := LL_inj h0 h1 (t, x)
  have hmf : ∀ ξ : ℝ × ℝ, (LL κ₀ (t, x)).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) planeG x) ξ =
      (LL κ₀ (t, x)).comp (fderiv ℝ planeG x) ξ := fun ξ =>
    congrArg (LL κ₀ (t, x)) (mf_eq planeG x ξ)
  have hfun : ⇑((LL κ₀ (t, x)).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) planeG x)) =
      ⇑((LL κ₀ (t, x)).comp (fderiv ℝ planeG x)) := funext hmf
  rw [hfun]
  exact hinj

/-- 形式解。 -/
def planeSol (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1) :
    HtpyFormalSol (immersionRel 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) 𝓘(ℝ, V3) V3) :=
  { planeAux κ₀ with
    is_sol' := fun t x => planeSol_inj h0 h1 t x }

set_option backward.isDefEq.respectTransparency false in
theorem planeSol_hol (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1) {p : ℝ × (ℝ × ℝ)}
    (hp : p.1 < 1 / 4 ∨ 3 / 4 < p.1 ∨ 9 / 10 < tau p.2) :
    (planeSol h0 h1 p.1).toOneJetSec.IsHolonomicAt p.2 := by
  change
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun y ↦ bsP κ₀ p.1 y) p.2 =
      (LL κ₀ p).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) planeG p.2)
  refine ContinuousLinearMap.ext fun ξ => ?_
  have e := congrArg (fun L => L ξ) (hol_identity κ₀ hp)
  change mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (bsP κ₀ p.1) p.2 ξ =
    LL κ₀ p (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) planeG p.2 ξ)
  rw [mf_eq, mf_eq]
  exact e

/-- 固定する閉集合：端の時刻とホーン。 -/
def fixedSet : Set (ℝ × (ℝ × ℝ)) := {p | p.1 ≤ 0 ∨ 1 ≤ p.1 ∨ 1 ≤ tau p.2}

theorem isClosed_fixedSet : IsClosed fixedSet := by
  have h1 : IsClosed {p : ℝ × (ℝ × ℝ) | p.1 ≤ 0} := isClosed_le continuous_fst continuous_const
  have h2 : IsClosed {p : ℝ × (ℝ × ℝ) | 1 ≤ p.1} := isClosed_le continuous_const continuous_fst
  have h3 : IsClosed {p : ℝ × (ℝ × ℝ) | 1 ≤ tau p.2} :=
    isClosed_le continuous_const (contDiff_tau.continuous.comp continuous_snd)
  exact h1.union (h2.union h3)

theorem planeSol_hol_near (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1) :
    ∀ᶠ p : ℝ × (ℝ × ℝ) near fixedSet, (planeSol h0 h1 p.1).toOneJetSec.IsHolonomicAt p.2 := by
  have hopen : IsOpen {p : ℝ × (ℝ × ℝ) | p.1 < 1 / 4 ∨ 3 / 4 < p.1 ∨ 9 / 10 < tau p.2} := by
    have h1 : IsOpen {p : ℝ × (ℝ × ℝ) | p.1 < 1 / 4} := isOpen_lt continuous_fst continuous_const
    have h2 : IsOpen {p : ℝ × (ℝ × ℝ) | 3 / 4 < p.1} := isOpen_lt continuous_const continuous_fst
    have h3 : IsOpen {p : ℝ × (ℝ × ℝ) | 9 / 10 < tau p.2} :=
      isOpen_lt continuous_const (contDiff_tau.continuous.comp continuous_snd)
    exact h1.union (h2.union h3)
  have hmem : {p : ℝ × (ℝ × ℝ) | p.1 < 1 / 4 ∨ 3 / 4 < p.1 ∨ 9 / 10 < tau p.2} ∈ 𝓝ˢ fixedSet := by
    refine hopen.mem_nhdsSet.mpr ?_
    rintro p (hp | hp | hp)
    · left; linarith
    · right; left; linarith
    · right; right; linarith
  filter_upwards [hmem] with p hp
  exact planeSol_hol h0 h1 hp

/-- **定理 C3**。α 全体の正則ホモトピーで、端の時刻では g と −g、ホーンでは傘の明示式に等しく、
至るところ傘に ε で近い。 -/
theorem plane_eversion_rel_horn (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ × ℝ → V3,
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2) ∧
      (∀ s y, Function.Injective (fderiv ℝ (f s) y)) ∧
      (∀ s y, (s ≤ 0 ∨ 1 ≤ s ∨ 1 ≤ tau y) → f s y = bsP κ₀ s y) ∧
      (∀ s y, dist (f s y) (bsP κ₀ s y) ≤ ε) := by
  have ineq_rank : finrank ℝ (ℝ × ℝ) < finrank ℝ V3 := by simp
  rcases (immersionRel_satisfiesHPrincipleWith 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) 𝓘(ℝ, V3) V3 𝓘(ℝ, ℝ) ℝ
      ineq_rank isClosed_fixedSet (ε := fun _ => ε) (fun _ => hε) continuous_const).bs
      (planeSol h0 h1) (planeSol_hol_near h0 h1) with ⟨f, h₁, h₂, h₃, h₅⟩
  have hfix := h₂.forall_mem principal_le_nhdsSet
  have hsm : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2) := by
    have hid : ContMDiff 𝓘(ℝ, ℝ × (ℝ × ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) ∞
        (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2)) :=
      (contDiff_fst.contMDiff).prodMk (contDiff_snd.contMDiff)
    exact (h₁.comp hid).contDiff
  refine ⟨f, hsm, ?_, ?_, ?_⟩
  · intro s y
    have h : Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f s) y) := h₅ s y
    have hfun : ⇑(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f s) y) = ⇑(fderiv ℝ (f s) y) :=
      funext (mf_eq (f s) y)
    rw [hfun] at h
    exact h
  · intro s y hy
    exact hfix (s, y) hy
  · intro s y
    exact h₃ s y

end Zeno.Smale
