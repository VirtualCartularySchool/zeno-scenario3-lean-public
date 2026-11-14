/-
# ZenoSmale.Mobius : 射影平面のはめ込み（読み M2 の面）

平面 α（§8 の γ：平らな中心とホーン）を射影平面に完備化し、無限遠直線のまわりを
芯の模型 C で閉じる。ホーンの端と芯の間は、明示的な形式解（`Zeno.Model.Lfull`）に
h 原理を適用して正則化する。得られる面 S は円柱の上の写像で、τ(w, v) = (−w, v + π) で
不変であり、法線は τ で反転する（一つの側しか持たない）。
-/
import SphereEversion.Main
import Zeno.Mobius
import ZenoSmale.Plane

noncomputable section

namespace Zeno.Smale

open Metric Module Set Function Filter ContinuousLinearMap
open scoped Manifold Topology
open Zeno.Model

local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {k δ w₀ : ℝ}

/-- 座標の埋め込み y ↦ (0, y)。形式微分を一つの線形写像の場へ載せるための台。 -/
def J0 : ℝ × ℝ →L[ℝ] V3 := (0 : ℝ × ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))

/-- 射影 q ↦ (q₂, q₃)。 -/
def P23 : V3 →L[ℝ] ℝ × ℝ := ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)

theorem P23_J0 (ξ : ℝ × ℝ) : P23 (J0 ξ) = ξ := rfl

theorem mf_J0_apply (x ξ : ℝ × ℝ) : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) J0 x ξ = J0 ξ :=
  (mf_eq J0 x ξ).trans (by rw [ContinuousLinearMap.fderiv])

set_option backward.isDefEq.respectTransparency false in
theorem formal_apply (x ξ : ℝ × ℝ) :
    (((Lfull k δ w₀ x).comp P23).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) J0 x)) ξ =
      Lfull k δ w₀ x ξ :=
  congrArg (fun z => Lfull k δ w₀ x (P23 z)) (mf_J0_apply x ξ)

theorem mobBs_smooth (hok : MobOK k δ w₀) :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3) ∞ fun p : ℝ × (ℝ × ℝ) ↦ bsM k δ w₀ p.2 :=
  (contDiff_bsM hok).contMDiff.comp contMDiff_snd

theorem mobL_smooth :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3 →L[ℝ] V3) ∞
      fun p : ℝ × (ℝ × ℝ) ↦ (Lfull k δ w₀ p.2).comp P23 :=
  ((contDiff_Lfull (k := k) (δ := δ) (w₀ := w₀)).clm_comp contDiff_const).contMDiff.comp
    contMDiff_snd

/-- 形式解の土台。 -/
def mobAux (hok : MobOK k δ w₀) :
    FamilyOneJetSec 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) 𝓘(ℝ, V3) V3 𝓘(ℝ, ℝ) ℝ :=
  familyJoin (mobBs_smooth hok) <|
    familyTwist (drop (oneJetExtSec ⟨J0, J0.contDiff.contMDiff⟩))
      (fun p : ℝ × (ℝ × ℝ) ↦ (Lfull k δ w₀ p.2).comp P23)
      (fun p => mobL_smooth p)

theorem mobSol_inj (hok : MobOK k δ w₀) (_t : ℝ) (x : ℝ × ℝ) :
    Injective (((Lfull k δ w₀ x).comp P23).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) J0 x)) := by
  have hfun : ⇑(((Lfull k δ w₀ x).comp P23).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) J0 x)) =
      ⇑(Lfull k δ w₀ x) := funext (formal_apply x)
  rw [hfun]
  exact Lfull_inj hok x

/-- 形式解。 -/
def mobSol (hok : MobOK k δ w₀) :
    HtpyFormalSol (immersionRel 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) 𝓘(ℝ, V3) V3) :=
  { mobAux hok with
    is_sol' := fun t x => mobSol_inj hok t x }

set_option backward.isDefEq.respectTransparency false in
theorem mobSol_hol (hok : MobOK k δ w₀) {p : ℝ × (ℝ × ℝ)}
    (hp : tau p.2 < mT0 w₀ + mDl δ w₀ ∨ mT0 w₀ + 4 * mDl δ w₀ < tau p.2) :
    (mobSol hok p.1).toOneJetSec.IsHolonomicAt p.2 := by
  change
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (fun y ↦ bsM k δ w₀ y) p.2 =
      ((Lfull k δ w₀ p.2).comp P23).comp (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) J0 p.2)
  refine ContinuousLinearMap.ext fun ξ => ?_
  exact (mf_eq (fun y => bsM k δ w₀ y) p.2 ξ).trans
    ((congrArg (fun L : ℝ × ℝ →L[ℝ] V3 => L ξ) (bsM_holonomic hok hp)).trans
      (formal_apply p.2 ξ).symm)

/-- 固定する閉集合：ホーンと平らな中心（|y|² ≤ 1/w₀²）と、芯の近く（|y|² ≥ 1/δ²）。 -/
def mobFixed (δ w₀ : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | tau p.2 ≤ mT0 w₀ ∨ mT0 w₀ + 5 * mDl δ w₀ ≤ tau p.2}

theorem isClosed_mobFixed (δ w₀ : ℝ) : IsClosed (mobFixed δ w₀) := by
  have hc : Continuous fun p : ℝ × (ℝ × ℝ) => tau p.2 := contDiff_tau.continuous.comp continuous_snd
  exact (isClosed_le hc continuous_const).union (isClosed_le continuous_const hc)

theorem mobSol_hol_near (hok : MobOK k δ w₀) :
    ∀ᶠ p : ℝ × (ℝ × ℝ) near mobFixed δ w₀, (mobSol hok p.1).toOneJetSec.IsHolonomicAt p.2 := by
  have hdl := hok.dl_pos
  have hc : Continuous fun p : ℝ × (ℝ × ℝ) => tau p.2 := contDiff_tau.continuous.comp continuous_snd
  have hopen : IsOpen {p : ℝ × (ℝ × ℝ) |
      tau p.2 < mT0 w₀ + mDl δ w₀ ∨ mT0 w₀ + 4 * mDl δ w₀ < tau p.2} :=
    (isOpen_lt hc continuous_const).union (isOpen_lt continuous_const hc)
  have hmem : {p : ℝ × (ℝ × ℝ) | tau p.2 < mT0 w₀ + mDl δ w₀ ∨
      mT0 w₀ + 4 * mDl δ w₀ < tau p.2} ∈ 𝓝ˢ (mobFixed δ w₀) := by
    refine hopen.mem_nhdsSet.mpr ?_
    rintro p (hp | hp)
    · left; linarith
    · right; linarith
  filter_upwards [hmem] with p hp
  exact mobSol_hol hok hp

/-- **定理（射影平面の平面部分）**。平面全体のはめ込み f で、ホーンと中心では γ、芯の近くでは
C∘y⁻¹ に等しく、至るところ基底の写像に ε で近いものがある。 -/
theorem mob_plane (hok : MobOK k δ w₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ × ℝ → V3,
      ContDiff ℝ ∞ f ∧
      (∀ y, Function.Injective (fderiv ℝ f y)) ∧
      (∀ y, (tau y ≤ mT0 w₀ ∨ mT0 w₀ + 5 * mDl δ w₀ ≤ tau y) → f y = bsM k δ w₀ y) ∧
      (∀ y, dist (f y) (bsM k δ w₀ y) ≤ ε) := by
  have ineq_rank : finrank ℝ (ℝ × ℝ) < finrank ℝ V3 := by simp
  rcases (immersionRel_satisfiesHPrincipleWith 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) 𝓘(ℝ, V3) V3 𝓘(ℝ, ℝ) ℝ
      ineq_rank (isClosed_mobFixed δ w₀) (ε := fun _ => ε) (fun _ => hε) continuous_const).bs
      (mobSol hok) (mobSol_hol_near hok) with ⟨f, h₁, h₂, h₃, h₅⟩
  have hfix := h₂.forall_mem principal_le_nhdsSet
  have hsm : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2) := by
    have hid : ContMDiff 𝓘(ℝ, ℝ × (ℝ × ℝ)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) ∞
        (fun p : ℝ × (ℝ × ℝ) => (p.1, p.2)) :=
      (contDiff_fst.contMDiff).prodMk (contDiff_snd.contMDiff)
    exact (h₁.comp hid).contDiff
  refine ⟨f 0, hsm.comp (contDiff_const.prodMk contDiff_id), ?_, ?_, ?_⟩
  · intro y
    have h : Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f 0) y) := h₅ 0 y
    have hfun : ⇑(mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (f 0) y) = ⇑(fderiv ℝ (f 0) y) :=
      funext (mf_eq (f 0) y)
    rw [hfun] at h
    exact h
  · intro y hy
    exact hfix (0, y) hy
  · intro y
    exact h₃ 0 y

end Zeno.Smale
