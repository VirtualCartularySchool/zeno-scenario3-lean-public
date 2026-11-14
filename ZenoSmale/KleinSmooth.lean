/-
# ZenoSmale.KleinSmooth : 商曲面 M = ℝ²/Γ の滑らかな構造と、はめ込み・正則ホモトピーの降下

`KleinQuotient` は M を位相空間として作った。本ファイルは、本文の命題 2.4 と命題 2.5 を形式化する。

1. **座標**。各点 p ∈ ℝ² について、被覆写像 π = `toM` の開球 B(p, 2) への制限は像の上への同相写像であり
   （`coverAt`）、その逆 φ_p = `chartM p` を M の座標とする。座標変換は局所的に Γ の元 γ_{k,m}
   （アフィン写像）に等しい（`chartM_toM_eq_gam`）。したがって M は、任意の滑らかさ n（∞ と ω を含む）
   について、ℝ² を模型とする境界のない多様体である。
2. **π は局所微分同相である**（`isLocalDiffeomorph_toM`）。とくに π は滑らかで、その微分は各点で
   線形同型である。
3. **降下**。Γ 不変な写像 f : ℝ² → ℝ³ について、f̄ ∘ π = f で決まる f̄ : M → ℝ³（`descend`）は、
   f が滑らかなら滑らかであり（`contMDiff_descend`。逆は `contDiff_of_contMDiff_descend`）、鎖律
   df̄(dπ ξ) = df ξ が成り立ち（`mfderiv_descend_apply`）、f̄ の π(p) での微分の像は f の p での微分の像に
   等しく（`mfderiv_descend_range`）、f̄ の微分が点 π(p) で単射であることと f の微分が p で単射である
   ことは同値である（`descend_immersion_iff`）。
4. **Ŝ と F の降下**。Ŝ_M（`ShatM`）は M の滑らかなはめ込みであり、首の裏返し F の降下
   (s, x) ↦ F̄_s(x)（`FM`）は ℝ × M の上で滑らかで、各段ははめ込みである。すなわち M の正則ホモトピー
   である（`RegularHomotopyOnM`、`FM_regularHomotopy`）。Mathlib の「微分の意味でのはめ込み」
   （`IsDiffImmersionAt`）の形も述べる。
5. **向きづけ不可能性**。Γ と両立する向き（ℝ² の上の連続で消えない関数 f で f ∘ γ_{k,m} = (−1)ᵏ f を
   満たすもの）は存在しない（`no_gam_orientation`）。
6. **閉じた曲面、平面との区別**。M はコンパクト、ハウスドルフ、連結、第二可算で、境界のない滑らかな
   多様体である（`kleinM_closed_surface`）。M は ℝ² と同相でない（`kleinM_not_homeomorph_plane`）。

一般の商多様体の理論は作らない。この M と、その座標、π、降下だけを扱う。
-/
import ZenoSmale.KleinQuotient
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ImmersionDiff

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff Manifold
open Zeno.Model

/-! ### 座標 -/

/-- 被覆写像の、開球 B(p, 2) の上への制限（像の上への同相写像）。 -/
def coverAt (p : ℝ × ℝ) : OpenPartialHomeomorph (ℝ × ℝ) KleinM :=
  OpenPartialHomeomorph.ofContinuousOpen
    (Set.InjOn.toPartialEquiv toM (ball p 2) (toM_injOn_ball p))
    continuous_toM.continuousOn isOpenMap_toM isOpen_ball

theorem coverAt_coe (p : ℝ × ℝ) : ⇑(coverAt p) = toM := rfl

theorem coverAt_source (p : ℝ × ℝ) : (coverAt p).source = ball p 2 := rfl

theorem coverAt_target (p : ℝ × ℝ) : (coverAt p).target = toM '' ball p 2 := rfl

/-- 座標 φ_p = (π|B(p, 2))⁻¹ : π(B(p, 2)) → B(p, 2)。 -/
def chartM (p : ℝ × ℝ) : OpenPartialHomeomorph KleinM (ℝ × ℝ) := (coverAt p).symm

theorem chartM_source (p : ℝ × ℝ) : (chartM p).source = toM '' ball p 2 := rfl

theorem chartM_target (p : ℝ × ℝ) : (chartM p).target = ball p 2 := rfl

theorem chartM_symm_coe (p : ℝ × ℝ) : ⇑(chartM p).symm = toM := rfl

/-- 座標は被覆写像の局所的な逆である。 -/
theorem chartM_toM {p u : ℝ × ℝ} (hu : u ∈ ball p 2) : chartM p (toM u) = u :=
  (coverAt p).left_inv hu

theorem toM_chartM {p : ℝ × ℝ} {x : KleinM} (hx : x ∈ toM '' ball p 2) :
    toM (chartM p x) = x :=
  (coverAt p).right_inv hx

theorem toM_mem_chartM_source (p : ℝ × ℝ) : toM p ∈ (chartM p).source :=
  ⟨p, mem_ball_self two_pos, rfl⟩

theorem isOpen_chartM_source (p : ℝ × ℝ) : IsOpen (toM '' ball p 2) :=
  isOpenMap_toM _ isOpen_ball

/-- **座標変換は Γ の元である**：π(u) が座標 φ_q の定義域に入れば、ある γ_{k,m} について γ_{k,m}(u) ∈ B(q, 2)
であり、φ_q(π(u)) = γ_{k,m}(u) である。 -/
theorem chartM_toM_eq_gam {q u : ℝ × ℝ} (h : toM u ∈ toM '' ball q 2) :
    ∃ k m : ℤ, gam k m u ∈ ball q 2 ∧ chartM q (toM u) = gam k m u := by
  obtain ⟨u', hu', he⟩ := h
  obtain ⟨k, m, hkm⟩ := toM_eq_iff.mp he.symm
  have hmem : gam k m u ∈ ball q 2 := by rw [hkm]; exact hu'
  refine ⟨k, m, hmem, ?_⟩
  rw [← toM_gam k m u]
  exact chartM_toM hmem

/-- Γ の元はアフィン写像であり、任意の滑らかさについて滑らかである。 -/
theorem contDiff_gam (n : ℕ∞ω) (k m : ℤ) : ContDiff ℝ n (gam k m) := by
  unfold gam
  exact (contDiff_fst.add contDiff_const).prodMk
    ((contDiff_const.mul contDiff_snd).add contDiff_const)

/-- M の点の持ち上げを一つ選ぶ。 -/
def liftM (x : KleinM) : ℝ × ℝ := Classical.choose (toM_surjective x)

theorem toM_liftM (x : KleinM) : toM (liftM x) = x := Classical.choose_spec (toM_surjective x)

/-- **M の座標系**：座標は φ_p（p ∈ ℝ²）のすべてである。 -/
instance instChartedSpaceKleinM : ChartedSpace (ℝ × ℝ) KleinM where
  atlas := Set.range chartM
  chartAt x := chartM (liftM x)
  mem_chart_source x := ⟨liftM x, mem_ball_self two_pos, toM_liftM x⟩
  chart_mem_atlas x := ⟨liftM x, rfl⟩

theorem chartM_mem_atlas (p : ℝ × ℝ) : chartM p ∈ atlas (ℝ × ℝ) KleinM := ⟨p, rfl⟩

theorem chartAt_kleinM (x : KleinM) : chartAt (ℝ × ℝ) x = chartM (liftM x) := rfl

/-- **M は滑らかな曲面である**：座標変換は Γ の元（アフィン写像）なので、任意の n（∞、ω を含む）について
M は ℝ² を模型とする境界のない Cⁿ 多様体である。 -/
instance instIsManifoldKleinM (n : ℕ∞ω) : IsManifold 𝓘(ℝ, ℝ × ℝ) n KleinM := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨p, rfl⟩ ⟨q, rfl⟩
  intro u hu
  simp only [mfld_simps] at hu ⊢
  obtain ⟨-, hu2⟩ := hu
  obtain ⟨k, m, hkm, -⟩ := chartM_toM_eq_gam hu2
  have hev : (⇑(chartM q) ∘ ⇑(chartM p).symm) =ᶠ[𝓝 u] gam k m := by
    have hopen : IsOpen (gam k m ⁻¹' ball q 2) := isOpen_ball.preimage (continuous_gam k m)
    filter_upwards [hopen.mem_nhds hkm] with u' hu'
    show chartM q (toM u') = gam k m u'
    rw [← toM_gam k m u']
    exact chartM_toM hu'
  exact ((contDiff_gam n k m).contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt

/-! ### π は局所微分同相である -/

/-- 座標 φ_p は定義域の上で滑らかである。 -/
theorem contMDiffOn_chartM (p : ℝ × ℝ) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (chartM p) (toM '' ball p 2) :=
  contMDiffOn_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chartM_mem_atlas p))

/-- π は各開球 B(p, 2) の上で滑らかである。 -/
theorem contMDiffOn_toM_ball (p : ℝ × ℝ) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ toM (ball p 2) :=
  contMDiffOn_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas (chartM_mem_atlas p))

/-- 被覆写像の B(p, 2) への制限は部分微分同相である。 -/
def coverDiffeo (p : ℝ × ℝ) :
    PartialDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ) KleinM ∞ where
  toPartialEquiv := (coverAt p).toPartialEquiv
  open_source := (coverAt p).open_source
  open_target := (coverAt p).open_target
  contMDiffOn_toFun := contMDiffOn_toM_ball p
  contMDiffOn_invFun := contMDiffOn_chartM p

/-- **π は局所微分同相である**。 -/
theorem isLocalDiffeomorph_toM :
    IsLocalDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ toM :=
  fun p => ⟨coverDiffeo p, mem_ball_self two_pos, fun _ _ => rfl⟩

/-- π は滑らかである。 -/
theorem contMDiff_toM : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ toM :=
  isLocalDiffeomorph_toM.contMDiff

theorem smoothness_ne_zero : (∞ : ℕ∞ω) ≠ 0 := by simp

/-- **dπ は各点で線形同型である**。 -/
theorem toM_mfderiv_bijective (p : ℝ × ℝ) :
    Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) toM p) := by
  obtain ⟨e, he⟩ := isLocalDiffeomorph_toM.isInvertible_mfderiv smoothness_ne_zero p
  rw [← he]
  exact e.bijective

/-! ### 降下：滑らかさ、鎖律、はめ込み -/

section Descend

variable {G : ℝ → ℝ → V3}
  (h : ∀ (k m : ℤ) (p : ℝ × ℝ), G (gam k m p).1 (gam k m p).2 = G p.1 p.2)

/-- **滑らかさの降下**：Γ 不変な滑らかな写像 f : ℝ² → ℝ³ の降下 f̄ : M → ℝ³ は滑らかである。 -/
theorem contMDiff_descend (hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2)) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (descend G h) := by
  intro x
  obtain ⟨p, rfl⟩ := toM_surjective x
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞
      ((fun u : ℝ × ℝ => G u.1 u.2) ∘ chartM p) (toM '' ball p 2) :=
    hG.contMDiff.comp_contMDiffOn (contMDiffOn_chartM p)
  have heq : ∀ y ∈ toM '' ball p 2,
      descend G h y = ((fun u : ℝ × ℝ => G u.1 u.2) ∘ chartM p) y := by
    intro y hy
    have e : descend G h (toM (chartM p y)) = G (chartM p y).1 (chartM p y).2 := rfl
    rw [toM_chartM hy] at e
    exact e
  exact (hcomp.congr heq).contMDiffAt
    ((isOpen_chartM_source p).mem_nhds (toM_mem_chartM_source p))

/-- 逆向き：降下 f̄ が滑らかなら f = f̄ ∘ π は滑らかである。 -/
theorem contDiff_of_contMDiff_descend
    (hG : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (descend G h)) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2) := by
  have h1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (descend G h ∘ toM) := hG.comp contMDiff_toM
  exact contMDiff_iff_contDiff.mp h1

/-- **鎖律** df|ₚ = df̄|_{π(p)} ∘ dπ|ₚ（接ベクトルごとの形）：p での任意の接ベクトル ξ について、
df̄|_{π(p)}(dπ|ₚ ξ) = df|ₚ ξ。 -/
theorem mfderiv_descend_apply (hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2)) (p ξ : ℝ × ℝ) :
    (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (descend G h) (toM p))
        ((mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) toM p) ξ) =
      fderiv ℝ (fun u : ℝ × ℝ => G u.1 u.2) p ξ := by
  have hD : HasFDerivAt (fun u : ℝ × ℝ => G u.1 u.2)
      (fderiv ℝ (fun u : ℝ × ℝ => G u.1 u.2) p) p :=
    ((hG.differentiable (by simp)) p).hasFDerivAt
  have hM : HasMFDerivAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (descend G h ∘ toM) p
      (fderiv ℝ (fun u : ℝ × ℝ => G u.1 u.2) p) := hD.hasMFDerivAt
  have e2 := mfderiv_comp_apply (I := 𝓘(ℝ, ℝ × ℝ)) (I' := 𝓘(ℝ, ℝ × ℝ)) (I'' := 𝓘(ℝ, V3))
    (x := p) (g := descend G h) (f := toM)
    ((contMDiff_descend h hG).mdifferentiableAt smoothness_ne_zero)
    (contMDiff_toM.mdifferentiableAt smoothness_ne_zero) ξ
  rw [← e2, hM.mfderiv]
  rfl

/-- **はめ込みの降下**：f̄ の微分が π(p) で単射であることと、f の微分が p で単射であることは同値である。 -/
theorem descend_immersion_iff (hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2)) (p : ℝ × ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (descend G h) (toM p)) ↔
      Function.Injective (fderiv ℝ (fun u : ℝ × ℝ => G u.1 u.2) p) := by
  have key := mfderiv_descend_apply h hG p
  obtain ⟨hBi, hBs⟩ := toM_mfderiv_bijective p
  constructor
  · intro hA ξ ξ' hξ
    apply hBi
    apply hA
    rw [key ξ, key ξ']
    exact hξ
  · intro hDinj a b hab
    obtain ⟨ξ, rfl⟩ := hBs a
    obtain ⟨ξ', rfl⟩ := hBs b
    rw [key ξ, key ξ'] at hab
    rw [hDinj hab]

/-- **接平面の降下**：f̄ の π(p) での微分の像は、f の p での微分の像に等しい。したがって M の上の法線
（f̄ の接平面に直交するベクトル）は、持ち上げた点での f の接平面に直交するベクトルである。 -/
theorem mfderiv_descend_range (hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2)) (p : ℝ × ℝ) (y : V3) :
    (∃ a, (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (descend G h) (toM p)) a = y) ↔
      ∃ ξ : ℝ × ℝ, fderiv ℝ (fun u : ℝ × ℝ => G u.1 u.2) p ξ = y := by
  have key := mfderiv_descend_apply h hG p
  obtain ⟨-, hBs⟩ := toM_mfderiv_bijective p
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨ξ, rfl⟩ := hBs a
    exact ⟨ξ, by rw [← key ξ]; exact ha⟩
  · rintro ⟨ξ, hξ⟩
    exact ⟨_, by rw [key ξ]; exact hξ⟩

end Descend

/-! ### 静的な面 Ŝ の降下 -/

section Static

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
/-- Ŝ_M : M → ℝ³ は滑らかである。 -/
theorem contMDiff_ShatM : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (ShatM w₀) :=
  contMDiff_descend (Shat_gam w₀) (contDiff_Shat h0 h1)

include h0 h1 in
/-- **Ŝ_M は M のはめ込みである**：微分は M の各点で単射である。 -/
theorem ShatM_immersion (x : KleinM) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (ShatM w₀) x) := by
  obtain ⟨p, rfl⟩ := toM_surjective x
  exact (descend_immersion_iff (Shat_gam w₀) (contDiff_Shat h0 h1) p).mpr (Shat_immersion h0 h1 p)

include h0 h1 in
/-- Mathlib の「微分の意味でのはめ込み」（`IsDiffImmersionAt`）の形。 -/
theorem ShatM_isDiffImmersionAt (x : KleinM) :
    IsDiffImmersionAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (ShatM w₀) x :=
  IsDiffImmersionAt.of_injective_of_finiteDimensional (ShatM_immersion h0 h1 x)

end Static

/-! ### M の正則ホモトピー -/

/-- **M の正則ホモトピー**：(s, x) について滑らかで、各段が M のはめ込みである族 H : ℝ × M → ℝ³。 -/
structure RegularHomotopyOnM (H : ℝ → KleinM → V3) : Prop where
  /-- 族は ℝ × M の上で滑らかである。 -/
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3) ∞ (fun z : ℝ × KleinM => H z.1 z.2)
  /-- 各段は M の上で滑らかである。 -/
  stage_smooth : ∀ s : ℝ, ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (H s)
  /-- 各段の微分は M の各点で単射である。 -/
  immersion : ∀ (s : ℝ) (x : KleinM),
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (H s) x)

section Family

variable {w₀ ε : ℝ} {F : ℝ → ℝ → ℝ → V3} (E : NeckEversion w₀ ε (Shat w₀) F)

include E in
/-- 族の各段は被覆平面の上で滑らかである。 -/
theorem contDiff_stage (s : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F s p.1 p.2) :=
  E.smooth.comp (contDiff_const.prodMk contDiff_id)

/-- 各段 F̄_s : M → ℝ³ は滑らかである。 -/
theorem contMDiff_FM (s : ℝ) : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (FM E s) :=
  contMDiff_descend (F_gam E s) (contDiff_stage E s)

/-- **各段 F̄_s は M のはめ込みである**。 -/
theorem FM_immersion (s : ℝ) (x : KleinM) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (FM E s) x) := by
  obtain ⟨p, rfl⟩ := toM_surjective x
  exact (descend_immersion_iff (F_gam E s) (contDiff_stage E s) p).mpr (E.immersion s p)

/-- Mathlib の「微分の意味でのはめ込み」（`IsDiffImmersionAt`）の形。 -/
theorem FM_isDiffImmersionAt (s : ℝ) (x : KleinM) :
    IsDiffImmersionAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (FM E s) x :=
  IsDiffImmersionAt.of_injective_of_finiteDimensional (FM_immersion E s x)

/-- **族 (s, x) ↦ F̄_s(x) は ℝ × M の上で滑らかである**。 -/
theorem contMDiff_FM_joint :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3) ∞ (fun z : ℝ × KleinM => FM E z.1 z.2) := by
  rintro ⟨s₀, x⟩
  obtain ⟨p, rfl⟩ := toM_surjective x
  have hUo : IsOpen (Prod.snd ⁻¹' (toM '' ball p 2) : Set (ℝ × KleinM)) :=
    (isOpen_chartM_source p).preimage continuous_snd
  have hψ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ × ℝ × ℝ) ∞
      (fun z : ℝ × KleinM => (z.1, chartM p z.2)) (Prod.snd ⁻¹' (toM '' ball p 2)) :=
    contMDiffOn_fst.prodMk_space ((contMDiffOn_chartM p).comp contMDiffOn_snd (fun _ hz => hz))
  have hcomp : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, V3) ∞
      ((fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) ∘ fun z : ℝ × KleinM => (z.1, chartM p z.2))
      (Prod.snd ⁻¹' (toM '' ball p 2)) :=
    E.smooth.contMDiff.comp_contMDiffOn hψ
  refine (hcomp.congr ?_).contMDiffAt (hUo.mem_nhds (toM_mem_chartM_source p))
  rintro ⟨s, y⟩ hy
  have e : FM E s (toM (chartM p y)) = F s (chartM p y).1 (chartM p y).2 := rfl
  rw [toM_chartM hy] at e
  exact e

/-- **首の裏返しの降下は M の正則ホモトピーである**。 -/
theorem FM_regularHomotopy : RegularHomotopyOnM (FM E) :=
  ⟨contMDiff_FM_joint E, contMDiff_FM E, FM_immersion E⟩

/-- 終わりの段：s ≥ 1 の首では F̄_s(π(w, v)) = −Ŝ_M(π(−w, π − v))。 -/
theorem FM_of_finish {s : ℝ} (hs : 1 ≤ s) {w : ℝ} (hw : |w| ≤ 1) (v : ℝ) :
    FM E s (toM (w, v)) = -ShatM w₀ (toM (-w, π - v)) :=
  E.finish s w v hs hw

/-- 首の動く部分の外では、どの段も F̄_s = Ŝ_M である。 -/
theorem FM_of_support (s : ℝ) {w : ℝ} (hw : ∀ k : ℤ, (9 / 10) * w₀ ≤ |w - 4 * (k : ℝ)|) (v : ℝ) :
    FM E s (toM (w, v)) = ShatM w₀ (toM (w, v)) :=
  E.support s w v hw

end Family

/-! ### 向きづけ不可能性（被覆変換の形） -/

/-- γ_{k,m} の線形部分は diag(1, (−1)ᵏ) であり、その行列式は (−1)ᵏ = `sgn k` である。M の向き（至る
ところ消えない最高次の形式）を局所微分同相 π で引き戻すと、ℝ² の上の連続で消えない関数 f で
f ∘ γ_{k,m} = (−1)ᵏ f を満たすものになる。**そのような f は存在しない**。したがって M は向きづけ
不可能である。 -/
theorem no_gam_orientation :
    ¬ ∃ f : ℝ × ℝ → ℝ, Continuous f ∧ (∀ p, f p ≠ 0) ∧
      ∀ (k m : ℤ) (p : ℝ × ℝ), f (gam k m p) = sgn k * f p := by
  rintro ⟨f, hf, hne, heq⟩
  have h1 : f (gam 1 0 (0, 0)) = -f (0, 0) := by
    rw [heq 1 0 (0, 0), sgn_one]
    ring
  let c : ℝ → ℝ × ℝ := fun t => ((1 - t) • ((0 : ℝ), (0 : ℝ)) + t • gam 1 0 (0, 0))
  have hc : Continuous c := by fun_prop
  have hfc : ContinuousOn (fun t => f (c t)) (uIcc (0 : ℝ) 1) := (hf.comp hc).continuousOn
  have e0 : f (c 0) = f (0, 0) := by simp [c]
  have e1 : f (c 1) = -f (0, 0) := by
    have : c 1 = gam 1 0 (0, 0) := by simp [c]
    rw [this, h1]
  have hmem : (0 : ℝ) ∈ uIcc (f (c 0)) (f (c 1)) := by
    rw [e0, e1, mem_uIcc]
    rcases le_total 0 (f (0, 0)) with h | h
    · right; constructor <;> linarith
    · left; constructor <;> linarith
  obtain ⟨t, -, ht⟩ := intermediate_value_uIcc hfc hmem
  exact hne (c t) ht

/-! ### M は閉じた曲面であり、平面と同相でない -/

/-- π は開な商写像である。 -/
theorem isOpenQuotientMap_toM : IsOpenQuotientMap toM :=
  ⟨toM_surjective, continuous_toM, isOpenMap_toM⟩

/-- M は連結である。 -/
instance kleinM_connectedSpace : ConnectedSpace KleinM :=
  toM_surjective.connectedSpace continuous_toM

/-- M は第二可算である。 -/
instance kleinM_secondCountable : SecondCountableTopology KleinM :=
  isOpenQuotientMap_toM.secondCountableTopology

/-- **M は平面と同相でない**：M はコンパクトであり、ℝ² はコンパクトでない。したがって被覆平面と商曲面は
位相空間として別の対象である。 -/
theorem kleinM_not_homeomorph_plane : ¬ Nonempty (KleinM ≃ₜ ℝ × ℝ) := by
  rintro ⟨e⟩
  exact not_compactSpace_iff.mpr inferInstance e.compactSpace

/-- **M は閉じた滑らかな曲面である**：コンパクト、ハウスドルフ、連結、第二可算で、ℝ² を模型とする
境界のない滑らかな多様体である。 -/
theorem kleinM_closed_surface :
    CompactSpace KleinM ∧ T2Space KleinM ∧ ConnectedSpace KleinM ∧
      SecondCountableTopology KleinM ∧ IsManifold 𝓘(ℝ, ℝ × ℝ) ∞ KleinM ∧
      BoundarylessManifold 𝓘(ℝ, ℝ × ℝ) KleinM :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end Zeno.Smale
