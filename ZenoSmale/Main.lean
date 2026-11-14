/-
# ZenoSmale.Main : MatheMagical Project の主定理

競走から P → ℘ の形成写像を作り、一つの枠つき平面 (G, N) の上に三つの形を置く。
A は理想形（無限捻転そのまま、t∗ で ℘ に一致）、B は静止した正則な接続（全時刻で非衝突）、
C は平面全体の正則ホモトピー（Smale–Hirsch）である。

表裏の反転、前後の反転、非衝突は別々の欄にあり、どれも定義に含まれていない。
反転は「強制」ではない。同じホーンの対について、反転しない世界（命題 D の射影チャート、B8 の管）も
同じ主定理の中で正則に実現されている。
-/
import ZenoSmale.Basic
import ZenoSmale.Surface
import ZenoSmale.Plane
import Zeno.Flex
import Zeno.Tube
import Zeno.Charts
import Zeno.Meaning

noncomputable section

namespace Zeno

open Metric Module Set Function Filter
open scoped Manifold Topology ContDiff
open Zeno.Model Zeno.Smale Real

/-- **C4**：球面そのものの場合。`theorem Smale` の族の端点は E で働く。 -/
structure SmaleFacts : Prop where
  /-- Smale の定理（sphere-eversion）。 -/
  exists_eversion : ∃ f, IsEversion f
  /-- 端点の作用：枠に E として働き、⟨q, n⟩ の符号を変え、途中に ⟨q, n⟩ = 0 の時刻がある。 -/
  endpoints : ∀ f, IsEversion f → ∀ x : 𝕊²,
    framePt (𝓡 2) (f 1) x (e0 x) (e1 x) = Everse (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) ∧
    pair3 (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) ≠ 0 ∧
    pair3 (framePt (𝓡 2) (f 1) x (e0 x) (e1 x)) = -pair3 (framePt (𝓡 2) (f 0) x (e0 x) (e1 x)) ∧
    ∃ t ∈ Ioo (0 : ℝ) 1, pair3 (framePt (𝓡 2) (f t) x (e0 x) (e1 x)) = 0
  /-- 文字どおり一点では起きない。 -/
  not_point : ∀ q : ℝ³, ¬ Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (fun _ : 𝕊² => q) ((⊤ : ℕ∞) : WithTop ℕ∞)
  /-- 放射状の潰れに δ で近い族がある。 -/
  close : ∀ δ : ℝ, 0 < δ → ∃ f : ℝ → 𝕊² → ℝ³, IsEversion f ∧
    ∀ t x, dist (f t x) ((1 - smoothStep t : ℝ) • (x : ℝ³) + (smoothStep t : ℝ) • (-(x : ℝ³))) ≤ δ
  /-- 任意の球の中で裏返る。 -/
  in_ball : ∀ η : ℝ, 0 < η → ∃ f : ℝ → 𝕊² → ℝ³,
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ((⊤ : ℕ∞) : WithTop ℕ∞) ↿f ∧
    (f 0 = fun x : 𝕊² => (η / 2) • (x : ℝ³)) ∧ (f 1 = -f 0) ∧
    (∀ t, Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (f t) ((⊤ : ℕ∞) : WithTop ℕ∞)) ∧ (∀ t x, ‖f t x‖ ≤ η) ∧
    ∀ x, framePt (𝓡 2) (f 1) x (e0 x) (e1 x) = Everse (framePt (𝓡 2) (f 0) x (e0 x) (e1 x))

theorem smale_facts : SmaleFacts where
  exists_eversion := exists_isEversion
  endpoints := fun _ hf x => smale_endpoints hf x
  not_point := not_immersion_const
  close := fun _ hδ => sphere_eversion_close hδ
  in_ball := fun _ hη => eversion_in_ball hη

/-- **主定理**。 -/
structure MainTheorem (R : Race) : Prop where
  /-- 定理 A：理想形。 -/
  ideal : IdealPassage R
  /-- 子午線：レムニスケートで、w = 0 に変曲点をもつ。 -/
  meridian : ∀ w : ℝ, (aa w ^ 2 + bb w ^ 2) ^ 2 = aa w * bb w ∧
    (aa w : ℂ) + Complex.I * (bb w : ℂ) = (w : ℂ) / (1 - Complex.I * (w : ℂ) ^ 2) ∧
    (da w : ℂ) + Complex.I * (db w : ℂ) =
      (1 + Complex.I * (w : ℂ) ^ 2) ^ 3 / ((Zeno.Model.D w : ℝ) : ℂ) ^ 2
  /-- 命題 D：何が反転を選ぶか。 -/
  charts : ChartDichotomy
  /-- B1、B2：静止した正則な接続の面。 -/
  neck : ∀ w₀ ∈ Ioo (0 : ℝ) 1, IsNeckSurface w₀ (Sig w₀) (Xf w₀) ∧
    IsNormalField (Sig w₀) (fun p => Xf w₀ p.1 p.2)
  /-- 定理 B：その面の上の走者。t = 0 に両者は右岸に、t = 2t∗ に左岸にいる。 -/
  regular : ∀ n₁ : ℕ, 1 ≤ n₁ → ∀ w₀, 0 < w₀ → w₀ ≤ R.r ^ n₁ →
    RegularPassage R w₀ (R.r ^ n₁) n₁ (Sig w₀) (Xf w₀) (VtR (R.r ^ n₁))
      (VaR R.r w₀ (R.r ^ n₁) n₁) ∧
    (R.r ^ n₁ ≤ R.r * R.g 0 ∧ R.r ^ n₁ ≤ R.g 0) ∧
    (R.r * R.g (2 * R.tstar) ≤ -R.r ^ n₁ ∧ R.g (2 * R.tstar) ≤ -R.r ^ n₁)
  /-- B は A に収束する（「或いは近似的に」）。 -/
  regular_limit : ∀ t,
    Tendsto (fun n : ℕ => R.runT (Sig (R.r ^ n)) (VtR (R.r ^ n)) t) atTop (𝓝 (R.idealT t)) ∧
    Tendsto (fun n : ℕ => R.runA (Sig (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n) t) atTop
      (𝓝 (R.idealA t))
  /-- B8：反例世界。半回転のない管も正則で、そこでは表裏は反転しない。 -/
  tube : ∀ w₀ ∈ Ioo (0 : ℝ) 1, IsTubeSurface w₀ (Tub w₀) (XT w₀) ∧
    IsNormalField (Tub w₀) (fun p => XT w₀ p.1 p.2)
  tube_keeps : ∀ w₀, 0 < w₀ → ∀ S X, IsTubeSurface w₀ S X → ∀ n, IsNormalField S n →
    ∀ w₁ w₂ v₁ v₂, w₀ < w₁ → w₂ < -w₀ →
      0 < side (S w₁ v₁) (n (w₁, v₁)) * side (S w₂ v₂) (n (w₂, v₂))
  no_equivariant : ∀ w, w ≠ 0 → ¬ ∃ A B : ℝ, ∀ v, ((A, B * cos v, B * sin v) : V3) = G w (π - v)
  symmetric_neck : ∀ S : ℝ → ℝ → V3, (∀ w v, S (-w) (π - v) = -S w v) → S 0 (π / 2) = wp
  /-- C1：傘の折り目。 -/
  umbrella_ends : ∀ q : V3, Lam 0 q = q ∧ Lam π q = -q
  umbrella : ∀ φ y, Function.Injective (fderiv ℝ (fun y => Lam φ (planeG y)) y) ↔
    ¬ (cos φ = 0 ∧ tau y ^ 2 = 1 / 3)
  /-- 平面 g はホーンをちょうど含むはめ込みである。 -/
  plane_horn : ∀ ρ, 0 < ρ → ρ ^ 2 ≤ 2 → ∀ v, planeG (cos v / ρ, sin v / ρ) = G ρ v
  plane_immersion : ∀ y, Function.Injective (fderiv ℝ planeG y)
  /-- C3、C2：平面全体の正則ホモトピーと、その上の走者。走者の窓を狭めると A に収束する。 -/
  flex : ∀ κ₀ ε : ℝ, 0 < κ₀ → κ₀ ≤ 1 → 0 < ε → ∃ f : ℝ → ℝ × ℝ → V3,
    IsPlaneEversion κ₀ ε f ∧ FamilyFacts κ₀ ε f ∧
    (∀ η ∈ Ioo (0 : ℝ) 1,
      FlexPassage R η κ₀ f (R.sT η) (R.yTt η) (R.yAt η) (R.thT η) (R.zT η) ∧
      η ≤ R.g 0 ∧ R.g (2 * R.tstar) ≤ -η) ∧
    (∀ t ∈ Icc 0 (2 * R.tstar),
      Tendsto (fun η => f (R.sT η t) (R.yTt η t)) (𝓝[>] 0) (𝓝 (R.idealT t)) ∧
      Tendsto (fun η => f (R.sT η t) (R.yAt η t)) (𝓝[>] 0) (𝓝 (R.idealA t)))
  /-- 𝔾 の実軸は G で、傘は 𝔾 の極座標である。 -/
  complex_form : (∀ w v : ℝ, GG (w : ℂ) v = G w v) ∧ (∀ ρ φ v : ℝ, GG (zOf ρ φ) v = Lam φ (G ρ v)) ∧
    (∀ ρ φ : ℝ, zOf ρ φ = (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
  /-- C4：球面。 -/
  smale : SmaleFacts

/-- **主定理**：任意の競走について、理想形、静止した正則な接続、正則ホモトピーの各構成が、
枠つき平面 (G, N) を共通の基準として成り立つ。球面の欄 `smale` は独立した参照結果である。 -/
theorem mathemagical_main (R : Race) : MainTheorem R where
  ideal := ideal_passage R
  meridian := fun w => ⟨lemniscate w, meridian_formula w, meridian_velocity w⟩
  charts := chart_dichotomy
  neck := fun w₀ h => ⟨Sig_isNeckSurface h.1 h.2, (Sig_isNeckSurface h.1 h.2).isNormalField⟩
  regular := fun n₁ hn w₀ h0 hc => by
    have hr0 := R.r_pos
    have hr1 := R.r_lt_one
    have hle : R.r ^ n₁ ≤ R.r := by
      calc R.r ^ n₁ ≤ R.r ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le hn
        _ = R.r := pow_one _
    have h1 : w₀ < 1 := by linarith
    refine ⟨regular_passage R h0 h1 n₁ hc, ?_, ?_⟩
    · rw [R.g_start]
      constructor <;> linarith
    · rw [R.g_end]
      constructor <;> linarith
  regular_limit := fun t => ⟨regular_tendsto_T R t, regular_tendsto_A R t⟩
  tube := fun w₀ h => ⟨Tub_isTubeSurface h.1 h.2, (Tub_isTubeSurface h.1 h.2).isNormalField⟩
  tube_keeps := fun w₀ h0 S X h n hn w₁ w₂ v₁ v₂ h₁ h₂ => tube_no_reversal h0 h hn h₁ h₂ v₁ v₂
  no_equivariant := fun w hw => no_equivariant_neck hw
  symmetric_neck := fun _ h => symmetric_neck_passes_wp h
  umbrella_ends := fun q => ⟨Lam_zero q, Lam_pi q⟩
  umbrella := umbrella_crease
  plane_horn := fun ρ hρ h v => planeG_polar hρ h v
  plane_immersion := planeG_immersion
  flex := fun κ₀ ε h0 h1 hε => by
    obtain ⟨f, hs, hi, hx, hc⟩ := plane_eversion_rel_horn h0 h1 hε
    have hf : IsPlaneEversion κ₀ ε f := ⟨hs, hi, hx, hc⟩
    refine ⟨f, hf, family_facts h0 h1 hf, ?_, ?_⟩
    · intro η hη
      refine ⟨flex_passage R hη.1 hη.2 h0 h1 hf, ?_, ?_⟩
      · rw [R.g_start]; exact hη.2.le
      · rw [R.g_end]; linarith [hη.2]
    · intro t ht
      exact ⟨flex_tendsto_T R h0 h1 hf ht, flex_tendsto_A R h0 h1 hf ht⟩
  complex_form := ⟨GG_real, GG_polar, zOf_eq⟩
  smale := smale_facts

/-- **【議論】の形**：静止した正則な面の上で、出発時に亀は表、アキレスは裏にいて、到着時に入れ替わっている。
その間、二人は同時刻には一度も同じ点におらず、アキレスは亀の過去の位置に後から着く（最初の段階）。
「追い越し」という語はこの定理の外にある見做しである。 -/
theorem regular_headline (R : Race) {n₁ : ℕ} (hn : 1 ≤ n₁) :
    let c := R.r ^ n₁
    let T := R.runT (Sig c) (VtR c)
    let A := R.runA (Sig c) (VaR R.r c c n₁)
    let X := Xf c
    Front (T 0) (X (R.r * R.g 0) (VtR c (R.r * R.g 0))) ∧
    Back (T (2 * R.tstar)) (X (R.r * R.g (2 * R.tstar)) (VtR c (R.r * R.g (2 * R.tstar)))) ∧
    Back (A 0) (-X (R.g 0) (VaR R.r c c n₁ (R.g 0))) ∧
    Front (A (2 * R.tstar)) (-X (R.g (2 * R.tstar)) (VaR R.r c c n₁ (R.g (2 * R.tstar)))) ∧
    A (R.tn 1) = T (R.tn 0) ∧ R.tn 0 < R.tn 1 ∧
    (∀ t ∈ Icc 0 (2 * R.tstar), T t ≠ A t) := by
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hc0 : 0 < R.r ^ n₁ := pow_pos hr0 n₁
  obtain ⟨hP, ⟨h1, h2⟩, h3, h4⟩ := (mathemagical_main R).regular n₁ hn (R.r ^ n₁) hc0 le_rfl
  refine ⟨hP.side_T_right 0 h1, hP.side_T_left _ h3, hP.side_A_right 0 h2, hP.side_A_left _ h4,
    hP.step_before 0 (by omega), ?_, hP.no_collision⟩
  simp only [Race.tn, pow_zero, sub_self, mul_zero, pow_one]
  exact mul_pos R.tstar_pos (by linarith)

/-- **【議論】の形（位置としての表裏）**：出発時、亀を自分の側へ少しずらした点はホーンの外（Φ > 0）に、
アキレスを自分の側へ少しずらした点はホーンの内（Φ < 0）にある。到着時はその逆である。 -/
theorem regular_headline_outside (R : Race) {n₁ : ℕ} (hn : 1 ≤ n₁) :
    let c := R.r ^ n₁
    let T := R.runT (Sig c) (VtR c)
    let A := R.runA (Sig c) (VaR R.r c c n₁)
    let X := Xf c
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < Phi (T 0 + ε • X (R.r * R.g 0) (VtR c (R.r * R.g 0)))) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), Phi (T (2 * R.tstar) +
      ε • X (R.r * R.g (2 * R.tstar)) (VtR c (R.r * R.g (2 * R.tstar)))) < 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), Phi (A 0 + ε • -X (R.g 0) (VaR R.r c c n₁ (R.g 0))) < 0) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < Phi (A (2 * R.tstar) +
      ε • -X (R.g (2 * R.tstar)) (VaR R.r c c n₁ (R.g (2 * R.tstar))))) := by
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hc0 : 0 < R.r ^ n₁ := pow_pos hr0 n₁
  have hle : R.r ^ n₁ ≤ R.r := by
    calc R.r ^ n₁ ≤ R.r ^ 1 := pow_le_pow_of_le_one hr0.le hr1.le hn
      _ = R.r := pow_one _
  obtain ⟨hP, -, -⟩ := (mathemagical_main R).regular n₁ hn (R.r ^ n₁) hc0 le_rfl
  have hh := regular_headline R hn
  simp only at hh
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := hh
  have aT0 := hP.agree_T 0 (by rw [R.g_start, mul_one, abs_of_pos hr0]; exact hle)
  have aT2 := hP.agree_T (2 * R.tstar) (by rw [R.g_end, mul_neg_one, abs_neg, abs_of_pos hr0]; exact hle)
  have aA0 := hP.agree_A 0 (by rw [R.g_start, abs_one]; linarith)
  have aA2 := hP.agree_A (2 * R.tstar) (by rw [R.g_end, abs_neg, abs_one]; linarith)
  refine ⟨front_outside ?_ h1, back_inside ?_ h2, back_inside ?_ h3, front_outside ?_ h4⟩
  · rw [aT0]; exact Phi_G _ _
  · rw [aT2]; exact Phi_G _ _
  · rw [aA0]; exact Phi_G _ _
  · rw [aA2]; exact Phi_G _ _

/-- 具体例：d₀ = 1、vₜ = 1、vₐ = 2。r = ½、t∗ = 1。 -/
def exampleRace : Race where
  d0 := 1
  vt := 1
  va := 2
  hd := one_pos
  hvt := one_pos
  hlt := by norm_num

theorem example_r : exampleRace.r = 1 / 2 := by
  simp [Race.r, exampleRace]

theorem example_tstar : exampleRace.tstar = 1 := by
  simp [Race.tstar, exampleRace]
  norm_num

/-- **空虚でないこと**：具体的な競走で、主定理と【議論】の形がそのまま成り立つ。 -/
theorem mathemagical_nonvacuous :
    MainTheorem exampleRace ∧ exampleRace.r = 1 / 2 ∧ exampleRace.tstar = 1 ∧
    (let c := exampleRace.r ^ 1
     let T := exampleRace.runT (Sig c) (VtR c)
     let A := exampleRace.runA (Sig c) (VaR exampleRace.r c c 1)
     let X := Xf c
     Front (T 0) (X (exampleRace.r * exampleRace.g 0) (VtR c (exampleRace.r * exampleRace.g 0))) ∧
     Back (T 2) (X (exampleRace.r * exampleRace.g 2) (VtR c (exampleRace.r * exampleRace.g 2))) ∧
     Back (A 0) (-X (exampleRace.g 0) (VaR exampleRace.r c c 1 (exampleRace.g 0))) ∧
     Front (A 2) (-X (exampleRace.g 2) (VaR exampleRace.r c c 1 (exampleRace.g 2))) ∧
     A (exampleRace.tn 1) = T (exampleRace.tn 0) ∧
     exampleRace.tn 0 < exampleRace.tn 1 ∧
     (∀ t ∈ Icc (0 : ℝ) 2, T t ≠ A t)) := by
  have hts : exampleRace.tstar = 1 := example_tstar
  have ht2 : (2 : ℝ) = 2 * exampleRace.tstar := by rw [hts]; norm_num
  have h := regular_headline exampleRace (n₁ := 1) le_rfl
  refine ⟨mathemagical_main exampleRace, example_r, hts, ?_⟩
  simp only at h ⊢
  rw [ht2]
  exact h

end Zeno
