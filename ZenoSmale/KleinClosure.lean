/-
# ZenoSmale.KleinClosure : クラインの壺型閉包の束（量化の訂正、滑らかな商曲面、D7 の関係を加えたもの）

`KleinConception`（第 3 段階の束）に、次を加えて一つの定理 `mathemagical_klein_closure` にする。

- `stages_pos`・`stages_pos_static`・`stages_bounded`・`stages_bounded_static`：首の幅、面、裏返しの族、
  導線を固定すると、正の段階数のすべてを実現することはできず、実現できる段階数の集合は上に有界である
  （`KleinStages`）。既存の欄 `no_uniform`・`no_uniform_static` はこの系である。
- `surface`・`charts`・`covering`・`not_plane`・`not_orientable`：M = ℝ²/Γ は閉じた滑らかな曲面であり、
  座標変換は Γ の元、π は局所微分同相で、M は平面と同相でなく、Γ と両立する向きはない（`KleinSmooth`）。
- `descent`・`static_immersion`・`regular_homotopy`：Γ 不変な滑らかな写像は M の上の滑らかな写像に
  降下し、鎖律 df = df̄ ∘ dπ が成り立ち、はめ込みははめ込みに降下する。Ŝ_M は M の滑らかなはめ込みで
  あり、首の裏返しの降下は M の正則ホモトピーである。
- `same_F`：各 n₁ ≥ 1、ε > 0 について、同じ F が `DynamicPassage`、`DynamicEffects` を満たし、その降下が
  M の正則ホモトピーであり、D7 の位置の水準の命題（対称面の通過、t∗ での中央円、複素迂回の形との
  非両立、純虚数の助変数）を満たす。
- `formed`・`doors`・`static_doors`・`ideal_door`・`freedom`・`complex_display`：D7 の、形成写像と
  二つの扉、静的な面、理想形、自由度、複素表示についての命題（`KleinDoors`）。
- `twist_inherit`：岸の上では導線は第 3.1 版の捻り写像による像であり、各段階数での捻転は有界である。
- `cover_loops`：被覆平面の上で閉じた道に沿っては側は交換されない。M2 は商曲面の上の閉路で起きる。
-/
import ZenoSmale.KleinStages
import ZenoSmale.KleinSmooth
import ZenoSmale.KleinDoors
import Zeno.MobiusRun

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff Manifold
open Zeno.Model

/-! ### 被覆平面と商曲面：M2 は商曲面の上の閉路で起き、被覆平面の上の閉路では起きない -/

/-- **被覆平面の上の閉路では側は交換されない（静的な面）**：ℝ² の上で閉じた道に沿って Ŝ の法線に平行な
連続で消えない法線を運ぶと、正の倍で元に戻る。M2 の閉路は M の上で閉じ、ℝ² の上では閉じない
（`Shat_monodromy`）。 -/
theorem cover_loop_no_exchange {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) {γ : ℝ → ℝ × ℝ}
    (hγ : Continuous γ) (hloop : γ 1 = γ 0) {n : ℝ → V3} (hn : Continuous n)
    (hn0 : ∀ s, n s ≠ wp) (hpar : ∀ s, cross (n s) (Xhat w₀ (γ s).1 (γ s).2) = wp) :
    ∃ κ : ℝ, 0 < κ ∧ n 1 = κ • n 0 :=
  two_sided_no_exchange (N₀ := fun p : ℝ × ℝ => Xhat w₀ p.1 p.2) (continuous_Xhat h0 h1)
    (fun p => Xhat_ne h0 h1 p.1 p.2) hγ hn hn0 hpar hloop

/-- **被覆平面の上の閉路では側は交換されない（動く面）**：段 σ と道 γ がともに元に戻るなら、動く面の法線に
平行な連続で消えない法線は、正の倍で元に戻る。 -/
theorem cover_loop_no_exchange_dyn {w₀ ε : ℝ} {F : ℝ → ℝ → ℝ → V3}
    (E : NeckEversion w₀ ε (Shat w₀) F) {σ : ℝ → ℝ} (hσ : Continuous σ) {γ : ℝ → ℝ × ℝ}
    (hγ : Continuous γ) (hσloop : σ 1 = σ 0) (hloop : γ 1 = γ 0) {n : ℝ → V3}
    (hn : Continuous n) (hn0 : ∀ s, n s ≠ wp)
    (hpar : ∀ s, cross (n s) (XF F (σ s) (γ s).1 (γ s).2) = wp) :
    ∃ κ : ℝ, 0 < κ ∧ n 1 = κ • n 0 :=
  two_sided_no_exchange (N₀ := fun q : ℝ × ℝ × ℝ => XF F q.1 q.2.1 q.2.2)
    (continuous_XF_joint E) (fun q => XF_ne E q.1 q.2.1 q.2.2) (γ := fun s => (σ s, γ s))
    (hσ.prodMk hγ) hn hn0 hpar (by rw [hσloop, hloop])

/-! ### 無限捻転の継承：岸の上の導線は、第 3.1 版の捻り写像による像である -/

/-- 右岸（w ≥ c ≥ w₀ > 0）では、亀の角度は 0、アキレスの角度は捻転 θ(w) である。すなわちアキレスの導線は、
亀の直線 v = 0 の、捻り写像 (w, v) ↦ (w, v + θ(w)) による像である（第 3.1 版 定理 4.1 の (ii)）。 -/
theorem twist_shore_right {r w₀ c w : ℝ} (h0 : 0 < w₀) (hc : w₀ ≤ c) (hw : c ≤ w) (n₁ : ℕ) :
    VtR c w = 0 ∧ VaR r w₀ c n₁ w = theta r w := by
  have hc0 : 0 < c := h0.trans_le hc
  have hsq : w₀ ^ 2 / 2 ≤ w ^ 2 := by nlinarith
  refine ⟨by simp [VtR, ell_of_ge hc0 hw], ?_⟩
  simp only [VaR, ell_of_ge hc0 hw, thetaSm_of h0.ne' hsq]
  ring

/-- 左岸（w ≤ −c）では、亀の角度は −π、アキレスの角度は π + 4πn₁ − θ(w) である（左岸では面が
G(w, π − v) なので、位置は G(w, 0) と G(w, θ(w)) である）。 -/
theorem twist_shore_left {r w₀ c w : ℝ} (h0 : 0 < w₀) (hc : w₀ ≤ c) (hw : w ≤ -c) (n₁ : ℕ) :
    VtR c w = -π ∧ VaR r w₀ c n₁ w = π + 4 * π * n₁ - theta r w := by
  have hc0 : 0 < c := h0.trans_le hc
  have hsq : w₀ ^ 2 / 2 ≤ w ^ 2 := by nlinarith
  refine ⟨by simp [VtR, ell_of_le hc0 hw], ?_⟩
  simp only [VaR, ell_of_le hc0 hw, thetaSm_of h0.ne' hsq]
  ring

/-- **一つの連続な導線の捻転は有界である**：各段階数 n₁ で、アキレスの角度は [−1, 1] の上で有界である。
無限の捻転は、一つの正則な模型の中ではなく、n₁ → ∞ の極限（`twist_tendsto`）で現れる。 -/
theorem twist_bounded (r : ℝ) {w₀ : ℝ} (h0 : w₀ ≠ 0) (c : ℝ) (n₁ : ℕ) :
    ∃ B : ℝ, ∀ w ∈ Icc (-1 : ℝ) 1, |VaR r w₀ c n₁ w| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (contDiff_VaR r h0 c n₁).continuous.continuousOn (s := Icc (-1 : ℝ) 1)
  exact ⟨B, fun w hw => by simpa using hB w hw⟩

/-! ### 束 -/

/-- **クラインの壺型閉包の束**。 -/
structure KleinClosure (R : Race) : Prop where
  /-- 第 3 段階までの束（`mathemagical_klein_conception`）。 -/
  conception : KleinConception R
  /-- 量化の順序（動的、正の段階数）：首の幅、面、裏返しの族、導線を固定して、すべての正の段階数を実現する
  ことはできない。 -/
  stages_pos : ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (F : ℝ → ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
    ∀ n₁ : ℕ, 1 ≤ n₁ → ∃ c ε : ℝ, DynamicPassage R w₀ c ε n₁ S X F Vt Va
  /-- 量化の順序（静的、正の段階数）。 -/
  stages_pos_static : ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
    ∀ n₁ : ℕ, 1 ≤ n₁ → ∃ c : ℝ, KleinPassage R w₀ c n₁ S X Vt Va
  /-- 固定した構成が実現する段階数の集合は上に有界である（動的）。 -/
  stages_bounded : ∀ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (F : ℝ → ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
    ∃ N : ℕ, ∀ n₁ : ℕ, (∃ c ε : ℝ, DynamicPassage R w₀ c ε n₁ S X F Vt Va) → n₁ < N
  /-- 固定した構成が実現する段階数の集合は上に有界である（静的）。 -/
  stages_bounded_static : ∀ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
    ∃ N : ℕ, ∀ n₁ : ℕ, (∃ c : ℝ, KleinPassage R w₀ c n₁ S X Vt Va) → n₁ < N
  /-- M は閉じた滑らかな曲面である。 -/
  surface : CompactSpace KleinM ∧ T2Space KleinM ∧ ConnectedSpace KleinM ∧
    SecondCountableTopology KleinM ∧ IsManifold 𝓘(ℝ, ℝ × ℝ) ∞ KleinM ∧
    BoundarylessManifold 𝓘(ℝ, ℝ × ℝ) KleinM
  /-- 座標は π の局所的な逆であり、座標変換は Γ の元である。 -/
  charts : (∀ p u : ℝ × ℝ, u ∈ ball p 2 → chartM p (toM u) = u) ∧
    (∀ q u : ℝ × ℝ, toM u ∈ toM '' ball q 2 →
      ∃ k m : ℤ, gam k m u ∈ ball q 2 ∧ chartM q (toM u) = gam k m u)
  /-- π は局所微分同相であり、その微分は各点で全単射である。 -/
  covering : IsLocalDiffeomorph 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ toM ∧
    ∀ p : ℝ × ℝ, Function.Bijective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) toM p)
  /-- M は平面と同相でない。 -/
  not_plane : ¬ Nonempty (KleinM ≃ₜ ℝ × ℝ)
  /-- Γ と両立する向きはない（M は向きづけ不可能）。 -/
  not_orientable : ¬ ∃ f : ℝ × ℝ → ℝ, Continuous f ∧ (∀ p, f p ≠ 0) ∧
    ∀ (k m : ℤ) (p : ℝ × ℝ), f (gam k m p) = sgn k * f p
  /-- 降下：滑らかさ、鎖律 df = df̄ ∘ dπ、接平面、はめ込み。 -/
  descent : ∀ (G : ℝ → ℝ → V3)
    (h : ∀ (k m : ℤ) (p : ℝ × ℝ), G (gam k m p).1 (gam k m p).2 = G p.1 p.2),
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2) →
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (descend G h) ∧
    (∀ p ξ : ℝ × ℝ, (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (descend G h) (toM p))
        ((mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) toM p) ξ) =
      fderiv ℝ (fun u : ℝ × ℝ => G u.1 u.2) p ξ) ∧
    (∀ (p : ℝ × ℝ) (y : V3),
      (∃ a, (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (descend G h) (toM p)) a = y) ↔
        ∃ ξ : ℝ × ℝ, fderiv ℝ (fun u : ℝ × ℝ => G u.1 u.2) p ξ = y) ∧
    (∀ p : ℝ × ℝ,
      Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (descend G h) (toM p)) ↔
        Function.Injective (fderiv ℝ (fun u : ℝ × ℝ => G u.1 u.2) p))
  /-- Ŝ_M は M の滑らかなはめ込みである。 -/
  static_immersion : ∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 →
    ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) ∞ (ShatM w₀) ∧
    ∀ x : KleinM, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V3) (ShatM w₀) x)
  /-- 首の裏返しの降下は M の正則ホモトピーであり、s ≤ 0 で Ŝ_M、s ≥ 1 の首で −Ŝ_M ∘ φ に等しい。 -/
  regular_homotopy : ∀ (w₀ ε : ℝ) (F : ℝ → ℝ → ℝ → V3) (E : NeckEversion w₀ ε (Shat w₀) F),
    RegularHomotopyOnM (FM E) ∧ (∀ s : ℝ, s ≤ 0 → FM E s = ShatM w₀) ∧
    (∀ s w v : ℝ, 1 ≤ s → |w| ≤ 1 → FM E s (toM (w, v)) = -ShatM w₀ (toM (-w, π - v)))
  /-- 同じ F：`DynamicPassage`、`DynamicEffects`、M の正則ホモトピー、D7 の位置の水準の命題。 -/
  same_F : ∀ n₁ : ℕ, 1 ≤ n₁ → ∀ ε : ℝ, 0 < ε → ∃ (F : ℝ → ℝ → ℝ → V3)
    (P : DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ (Shat (R.r ^ n₁)) (Xhat (R.r ^ n₁)) F
      (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁)),
    DynamicEffects R (R.r ^ n₁) n₁ F ∧
    RegularHomotopyOnM (FM P.eversion) ∧
    (∀ s : ℝ, s ≤ 0 → FM P.eversion s = ShatM (R.r ^ n₁)) ∧
    (∃ t ∈ Ioo 0 R.tstar,
      xhat (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) = 0 ∧
      (dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t).1 = 0 ∧
      (∀ w v : ℝ, G w v ≠ dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) ∧
      |R.g t| < R.r ^ n₁) ∧
    (∃ t ∈ Ioo R.tstar (2 * R.tstar),
      xhat (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t) = 0 ∧
      (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t).1 = 0 ∧
      (∀ w v : ℝ, G w v ≠ dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t) ∧
      |R.r * R.g t| < R.r ^ n₁) ∧
    (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) R.tstar = F (1 / 2) 0 (VtR (R.r ^ n₁) 0) ∧
      dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) R.tstar =
        F (1 / 2) 0 (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ 0) ∧
      F (1 / 2) 0 (VtR (R.r ^ n₁) 0) ≠ F (1 / 2) 0 (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ 0)) ∧
    (¬ ∃ (z : ℂ) (κ κ' v v' : ℝ), 0 < κ ∧ 0 < κ' ∧
      dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) R.tstar = κ • GG ((R.r : ℂ) * z) v ∧
      dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) R.tstar = κ' • GG z v') ∧
    (R.r ^ n₁ + ε ≤ 1 / 2 →
      (∃ t ∈ Ioo R.tstar (2 * R.tstar), ∃ y v : ℝ, 0 < y ∧ y ≤ 1 ∧
        dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) t = GG ⟨0, y⟩ v) ∧
      (∃ t ∈ Ioo 0 R.tstar, ∃ y v : ℝ, 0 < y ∧ y ≤ 1 ∧
        dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t = GG ⟨0, y⟩ v))
  /-- D7：形成後の追いつきの方程式（助変数の水準）。解は t∗ だけ、値は ∞ で、実数解はない。差は t∗ の前で負、
  後で正である。 -/
  formed : (∀ t : ℝ, invOP (R.g t) = invOP (R.r * R.g t) ↔ t = R.tstar) ∧
    (invOP (R.g R.tstar) = OnePoint.infty ∧ invOP (R.r * R.g R.tstar) = OnePoint.infty) ∧
    (¬ ∃ t x : ℝ, invOP (R.g t) = (x : OnePoint ℝ) ∧ invOP (R.r * R.g t) = (x : OnePoint ℝ)) ∧
    (∀ t : ℝ, t < R.tstar → (R.g t)⁻¹ - (R.r * R.g t)⁻¹ < 0) ∧
    (∀ t : ℝ, R.tstar < t → 0 < (R.g t)⁻¹ - (R.r * R.g t)⁻¹)
  /-- D7：扉 0（一般形）、実の比較の零点の必然性とその対偶。 -/
  doors : (∀ (f : ℝ → V3) (a b : ℝ), a ≤ b → ContinuousOn f (Icc a b) →
      (∀ t ∈ Icc a b, f t ≠ wp) → 0 < xhat (f a) → xhat (f b) < 0 →
      ∃ t ∈ Ioo a b, xhat (f t) = 0 ∧ (f t).1 = 0 ∧ ∀ w v : ℝ, G w v ≠ f t) ∧
    (∀ (T A : ℝ → V3) (a b : ℝ), a ≤ b → ContinuousOn T (Icc a b) → ContinuousOn A (Icc a b) →
      (∀ t ∈ Icc a b, T t ≠ wp) → (∀ t ∈ Icc a b, A t ≠ wp) →
      xhat (A a) < xhat (T a) → xhat (T b) < xhat (A b) →
      ∃ t ∈ Ioo a b, xhat (T t) = xhat (A t)) ∧
    (∀ (T A : ℝ → V3) (a b : ℝ), a ≤ b → ContinuousOn T (Icc a b) → ContinuousOn A (Icc a b) →
      xhat (A a) < xhat (T a) → xhat (T b) < xhat (A b) →
      (∀ t ∈ Ioo a b, xhat (T t) ≠ xhat (A t)) → ∃ t ∈ Icc a b, T t = wp ∨ A t = wp)
  /-- D7：静的な面の上では、二人のどちらにも、t∗ の前に対称面を横切る時刻がある。 -/
  static_doors : ∀ n₁ : ℕ, 1 ≤ n₁ →
    (∃ t ∈ Ioo 0 R.tstar,
      xhat (R.runT (Shat (R.r ^ n₁)) (VtR (R.r ^ n₁)) t) = 0 ∧
      (R.runT (Shat (R.r ^ n₁)) (VtR (R.r ^ n₁)) t).1 = 0 ∧
      ∀ w v : ℝ, G w v ≠ R.runT (Shat (R.r ^ n₁)) (VtR (R.r ^ n₁)) t) ∧
    (∃ t ∈ Ioo 0 R.tstar,
      xhat (R.runA (Shat (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t) = 0 ∧
      (R.runA (Shat (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t).1 = 0 ∧
      ∀ w v : ℝ, G w v ≠ R.runA (Shat (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) t)
  /-- D7：理想形は扉 ∞ を通る。 -/
  ideal_door : R.idealT R.tstar = wp ∧ R.idealA R.tstar = wp ∧
    ∀ t, t ≠ R.tstar → xhat (R.idealT t) ≠ xhat (R.idealA t)
  /-- D7：自由度。中央の角度が 2π の整数倍だけ違えば t∗ に衝突する。主定理の導線では差は π + 2πn₁。 -/
  freedom : (∀ (w₀ : ℝ) (F : ℝ → ℝ → ℝ → V3), (∀ s w v : ℝ, F s w (v + 2 * π) = F s w v) →
      ∀ (Vt Va : ℝ → ℝ) (m : ℤ), Va 0 = Vt 0 + m * (2 * π) →
      dynT R w₀ F Vt R.tstar = dynA R w₀ F Va R.tstar) ∧
    (∀ S : ℝ → ℝ → V3, (∀ w v : ℝ, S w (v + 2 * π) = S w v) →
      ∀ (Vt Va : ℝ → ℝ) (m : ℤ), Va 0 = Vt 0 + m * (2 * π) →
      R.runT S Vt R.tstar = R.runA S Va R.tstar) ∧
    (∀ (w₀ : ℝ) (n₁ : ℕ), VaR R.r w₀ (R.r ^ n₁) n₁ 0 - VtR (R.r ^ n₁) 0 = π + n₁ * (2 * π))
  /-- D7：複素表示 𝔾 では、対称面の点は純虚数の助変数の点である。 -/
  complex_display : (∀ y v : ℝ, (GG ⟨0, y⟩ v).1 = 0) ∧
    (∀ q : V3, q.1 = 0 → q ≠ wp → nsq q ≤ 1 / 4 →
      ∃ y v : ℝ, 0 < y ∧ y ≤ 1 ∧ q = GG ⟨0, y⟩ v)
  /-- 無限捻転の継承：岸の上では導線は第 3.1 版の捻り写像による像であり、各段階数での捻転は有界である。 -/
  twist_inherit : (∀ (n₁ : ℕ) (w : ℝ), R.r ^ n₁ ≤ w →
      VtR (R.r ^ n₁) w = 0 ∧ VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ w = theta R.r w) ∧
    (∀ (n₁ : ℕ) (w : ℝ), w ≤ -R.r ^ n₁ →
      VtR (R.r ^ n₁) w = -π ∧
        VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ w = π + 4 * π * n₁ - theta R.r w) ∧
    (∀ n₁ : ℕ, ∃ B : ℝ, ∀ w ∈ Icc (-1 : ℝ) 1, |VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁ w| ≤ B)
  /-- 被覆平面の上で閉じた道に沿っては、側は交換されない。 -/
  cover_loops : ∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 → ∀ γ : ℝ → ℝ × ℝ, Continuous γ → γ 1 = γ 0 →
    ∀ n : ℝ → V3, Continuous n → (∀ s, n s ≠ wp) →
    (∀ s, cross (n s) (Xhat w₀ (γ s).1 (γ s).2) = wp) → ∃ κ : ℝ, 0 < κ ∧ n 1 = κ • n 0

end Zeno.Smale

namespace Zeno

open Zeno.Model Zeno.Smale Real Set Filter Topology

/-- **クラインの壺型閉包の束の定理**。 -/
theorem mathemagical_klein_closure (R : Race) : KleinClosure R where
  conception := mathemagical_klein_conception R
  stages_pos := no_uniform_dynamic_passage_pos R
  stages_pos_static := no_uniform_klein_passage_pos R
  stages_bounded := dynamic_stages_bounded R
  stages_bounded_static := klein_stages_bounded R
  surface := kleinM_closed_surface
  charts := ⟨fun _ _ hu => chartM_toM hu, fun _ _ h => chartM_toM_eq_gam h⟩
  covering := ⟨isLocalDiffeomorph_toM, toM_mfderiv_bijective⟩
  not_plane := kleinM_not_homeomorph_plane
  not_orientable := no_gam_orientation
  descent := fun _ h hG =>
    ⟨contMDiff_descend h hG, mfderiv_descend_apply h hG, mfderiv_descend_range h hG,
      descend_immersion_iff h hG⟩
  static_immersion := fun _ h0 h1 => ⟨contMDiff_ShatM h0 h1, ShatM_immersion h0 h1⟩
  regular_homotopy := fun _ _ _ E =>
    ⟨FM_regularHomotopy E, fun _ hs => FM_of_start E hs, fun _ _ v hs hw => FM_of_finish E hs hw v⟩
  same_F := fun n₁ hn ε hε => by
    obtain ⟨F, P, E⟩ := dynamic_effects R hn hε
    exact ⟨F, P, E, FM_regularHomotopy P.eversion, fun _ hs => FM_of_start P.eversion hs,
      door_zero_A P E, door_zero_T P E hn, dyn_centre P, no_common_complex_parameter E,
      fun hb => ⟨door_zero_T_imaginary P E hn hε.le hb, door_zero_A_imaginary P E hε.le hb⟩⟩
  formed := ⟨formed_meeting_iff R, formed_meeting_value R, formed_no_real_solution R,
    fun _ ht => formed_diff_neg R ht, fun _ ht => formed_diff_pos R ht⟩
  doors := ⟨fun _ _ _ hab hf hne ha hb => door_zero hab hf hne ha hb,
    fun _ _ _ _ hab hT hA hT0 hA0 ha hb => xhat_compare_zero_of_avoid hab hT hA hT0 hA0 ha hb,
    fun _ _ _ _ hab hT hA ha hb hno => passes_wp_of_no_compare_zero hab hT hA ha hb hno⟩
  static_doors := fun n₁ hn =>
    ⟨static_door_zero_T R (pow_pos R.r_pos n₁) (R.pow_lt_one hn) n₁ le_rfl hn,
      static_door_zero_A R (pow_pos R.r_pos n₁) (R.pow_lt_one hn) n₁ le_rfl⟩
  ideal_door := ideal_door_infty R
  freedom := ⟨fun w₀ _ hper _ _ _ h => dyn_collision_of_centre_angle R w₀ hper h,
    fun _ hper _ _ _ h => run_collision_of_centre_angle R hper h,
    fun w₀ n₁ => centre_angle_diff R w₀ n₁⟩
  complex_display := ⟨GG_imaginary_fst, fun _ h1 hne hs => mirror_point_imaginary h1 hne hs⟩
  twist_inherit := ⟨fun n₁ _ hw => twist_shore_right (pow_pos R.r_pos n₁) le_rfl hw n₁,
    fun n₁ _ hw => twist_shore_left (pow_pos R.r_pos n₁) le_rfl hw n₁,
    fun n₁ => twist_bounded R.r (pow_pos R.r_pos n₁).ne' (R.r ^ n₁) n₁⟩
  cover_loops := fun _ h0 h1 _ hγ hloop _ hn hn0 hpar =>
    cover_loop_no_exchange h0 h1 hγ hloop hn hn0 hpar

end Zeno
