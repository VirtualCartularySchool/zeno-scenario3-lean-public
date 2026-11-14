/-
# ZenoSmale.KleinSynthesis : K3⁺ の帰結の束（同じ F の上の全効果、量化の順序、理想化の極限）

`DynamicPassage` を満たす F について、`KleinNormal`・`KleinIdeal`・`KleinCover` の結果を一つの構造体
`DynamicEffects` にまとめ、`KleinTheorem` と合わせて一つの定理 `mathemagical_klein_synthesis` にする。

- `effects`：各 n₁ ≥ 1、ε > 0 について、**同じ F** が `DynamicPassage` と `DynamicEffects`
  （動く面の法線での M1、内在的な側の不変、動かないホーン、各段の M1、中央円の途中の段、Γ の作用、
  D7 の動的な比較、℘ の回避）を満たす。
- `d7_base`：D7 の基底の比較（x̂ の差 2bb₀/N₀ > 0、断面の差 0、回転枠での静的な値）。
- `no_uniform`・`no_uniform_static`：面の族と導線を固定してすべての段階数を実現することはできない。
- `limit`：全効果を満たす F_n の列で、走者が理想形に一様に収束するものがある。`limit_meet` は、
  その極限の理想形では t∗ に二人が一致すること（定理 10.1 による強制）。
- `window`：窓と球の収束。`deck`：Γ の作用（合成則、自由性、一様な離散性、Ŝ の不変性）。
- `quotient`：商曲面 M = ℝ²/Γ（`KleinM`）はコンパクトなハウスドルフ空間で、被覆写像は連続な開写像、
  半径 2 の球の上で単射。Ŝ は M に降下し、M の上に連続で消えない法線場はない。
-/
import ZenoSmale.KleinIdeal
import ZenoSmale.KleinQuotient
import ZenoSmale.KleinMain

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff
open Zeno.Model

/-- `DynamicPassage` は ε について単調である。 -/
theorem DynamicPassage.mono {R : Race} {w₀ c ε ε' : ℝ} {n₁ : ℕ} {X : ℝ → ℝ → V3}
    {F : ℝ → ℝ → ℝ → V3} {Vt Va : ℝ → ℝ} (h0 : 0 < w₀) (hε0 : 0 ≤ ε) (hε : ε ≤ ε')
    (P : DynamicPassage R w₀ c ε n₁ (Shat w₀) X F Vt Va) :
    DynamicPassage R w₀ c ε' n₁ (Shat w₀) X F Vt Va :=
  { P with
    eversion := P.eversion.mono h0 hε0 hε
    sandwich_T := fun t ht => (P.sandwich_T t ht).trans hε
    sandwich_A := fun t ht => (P.sandwich_A t ht).trans hε
    near_T := fun t ht => (P.near_T t ht).trans hε
    near_A := fun t ht => (P.near_A t ht).trans hε }

/-- **K3⁺ の帰結**：`DynamicPassage` を満たす F が、動く面自身の法線と Γ の作用について満たすこと。
w₀ は首の幅、岸の閾値は rⁿ¹ である。 -/
structure DynamicEffects (R : Race) (w₀ : ℝ) (n₁ : ℕ) (F : ℝ → ℝ → ℝ → V3) : Prop where
  /-- s ≤ 0 では動く面の法線は静的な法線である。 -/
  normal_start : ∀ s w v : ℝ, s ≤ 0 → XF F s w v = Xhat w₀ w v
  /-- 首の動く部分の外では、どの段でも動く面の法線は静的な法線である。 -/
  normal_shore : ∀ s w v : ℝ, w₀ * (9 / 10) < |w| → |w| < 2 → XF F s w v = Xhat w₀ w v
  /-- s ≥ 1 の首では X_{F,s}(w, v) = X̂(−w, π − v)（枠の法則 E）。 -/
  normal_finish : ∀ s w v : ℝ, 1 ≤ s → |w| < 1 → XF F s w v = Xhat w₀ (-w) (π - v)
  /-- 動く面の法線は (s, w, v) について連続である。 -/
  normal_cont : Continuous (fun q : ℝ × ℝ × ℝ => XF F q.1 q.2.1 q.2.2)
  /-- 亀に沿う動く面の法線は連続で消えない。 -/
  carry_T : Continuous (dynNT R w₀ F (VtR (R.r ^ n₁))) ∧
    ∀ t, dynNT R w₀ F (VtR (R.r ^ n₁)) t ≠ wp
  /-- アキレスに沿う動く面の法線は連続で消えない。 -/
  carry_A : Continuous (dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁)) ∧
    ∀ t, dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t ≠ wp
  /-- 動く面の法線での M1（亀）：右岸で表。 -/
  label_T_right : ∀ t ∈ Icc 0 (2 * R.tstar), R.r ^ n₁ ≤ R.r * R.g t →
    Front (dynT R w₀ F (VtR (R.r ^ n₁)) t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t)
  /-- 動く面の法線での M1（亀）：左岸で裏。 -/
  label_T_left : ∀ t ∈ Icc 0 (2 * R.tstar), R.r * R.g t ≤ -R.r ^ n₁ →
    Back (dynT R w₀ F (VtR (R.r ^ n₁)) t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t)
  /-- 動く面の法線での M1（アキレス）：右岸で裏。 -/
  label_A_right : ∀ t ∈ Icc 0 (2 * R.tstar), R.r ^ n₁ ≤ R.g t →
    Back (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
      (-dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
  /-- 動く面の法線での M1（アキレス）：左岸で表。 -/
  label_A_left : ∀ t ∈ Icc 0 (2 * R.tstar), R.g t ≤ -R.r ^ n₁ →
    Front (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
      (-dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
  /-- 亀のラベルが入れ替わる時刻があり、そのとき亀は首の中にいる。 -/
  label_zero_T : ∃ t ∈ Ioo 0 (2 * R.tstar), |R.r * R.g t| < R.r ^ n₁ ∧
    side (dynT R w₀ F (VtR (R.r ^ n₁)) t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t) = 0
  /-- アキレスのラベルが入れ替わる時刻があり、そのときアキレスは首の中にいる。 -/
  label_zero_A : ∃ t ∈ Ioo 0 (2 * R.tstar), |R.g t| < R.r ^ n₁ ∧
    side (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)
      (-dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) = 0
  /-- (P1)：亀が立つ側と動く面の法線の内積の符号は全時刻で変わらない。 -/
  intrinsic_T : ∀ n : ℝ → V3, Continuous n → (∀ t, n t ≠ wp) →
    (∀ t, cross (n t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t) = wp) →
    (∀ t, 0 < dot (n t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t)) ∨
      (∀ t, dot (n t) (dynNT R w₀ F (VtR (R.r ^ n₁)) t) < 0)
  /-- (P1)：アキレスについて同様。 -/
  intrinsic_A : ∀ n : ℝ → V3, Continuous n → (∀ t, n t ≠ wp) →
    (∀ t, cross (n t) (dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) = wp) →
    (∀ t, 0 < dot (n t) (dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t)) ∨
      (∀ t, dot (n t) (dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t) < 0)
  /-- 右のホーンは族のどの段でも動かない。 -/
  horn_right : ∀ s w v : ℝ, w₀ ≤ w → w ≤ 1 → F s w v = G w v
  /-- 左のホーンは族のどの段でも動かない。 -/
  horn_left : ∀ s w v : ℝ, -1 ≤ w → w ≤ -w₀ → F s w v = G w (π - v)
  /-- 各段の M1：族のどの段でも、どの連続な法線場についても両岸のラベルは逆である。 -/
  reversal_all : ∀ (s : ℝ) (n : ℝ × ℝ → V3), IsNormalField (F s) n → ∀ w₁ w₂ v₁ v₂ : ℝ,
    w₀ ≤ w₁ → w₁ ≤ 1 → -1 ≤ w₂ → w₂ ≤ -w₀ →
    side (F s w₁ v₁) (n (w₁, v₁)) * side (F s w₂ v₂) (n (w₂, v₂)) < 0
  /-- 中央円の各点について、side が 0 になる段がある。 -/
  flips_stage : ∀ v : ℝ, ∃ s ∈ Ioo (0 : ℝ) 1, side (F s 0 v) (XF F s 0 v) = 0
  /-- 商曲面 M の上の M2：どの段でも、M の上に連続で消えない法線場はない。 -/
  one_sided_M : ∀ s : ℝ, ¬ ∃ n : KleinM → V3, Continuous n ∧ (∀ x, n x ≠ wp) ∧
    (∀ p : ℝ × ℝ, cross (n (toM p)) (XF F s p.1 p.2) = wp)
  /-- 各段 F_s は Γ 不変である。 -/
  deck_F : ∀ (s : ℝ) (k m : ℤ) (p : ℝ × ℝ), F s (gam k m p).1 (gam k m p).2 = F s p.1 p.2
  /-- 動く面の法線は Γ 同変である。 -/
  deck_X : ∀ (s : ℝ) (k m : ℤ) (p : ℝ × ℝ),
    XF F s (gam k m p).1 (gam k m p).2 = sgn k • XF F s p.1 p.2
  /-- D7：動的な F の上では t∗ で x̂(T) > 0 > x̂(A)（静的な等式は成り立たない）。 -/
  xhat_sign : 0 < xhat (dynT R w₀ F (VtR (R.r ^ n₁)) R.tstar) ∧
    xhat (dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) R.tstar) < 0
  /-- D4：動く面の上の亀は全時刻で ℘ を通らない。 -/
  avoids_T : ∀ t ∈ Icc 0 (2 * R.tstar), dynT R w₀ F (VtR (R.r ^ n₁)) t ≠ wp
  /-- D4：動く面の上のアキレスは全時刻で ℘ を通らない。 -/
  avoids_A : ∀ t ∈ Icc 0 (2 * R.tstar), dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁) t ≠ wp

/-- **`DynamicPassage` から全効果が従う**（ε < bb₀ は D7 の動的な比較にだけ使う）。 -/
theorem DynamicPassage.effects {R : Race} {w₀ ε : ℝ} {n₁ : ℕ} {F : ℝ → ℝ → ℝ → V3}
    (h0 : 0 < w₀) (h1 : w₀ < 1) (hc : w₀ ≤ R.r ^ n₁) (hn : 1 ≤ n₁)
    (P : DynamicPassage R w₀ (R.r ^ n₁) ε n₁ (Shat w₀) (Xhat w₀) F (VtR (R.r ^ n₁))
      (VaR R.r w₀ (R.r ^ n₁) n₁)) (hε : ε < BB w₀ 0) : DynamicEffects R w₀ n₁ F where
  normal_start := fun _ w v hs => XF_of_start P.eversion hs w v
  normal_shore := fun s _ v hw hw2 => XF_of_shore h1 P.eversion s hw hw2 v
  normal_finish := fun _ _ v hs hw => XF_of_finish h0 h1 P.eversion hs hw v
  normal_cont := continuous_XF_joint P.eversion
  carry_T := ⟨continuous_dynNT R n₁ P.eversion, dynNT_ne R n₁ P.eversion⟩
  carry_A := ⟨continuous_dynNA R h0 n₁ P.eversion, dynNA_ne R n₁ P.eversion⟩
  label_T_right := fun _ ht hw => P.side_T_right_dyn h0 h1 hc ht hw
  label_T_left := fun _ ht hw => P.side_T_left_dyn h0 h1 hc ht hw
  label_A_right := fun _ ht hw => P.side_A_right_dyn h0 h1 hc ht hw
  label_A_left := fun _ ht hw => P.side_A_left_dyn h0 h1 hc ht hw
  label_zero_T := P.side_zero_T h0 h1 hc hn
  label_zero_A := P.side_zero_A h0 h1 hc
  intrinsic_T := fun _ hn' hn0 hpar => dyn_intrinsic_T R n₁ P.eversion hn' hn0 hpar
  intrinsic_A := fun _ hn' hn0 hpar => dyn_intrinsic_A R h0 n₁ P.eversion hn' hn0 hpar
  horn_right := fun s _ v hw hw1 => F_horn_right h0 h1 P.eversion s hw hw1 v
  horn_left := fun s _ v hw1 hw => F_horn_left h0 h1 P.eversion s hw1 hw v
  reversal_all := fun s _ hn' _ _ v₁ v₂ h₁ h₁' h₂ h₂' =>
    reversal_all h0 h1 P.eversion s hn' h₁ h₁' h₂ h₂' v₁ v₂
  flips_stage := flips_stage h0 h1 P.eversion
  one_sided_M := FM_one_sided P.eversion
  deck_F := F_gam P.eversion
  deck_X := XF_gam P.eversion
  xhat_sign := P.xhat_sign hε
  avoids_T := fun _ ht => P.runner_T_ne_wp h0 h1 (hε.trans (BB_zero_lt_en h0 h1)) ht
  avoids_A := fun _ ht => P.runner_A_ne_wp h0 h1 (hε.trans (BB_zero_lt_en h0 h1)) ht

/-- **同じ F の上の全効果**：n₁ ≥ 1、ε > 0 について、`DynamicPassage`（近さ ε）と `DynamicEffects` を
ともに満たす F がある。裏返しは ε′ := min(ε, bb₀/2) で取り、`DynamicPassage.mono` で ε に戻す。 -/
theorem dynamic_effects (R : Race) {n₁ : ℕ} (hn : 1 ≤ n₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℝ → ℝ → ℝ → V3,
      DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ (Shat (R.r ^ n₁)) (Xhat (R.r ^ n₁)) F
        (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) ∧
      DynamicEffects R (R.r ^ n₁) n₁ F := by
  have h0 : 0 < R.r ^ n₁ := pow_pos R.r_pos n₁
  have h1 : R.r ^ n₁ < 1 := R.pow_lt_one hn
  have hBB : 0 < BB (R.r ^ n₁) 0 := BB_pos h0 h1 0
  have hε' : 0 < min ε (BB (R.r ^ n₁) 0 / 2) := lt_min hε (half_pos hBB)
  obtain ⟨F, P⟩ := dynamic_passage R hn hε'
  refine ⟨F, P.mono h0 hε'.le (min_le_left _ _), P.effects h0 h1 le_rfl hn ?_⟩
  have := min_le_right ε (BB (R.r ^ n₁) 0 / 2)
  linarith

/-- **K3⁺ の帰結の束**。 -/
structure KleinSynthesis (R : Race) : Prop where
  /-- 静的な束と K3⁺（`mathemagical_klein`）。 -/
  klein : KleinTheorem R
  /-- 同じ F の上の全効果。 -/
  effects : ∀ n₁ : ℕ, 1 ≤ n₁ → ∀ ε : ℝ, 0 < ε → ∃ F : ℝ → ℝ → ℝ → V3,
    DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ (Shat (R.r ^ n₁)) (Xhat (R.r ^ n₁)) F
      (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) ∧
    DynamicEffects R (R.r ^ n₁) n₁ F
  /-- D7：動的な基底の比較。x̂ の差は 2bb₀/N₀ > 0、断面の差は 0、回転枠 rot2(−π/2) では静的な位置。 -/
  d7_base : ∀ n₁ : ℕ, 1 ≤ n₁ →
    (xhat (baseT R (R.r ^ n₁) (R.r ^ n₁) R.tstar) -
        xhat (baseA R (R.r ^ n₁) (R.r ^ n₁) n₁ R.tstar) =
          2 * BB (R.r ^ n₁) 0 / (AA (R.r ^ n₁) 0 ^ 2 + BB (R.r ^ n₁) 0 ^ 2) ∧
      0 < 2 * BB (R.r ^ n₁) 0 / (AA (R.r ^ n₁) 0 ^ 2 + BB (R.r ^ n₁) 0 ^ 2)) ∧
    (baseT R (R.r ^ n₁) (R.r ^ n₁) R.tstar).2 -
        (baseA R (R.r ^ n₁) (R.r ^ n₁) n₁ R.tstar).2 = ((0 : ℝ), (0 : ℝ)) ∧
    rot2 (-(π / 2)) (baseT R (R.r ^ n₁) (R.r ^ n₁) R.tstar) =
        R.runT (Shat (R.r ^ n₁)) (VtR (R.r ^ n₁)) R.tstar ∧
    rot2 (-(π / 2)) (baseA R (R.r ^ n₁) (R.r ^ n₁) n₁ R.tstar) =
        R.runA (Shat (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) R.tstar
  /-- 量化の順序（動的）：面の族と導線を固定して、すべての段階数を実現することはできない。 -/
  no_uniform : ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (F : ℝ → ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
    ∀ n₁ : ℕ, ∃ c ε : ℝ, DynamicPassage R w₀ c ε n₁ S X F Vt Va
  /-- 量化の順序（静的）。 -/
  no_uniform_static : ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
    ∀ n₁ : ℕ, ∃ c : ℝ, KleinPassage R w₀ c n₁ S X Vt Va
  /-- 理想化の極限：全効果を満たす F_n の列で、走者が [0, 2t∗] の上で理想形に一様に収束するものがある。 -/
  limit : ∃ F : ℕ → ℝ → ℝ → ℝ → V3,
    (∀ n : ℕ, 1 ≤ n →
      DynamicPassage R (R.r ^ n) (R.r ^ n) (R.r ^ n) n (Shat (R.r ^ n)) (Xhat (R.r ^ n)) (F n)
        (VtR (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n) ∧
      DynamicEffects R (R.r ^ n) n (F n)) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ t ∈ Icc 0 (2 * R.tstar),
      nsq (dynT R (R.r ^ n) (F n) (VtR (R.r ^ n)) t - R.idealT t) < (4 * R.r ^ n) ^ 2 ∧
      nsq (dynA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n) t - R.idealA t) <
        (4 * R.r ^ n) ^ 2) ∧
    TendstoUniformlyOn (fun n => dynT R (R.r ^ n) (F n) (VtR (R.r ^ n))) R.idealT atTop
      (Icc 0 (2 * R.tstar)) ∧
    TendstoUniformlyOn (fun n => dynA R (R.r ^ n) (F n) (VaR R.r (R.r ^ n) (R.r ^ n) n))
      R.idealA atTop (Icc 0 (2 * R.tstar))
  /-- 極限の理想形では、t∗ に二人は同じ点にいる（定理 10.1 による強制）。 -/
  limit_meet : R.idealT R.tstar = R.idealA R.tstar
  /-- 窓の両端は t∗ に、首を含む球の半径は 0 に収束する。 -/
  window : Tendsto (fun n : ℕ => t1 R (R.r ^ n)) atTop (𝓝 R.tstar) ∧
    Tendsto (fun n : ℕ => t2 R (R.r ^ n)) atTop (𝓝 R.tstar) ∧
    Tendsto (fun n : ℕ => 2 * R.r ^ n) atTop (𝓝 0)
  /-- Γ の作用：合成則、自由性、一様な離散性、基本領域、Ŝ の不変性。 -/
  deck : (∀ (k m k' m' : ℤ) (p : ℝ × ℝ),
      gam k m (gam k' m' p) = gam (k + k') (m + sgnZ k * m') p) ∧
    (∀ (k m : ℤ) (p : ℝ × ℝ), gam k m p = p → k = 0 ∧ m = 0) ∧
    (∀ k m : ℤ, k ≠ 0 ∨ m ≠ 0 → ∀ p : ℝ × ℝ, 4 ≤ dist (gam k m p) p) ∧
    (∀ p : ℝ × ℝ, ∃ k m : ℤ, (gam k m p).1 ∈ Ico (-1 : ℝ) 3 ∧
      (gam k m p).2 ∈ Ico (0 : ℝ) (2 * π)) ∧
    (∀ (w₀ : ℝ) (k m : ℤ) (p : ℝ × ℝ), Shat w₀ (gam k m p).1 (gam k m p).2 = Shat w₀ p.1 p.2)
  /-- 商曲面 M = ℝ²/Γ：コンパクトなハウスドルフ空間で、被覆写像は連続な開写像であり、半径 2 の開球の上で
  単射である。Ŝ は M からの連続写像に降下し、M の上に連続で消えない法線場はない（M の上の M2）。 -/
  quotient : CompactSpace KleinM ∧ T2Space KleinM ∧ Continuous toM ∧ IsOpenMap toM ∧
    (∀ p : ℝ × ℝ, InjOn toM (ball p 2)) ∧
    (∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 → Continuous (ShatM w₀) ∧
      ¬ ∃ n : KleinM → V3, Continuous n ∧ (∀ x, n x ≠ wp) ∧
        (∀ p : ℝ × ℝ, cross (n (toM p)) (Xhat w₀ p.1 p.2) = wp))

end Zeno.Smale

namespace Zeno

open Zeno.Model Zeno.Smale Real Set Filter Topology

/-- **K3⁺ の帰結の束の定理**。 -/
theorem mathemagical_klein_synthesis (R : Race) : KleinSynthesis R where
  klein := mathemagical_klein R
  effects := fun _ hn _ hε => dynamic_effects R hn hε
  d7_base := fun n₁ hn => by
    have h0 : 0 < R.r ^ n₁ := pow_pos R.r_pos n₁
    have h1 : R.r ^ n₁ < 1 := R.pow_lt_one hn
    obtain ⟨hT, hA⟩ := base_rotated_frame R h0 h1 (le_refl (R.r ^ n₁)) n₁
    exact ⟨base_xhat_sep R h0 h1 h0 n₁, base_cross_section R h0 h0 n₁, hT, hA⟩
  no_uniform := no_uniform_dynamic_passage R
  no_uniform_static := no_uniform_klein_passage R
  limit := by
    have hex : ∀ n : ℕ, ∃ F : ℝ → ℝ → ℝ → V3, 1 ≤ n →
        DynamicPassage R (R.r ^ n) (R.r ^ n) (R.r ^ n) n (Shat (R.r ^ n)) (Xhat (R.r ^ n)) F
          (VtR (R.r ^ n)) (VaR R.r (R.r ^ n) (R.r ^ n) n) ∧
        DynamicEffects R (R.r ^ n) n F := by
      intro n
      by_cases hn : 1 ≤ n
      · obtain ⟨F, P⟩ := dynamic_effects R hn (pow_pos R.r_pos n)
        exact ⟨F, fun _ => P⟩
      · exact ⟨fun _ _ _ => wp, fun h => absurd h hn⟩
    choose F hF using hex
    exact ⟨F, hF, dynamic_tendstoUniformlyOn R (fun n hn => (hF n hn).1)⟩
  limit_meet := ideal_coincidence_forced R
  window := klein_window_tendsto R
  deck := ⟨gam_comp, fun _ _ _ h => gam_free h, fun _ _ h p => four_le_dist_gam h p,
    exists_gam_mem_fundamental, Shat_gam⟩
  quotient := ⟨inferInstance, inferInstance, continuous_toM, isOpenMap_toM, toM_injOn_ball,
    fun _ h0 h1 => ⟨continuous_ShatM h0 h1, ShatM_one_sided h0 h1⟩⟩

end Zeno
