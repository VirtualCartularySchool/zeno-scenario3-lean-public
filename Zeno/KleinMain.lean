/-
# Zeno.KleinMain : クラインの壺型閉包の静的な束（h 原理を使わない部分）

構成 K（K-a〜K-e）、定理 K1（M の上の走者と M1・M2）、定理 K2（二つの貼り合わせ）、
命題 S（自己交差の位置）、D7 の検査の静的な小補題、基底の t∗ での位置と回転の対応を一つに束ねる。
定理 K3⁺（首の動的な裏返し）は `ZenoSmale.KleinMain` の `KleinTheorem` で加える。

量化は ∃M ∀n₁ ∃(Ŝ, 走者) である。M = ℝ²/Γ は L = 4 で固定し、Ŝ は w₀ = c = rⁿ¹ に依存する。
-/
import Zeno.KleinLocation
import Zeno.KleinBridge
import Zeno.KleinBase

noncomputable section

namespace Zeno

open Zeno.Model Real Set

/-- **クラインの壺型閉包の静的な束**。 -/
structure KleinStatic (R : Race) : Prop where
  /-- 構成 K：Ŝ は K-a〜K-c と口の条件を満たす。 -/
  surface : ∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 → IsKleinSurface w₀ (Shat w₀) (Xhat w₀)
  /-- K-d：法線の降下。 -/
  normal_glide : ∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 → ∀ w v, Xhat w₀ (w + 4) (-v) = -Xhat w₀ w v
  /-- K-e：Γ と両立する連続で消えない法線場はない。 -/
  one_sided : ∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 →
    ¬ ∃ n : ℝ × ℝ → V3, Continuous n ∧ (∀ p, n p ≠ wp) ∧
      (∀ p, cross (n p) (Xhat w₀ p.1 p.2) = wp) ∧
      (∀ w v, n (w + 4, -v) = n (w, v)) ∧ (∀ w v, n (w, v + 2 * π) = n (w, v))
  /-- K2：𝒯 閉包は二側であり、M1 は不成立である。 -/
  bridge : ∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 →
    (∃ n : ℝ × ℝ → V3, Continuous n ∧ (∀ p, n p ≠ wp) ∧
      (∀ p, cross (n p) (XhatT w₀ p.1 p.2) = wp) ∧
      (∀ w v, n (w + 4, v) = n (w, v)) ∧ (∀ w v, n (w, v + 2 * π) = n (w, v))) ∧
    (∀ n, IsNormalField (ShatT w₀) n → ∀ w₁ w₂ v₁ v₂, w₀ < w₁ → w₁ ≤ 1 → -1 ≤ w₂ → w₂ < -w₀ →
      0 < side (ShatT w₀ w₁ v₁) (n (w₁, v₁)) * side (ShatT w₀ w₂ v₂) (n (w₂, v₂)))
  /-- 命題 S：S1（外側の単射性）、S2（首は球の中、外側は外）、S4（首の繊維）。 -/
  location : ∀ w₀ : ℝ, 0 < w₀ → w₀ < 1 →
    (∀ w w' v v', w₀ ≤ w → w ≤ 4 - w₀ → w₀ ≤ w' → w' ≤ 4 - w₀ →
      Shat w₀ w v = Shat w₀ w' v' → w = w' ∧ ∃ k : ℤ, v' = v + k * (2 * π)) ∧
    (∀ w v, |w| < w₀ → nsq (Shat w₀ w v) < nsq (G w₀ 0)) ∧
    (∀ w v, w₀ ≤ w → w ≤ 4 - w₀ → nsq (G w₀ 0) ≤ nsq (Shat w₀ w v) ∧
      (nsq (G w₀ 0) = nsq (Shat w₀ w v) → w = w₀ ∨ w = 4 - w₀)) ∧
    (∀ w w' v v', |w| ≤ w₀ → |w'| ≤ w₀ → Sig w₀ w v = Sig w₀ w' v' →
      (w' = w ∨ w' = -w) ∧ (w' = w → ∃ k : ℤ, v' = v + k * (2 * π)))
  /-- 定理 K1：n₁ ≥ 1 の各段階数について、同じ源曲面 Ŝ の上の走者と M1・M2。 -/
  passage : ∀ n₁ : ℕ, 1 ≤ n₁ →
    KleinPassage R (R.r ^ n₁) (R.r ^ n₁) n₁ (Shat (R.r ^ n₁)) (Xhat (R.r ^ n₁))
      (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁)
  /-- (2″)：t∗ で x̂(T) = x̂(A)（静的）。 -/
  compare_xhat : ∀ n₁ : ℕ, 1 ≤ n₁ →
    xhat (R.runT (Shat (R.r ^ n₁)) (VtR (R.r ^ n₁)) R.tstar) =
      xhat (R.runA (Shat (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) R.tstar)
  /-- (1″)：t∗ で断面の座標の差は (0, 2 bb₀) ≠ 0（静的）。 -/
  cross_section : ∀ n₁ : ℕ, 1 ≤ n₁ →
    (R.runT (Shat (R.r ^ n₁)) (VtR (R.r ^ n₁)) R.tstar).2 -
      (R.runA (Shat (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) R.tstar).2 =
        ((0 : ℝ), 2 * BB (R.r ^ n₁) 0) ∧ 0 < BB (R.r ^ n₁) 0
  /-- 基底の t∗ での位置（正確）。 -/
  base_tstar : ∀ n₁ : ℕ, 1 ≤ n₁ →
    baseT R (R.r ^ n₁) (R.r ^ n₁) R.tstar = (BB (R.r ^ n₁) 0, 0, AA (R.r ^ n₁) 0) ∧
    baseA R (R.r ^ n₁) (R.r ^ n₁) n₁ R.tstar = (-(BB (R.r ^ n₁) 0), 0, AA (R.r ^ n₁) 0)
  /-- 回転の対応：t∗ で基底の位置は静的な位置を rot2(π/2) で回したもの（正確）。 -/
  dyn_rotation : ∀ n₁ : ℕ, 1 ≤ n₁ →
    baseT R (R.r ^ n₁) (R.r ^ n₁) R.tstar =
        rot2 (π / 2) (R.runT (Shat (R.r ^ n₁)) (VtR (R.r ^ n₁)) R.tstar) ∧
      baseA R (R.r ^ n₁) (R.r ^ n₁) n₁ R.tstar =
        rot2 (π / 2) (R.runA (Shat (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) R.tstar)

theorem Model.Race.pow_lt_one (R : Race) {n₁ : ℕ} (hn : 1 ≤ n₁) : R.r ^ n₁ < 1 :=
  pow_lt_one₀ R.r_pos.le R.r_lt_one (by omega)

/-- **クラインの壺型閉包の静的な束の定理**。 -/
theorem mathemagical_klein_static (R : Race) : KleinStatic R where
  surface := fun _ h0 h1 => Shat_isKlein h0 h1
  normal_glide := fun _ h0 h1 w v => Xhat_glide h0 h1 w v
  one_sided := fun _ h0 h1 =>
    no_equivariant_normal (continuous_Xhat h0 h1) (Xhat_ne h0 h1) (Xhat_glide h0 h1)
  bridge := fun _ h0 h1 =>
    ⟨ShatT_two_sided h0 h1, fun _ hn _ _ v₁ v₂ h₁ h₁' h₂ h₂' =>
      ShatT_no_reversal h0 h1 hn h₁ h₁' h₂ h₂' v₁ v₂⟩
  location := fun _ h0 h1 =>
    ⟨fun _ _ _ _ hw1 hw2 hw1' hw2' he => outer_injective h0 h1 hw1 hw2 hw1' hw2' he,
      fun _ v hw => neck_inside h0 h1 hw v,
      fun _ v hw1 hw2 => outer_outside h0 h1 hw1 hw2 v,
      fun _ _ _ _ hw hw' he => neck_fibre h0 h1 hw hw' he⟩
  passage := fun n₁ hn =>
    klein_passage R (pow_pos R.r_pos n₁) (R.pow_lt_one hn) n₁ le_rfl
  compare_xhat := fun n₁ hn =>
    Model.compare_xhat R (pow_pos R.r_pos n₁) (R.pow_lt_one hn) n₁ le_rfl
  cross_section := fun n₁ hn =>
    Model.cross_section R (pow_pos R.r_pos n₁) (R.pow_lt_one hn) n₁ le_rfl
  base_tstar := fun n₁ _ =>
    Model.base_tstar (pow_pos R.r_pos n₁) R (pow_pos R.r_pos n₁) n₁
  dyn_rotation := fun n₁ hn =>
    base_rotation (pow_pos R.r_pos n₁) (R.pow_lt_one hn) R le_rfl n₁

end Zeno
