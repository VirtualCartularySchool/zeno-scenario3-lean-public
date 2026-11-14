/-
# ZenoSmale.M2 : 読み M2 の定理（内在的な表裏の交換）

M2 は「走者が、面に沿って連続に運んだ自分の側を保ったまま、面の同じ点に反対の側で戻る」
ことである（閉路に沿った法線のモノドロミー）。

1. 必要性：面が両側なら（連続な法線場があれば）M2 は起きない（`two_sided_no_exchange`）。
2. 実現：平面 α（§8 の γ）を射影平面 α̂ = α ∪（無限遠直線）に完備化し、無限遠直線のまわりを
   芯の模型 C で閉じた正則なはめ込みがある（h 原理）。α̂ は一つの側しか持たず、
   その上で亀はホーンの表から同じホーンの裏へ、アキレスは裏から表へ移る。二人は全時刻で
   衝突せず、t∗ には無限遠直線を別々の点で横切る。

主定理 `MainTheorem` の文は変えていない。M2 の定理は別の構造体 `M2Theorem` である。
-/
import ZenoSmale.Main
import ZenoSmale.Mobius
import Zeno.MobiusPassage

noncomputable section

namespace Zeno

open Set Function Filter
open scoped Topology ContDiff
open Zeno.Model Zeno.Smale Real

/-- **定理 M2**：競走 R についての、読み M2 の必要性と実現。 -/
structure M2Theorem (R : Race) : Prop where
  /-- 両側の面では M2 は起きない：連続な法線場 N₀ のある面の上で、閉じた道に沿って連続に
  運んだ側は、正の倍で元に戻る。 -/
  obstruction : ∀ {α : Type} [TopologicalSpace α] {N₀ : α → V3}, Continuous N₀ →
    (∀ p, N₀ p ≠ wp) → ∀ {γ : ℝ → α}, Continuous γ → ∀ {n : ℝ → V3}, Continuous n →
    (∀ s, n s ≠ wp) → (∀ s, cross (n s) (N₀ (γ s)) = wp) → γ 1 = γ 0 →
    ∃ κ : ℝ, 0 < κ ∧ n 1 = κ • n 0
  /-- 理想形の折り返し：ホーン対の鏡映は円柱の対合 τ(w, v) = (−w, v + π) で表され、
  鏡映で折り返したホーンは τ で不変である。 -/
  fold : ∀ w v, G (-w) (v + π) = mirror (G w v) ∧ foldG (-w) (v + π) = foldG w v
  /-- 芯の模型ははめ込みで、τ で不変である。 -/
  core_model : ∀ k : ℝ, k ≠ 0 → ∀ w v, mobC k (-w) (v + π) = mobC k w v ∧
    cross (mobCv k w v) (mobCw v) ≠ wp
  /-- **射影平面の面とその上の走者**：任意の段数 n₁ ≥ 1 について、平面 α のはめ込み f
  （中心とホーンでは §8 の γ）と、円柱の上の面 S（w ≠ 0 で S(w, v) = f(e^{iv}/w)、
  無限遠直線の近くで芯の模型）があり、S の上で定理 M2 の走者の結論が成り立つ。 -/
  projective : ∀ n₁ : ℕ, 1 ≤ n₁ → ∃ (f : ℝ × ℝ → V3) (S X : ℝ → ℝ → V3),
    IsMobPlane (R.mkc n₁) (R.mδ n₁) (R.mw n₁) (R.mε n₁) f ∧
    (∀ y, tau y ≤ mT0 (R.mw n₁) → f y = planeG y) ∧
    (∀ w v, w ≠ 0 → S w v = f (Ypp (w, v))) ∧
    (∀ w v, |w| ≤ R.mδ n₁ → S w v = mobC (R.mkc n₁) w v) ∧
    MobiusPassage R n₁ S X

/-- **定理 M2 の証明**。 -/
theorem mathemagical_m2 (R : Race) : M2Theorem R where
  obstruction := fun hN hN0 _ hγ _ hn hn0 hpar hloop =>
    two_sided_no_exchange hN hN0 hγ hn hn0 hpar hloop
  fold := fun w v => ⟨G_mirror w v, foldG_deck w v⟩
  core_model := fun k hk w v => ⟨mobC_deck k w v, mobC_cross_ne hk w v⟩
  projective := by
    intro n₁ hn
    have hok := R.mok hn
    obtain ⟨f, hf1, hf2, hf3, hf4⟩ := mob_plane hok (R.mε_pos (n₁ := n₁))
    have hf : IsMobPlane (R.mkc n₁) (R.mδ n₁) (R.mw n₁) (R.mε n₁) f := ⟨hf1, hf2, hf3, hf4⟩
    refine ⟨f, mobS f (R.mkc n₁), mobX f (R.mkc n₁), hf, ?_, ?_, ?_, ?_⟩
    · intro y hy
      rw [hf3 y (Or.inl hy), bsM_eq_planeG hok (by linarith [hok.dl_pos])]
    · intro w v hw
      simp only [mobS, hw, ite_false]
    · intro w v hw
      exact mobS_core hok hf hw v
    · exact mobius_passage hn (mobS_isMobius hok hf)

/-- **完成した主定理**：定理 1.1（読み M1）と定理 M2（読み M2）。 -/
theorem mathemagical_complete (R : Race) : MainTheorem R ∧ M2Theorem R :=
  ⟨mathemagical_main R, mathemagical_m2 R⟩

end Zeno
