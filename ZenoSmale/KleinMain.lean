/-
# ZenoSmale.KleinMain : クラインの壺型閉包の束（定理 K3⁺ を含む）

`Zeno.KleinStatic`（構成 K、K1、K2、命題 S、基底）に、首の動的な裏返し（定理 K3⁺、`DynamicPassage`）、
理想化 ε = rⁿ¹（G6-6）、t∗ での分離 (2 bb₀, 0, 0) を加える。

`dynamic` の F は `start` で Ŝ に一致し、`static_before`・`static_after` で `passage` の走者に接続し、
`one_sided_all` で `surface` の一側性を各段に運び、`flips_middle` で中央円の外在的な側の反転を与える。
`idealization`・`dyn_separation` は `dynamic` の実例（ε の選択）と算術である。

`mathemagical_complete`（定理 1.1・1.2）は変えない。`mathemagical_klein` は別の定理である。
-/
import Zeno.KleinMain
import ZenoSmale.KleinDynamic

noncomputable section

namespace Zeno

open Zeno.Model Zeno.Smale Real Set

/-- **クラインの壺型閉包の束**（第 3 版 §2.10）。静的な束 `KleinStatic` を拡張する。 -/
structure KleinTheorem (R : Race) : Prop extends KleinStatic R where
  /-- 定理 K3⁺：n₁ ≥ 1 と ε > 0 について、w₀ = c = rⁿ¹ の首の裏返し F で `DynamicPassage` が成り立つ。 -/
  dynamic : ∀ n₁ : ℕ, 1 ≤ n₁ → ∀ ε : ℝ, 0 < ε →
    ∃ F : ℝ → ℝ → ℝ → V3, DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ (Shat (R.r ^ n₁))
      (Xhat (R.r ^ n₁)) F (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁)
  /-- 理想化（G6-6）：ε = rⁿ¹。裏返しは半径 2rⁿ¹ の球の中で、幅 t∗rⁿ¹/2 の窓の中で起きる。 -/
  idealization : ∀ n₁ : ℕ, 1 ≤ n₁ →
    ∃ F : ℝ → ℝ → ℝ → V3, DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) (R.r ^ n₁) n₁ (Shat (R.r ^ n₁))
      (Xhat (R.r ^ n₁)) F (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) ∧
      (∀ s w v : ℝ, |w| ≤ R.r ^ n₁ → nsq (F s w v) < (2 * R.r ^ n₁) ^ 2) ∧
      t2 R (R.r ^ n₁) - t1 R (R.r ^ n₁) = R.tstar * R.r ^ n₁ / 2
  /-- t∗ での分離：F の上の二人の差は (2 bb₀, 0, 0) に 2ε で近い。 -/
  dyn_separation : ∀ n₁ : ℕ, 1 ≤ n₁ → ∀ ε : ℝ, 0 < ε →
    ∃ F : ℝ → ℝ → ℝ → V3, DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ (Shat (R.r ^ n₁))
      (Xhat (R.r ^ n₁)) F (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) ∧
      √(nsq (dynT R (R.r ^ n₁) F (VtR (R.r ^ n₁)) R.tstar -
        dynA R (R.r ^ n₁) F (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) R.tstar -
          (2 * BB (R.r ^ n₁) 0, 0, 0))) ≤ 2 * ε

/-- **クラインの壺型閉包の定理**。 -/
theorem mathemagical_klein (R : Race) : KleinTheorem R :=
  { mathemagical_klein_static R with
    dynamic := fun _ hn _ hε => dynamic_passage R hn hε
    idealization := fun n₁ hn => by
      obtain ⟨F, P⟩ := dynamic_passage R hn (pow_pos R.r_pos n₁)
      refine ⟨F, P, fun s w v hw => ?_, t2_sub_t1 R⟩
      have h := P.eversion.ball s w v hw
      rwa [two_mul]
    dyn_separation := fun _ hn _ hε => by
      obtain ⟨F, P⟩ := dynamic_passage R hn hε
      exact ⟨F, P, P.separation⟩ }

end Zeno
