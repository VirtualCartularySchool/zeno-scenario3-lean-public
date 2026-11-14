/-
# ZenoSmale.KleinStages : 量化の訂正 — 固定した構成が実現する段階数は有界である

`KleinIdeal` の `no_uniform_dynamic_passage`、`no_uniform_klein_passage` は

  ¬ ∃ 構成, ∀ n₁ : ℕ, ∃ …, 通過(n₁)

の形であり、段階数 0 を含むすべての自然数についての実現を否定する。本文の主張は正の段階数だけについての
実現の否定

  ¬ ∃ 構成, ∀ n₁ ≥ 1, ∃ …, 通過(n₁)

であり、こちらのほうが強い。この二つの文は一般には同値でない。本ファイルは強い形を証明する。

1. **親補題**（`no_unbounded_dynamic_passage`、`no_unbounded_klein_passage`）。首の幅、面、裏返しの族、
   導線を固定すると、非有界な段階数の集合について通過を満たすことはできない。証明は既存のものと同じで
   あり、連続性と非衝突の証人を、仮定が与える任意の一つの段階数から取り、段階 k の等式を k + 1 以上の
   段階数の証人から取る。定理 10.1（`zeno_steps_force_coincidence`）により t∗ で二人が一致し、非衝突に
   反する。段階数 0 の証人は使わない。
2. **正の段階数**（`no_uniform_dynamic_passage_pos`、`no_uniform_klein_passage_pos`）。1 の系。
3. **有界性**（`dynamic_stages_bounded`、`klein_stages_bounded`）。固定した構成が通過を満たす段階数の
   集合は上に有界である。
4. **既存の弱い形**は 2 の系である（`no_uniform_dynamic_passage_of_pos`、
   `no_uniform_klein_passage_of_pos`）。既存の定理の文と証明は変えていない。

射程：否定されるのは、首の幅 w₀、面 S、法線 X、裏返しの族 F、導線 Vt・Va のすべてを固定した場合である
（岸の閾値 c と近さ ε は段階数ごとに変えてよい）。面だけを固定して導線を段階数ごとに変える場合は、
これらの定理の対象ではない。
-/
import ZenoSmale.KleinIdeal

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff
open Zeno.Model

/-! ### 親補題：非有界な段階数の集合は実現できない -/

/-- **親補題（動的）**：首の幅 w₀、面 S、裏返しの族 F、導線 Vt・Va を固定すると、非有界な段階数の集合に
ついて `DynamicPassage` を満たすことはできない（岸の閾値 c と近さ ε は段階数ごとに変えてよい）。 -/
theorem no_unbounded_dynamic_passage (R : Race) :
    ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (F : ℝ → ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
      ∀ N : ℕ, ∃ n₁ : ℕ, N ≤ n₁ ∧ ∃ c ε : ℝ, DynamicPassage R w₀ c ε n₁ S X F Vt Va := by
  rintro ⟨w₀, S, X, F, Vt, Va, h⟩
  obtain ⟨n₀, -, c₀, ε₀, P₀⟩ := h 0
  have hstep : ∀ k, dynA R w₀ F Va (R.tn (k + 1)) = dynT R w₀ F Vt (R.tn k) := by
    intro k
    obtain ⟨n₁, hn, c, ε, P⟩ := h (k + 1)
    exact P.step_before k (Nat.lt_of_succ_le hn)
  have hmeet := all_steps_force_meeting R P₀.smooth_T.continuous.continuousAt
    P₀.smooth_A.continuous.continuousAt hstep
  exact P₀.no_collision R.tstar R.tstar_mem hmeet

/-- **親補題（静的）**：面 S と導線を固定すると、非有界な段階数の集合について `KleinPassage` を満たすことは
できない。 -/
theorem no_unbounded_klein_passage (R : Race) :
    ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
      ∀ N : ℕ, ∃ n₁ : ℕ, N ≤ n₁ ∧ ∃ c : ℝ, KleinPassage R w₀ c n₁ S X Vt Va := by
  rintro ⟨w₀, S, X, Vt, Va, h⟩
  obtain ⟨n₀, -, c₀, P₀⟩ := h 0
  have hstep : ∀ k, R.runA S Va (R.tn (k + 1)) = R.runT S Vt (R.tn k) := by
    intro k
    obtain ⟨n₁, hn, c, P⟩ := h (k + 1)
    exact P.step_before k (Nat.lt_of_succ_le hn)
  have hmeet := all_steps_force_meeting R P₀.smooth_T.continuous.continuousAt
    P₀.smooth_A.continuous.continuousAt hstep
  exact P₀.no_collision R.tstar R.tstar_mem hmeet

/-! ### 正の段階数についての不可能性（本文 §7.2 の文） -/

/-- **量化の順序（動的、正の段階数）**：首の幅 w₀、面 S、裏返しの族 F、導線 Vt・Va を固定して、すべての
正の段階数 n₁ ≥ 1 について `DynamicPassage` を満たすことはできない。 -/
theorem no_uniform_dynamic_passage_pos (R : Race) :
    ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (F : ℝ → ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
      ∀ n₁ : ℕ, 1 ≤ n₁ → ∃ c ε : ℝ, DynamicPassage R w₀ c ε n₁ S X F Vt Va := by
  rintro ⟨w₀, S, X, F, Vt, Va, h⟩
  exact no_unbounded_dynamic_passage R
    ⟨w₀, S, X, F, Vt, Va, fun N => ⟨N + 1, Nat.le_succ N, h (N + 1) (Nat.succ_le_succ (Nat.zero_le N))⟩⟩

/-- **量化の順序（静的、正の段階数）**：面 S と導線を固定して、すべての正の段階数 n₁ ≥ 1 について
`KleinPassage` を満たすことはできない。 -/
theorem no_uniform_klein_passage_pos (R : Race) :
    ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
      ∀ n₁ : ℕ, 1 ≤ n₁ → ∃ c : ℝ, KleinPassage R w₀ c n₁ S X Vt Va := by
  rintro ⟨w₀, S, X, Vt, Va, h⟩
  exact no_unbounded_klein_passage R
    ⟨w₀, S, X, Vt, Va, fun N => ⟨N + 1, Nat.le_succ N, h (N + 1) (Nat.succ_le_succ (Nat.zero_le N))⟩⟩

/-! ### 有界性：固定した構成が実現する段階数の集合は上に有界である -/

/-- **段階数の有界性（動的）**：首の幅、面、裏返しの族、導線を固定すると、`DynamicPassage` を満たす
段階数の集合は上に有界である。 -/
theorem dynamic_stages_bounded (R : Race) (w₀ : ℝ) (S X : ℝ → ℝ → V3) (F : ℝ → ℝ → ℝ → V3)
    (Vt Va : ℝ → ℝ) :
    ∃ N : ℕ, ∀ n₁ : ℕ, (∃ c ε : ℝ, DynamicPassage R w₀ c ε n₁ S X F Vt Va) → n₁ < N := by
  by_contra hcon
  push Not at hcon
  refine no_unbounded_dynamic_passage R ⟨w₀, S, X, F, Vt, Va, fun N => ?_⟩
  obtain ⟨n₁, hP, hn⟩ := hcon N
  exact ⟨n₁, hn, hP⟩

/-- **段階数の有界性（静的）**。 -/
theorem klein_stages_bounded (R : Race) (w₀ : ℝ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ) :
    ∃ N : ℕ, ∀ n₁ : ℕ, (∃ c : ℝ, KleinPassage R w₀ c n₁ S X Vt Va) → n₁ < N := by
  by_contra hcon
  push Not at hcon
  refine no_unbounded_klein_passage R ⟨w₀, S, X, Vt, Va, fun N => ?_⟩
  obtain ⟨n₁, hP, hn⟩ := hcon N
  exact ⟨n₁, hn, hP⟩

/-! ### 既存の弱い形は強い形の系である -/

/-- 既存の `no_uniform_dynamic_passage` の文（すべての自然数についての実現の否定）は、
正の段階数についての不可能性の系である。 -/
theorem no_uniform_dynamic_passage_of_pos (R : Race) :
    ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (F : ℝ → ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
      ∀ n₁ : ℕ, ∃ c ε : ℝ, DynamicPassage R w₀ c ε n₁ S X F Vt Va := by
  rintro ⟨w₀, S, X, F, Vt, Va, h⟩
  exact no_uniform_dynamic_passage_pos R ⟨w₀, S, X, F, Vt, Va, fun n₁ _ => h n₁⟩

/-- 既存の `no_uniform_klein_passage` の文は、正の段階数についての不可能性の系である。 -/
theorem no_uniform_klein_passage_of_pos (R : Race) :
    ¬ ∃ (w₀ : ℝ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ),
      ∀ n₁ : ℕ, ∃ c : ℝ, KleinPassage R w₀ c n₁ S X Vt Va := by
  rintro ⟨w₀, S, X, Vt, Va, h⟩
  exact no_uniform_klein_passage_pos R ⟨w₀, S, X, Vt, Va, fun n₁ _ => h n₁⟩

end Zeno.Smale
