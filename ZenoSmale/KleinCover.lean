/-
# ZenoSmale.KleinCover : 被覆変換群 Γ の作用（被覆空間の辞書の仮定）

源曲面は商 M = ℝ²/Γ である。Γ は T(w, v) = (w, v + 2π) と Ω(w, v) = (w + 4, −v) が生成する群で、
その元は γ_{k,m}(w, v) = (w + 4k, (−1)ᵏ v + 2πm)（k, m ∈ ℤ）である。本ファイルは、商をとるために
必要な事実を被覆平面の上で証明する。商多様体そのものは Lean の型として作らない（本文で述べる）。

- 合成則 γ_{k,m} ∘ γ_{k′,m′} = γ_{k+k′, m+(−1)ᵏm′}、単位元、逆元（群であること）。
- 自由性：γ_{k,m} p = p なら (k, m) = (0, 0)。
- 一様な離散性：(k, m) ≠ (0, 0) なら dist(γ_{k,m} p, p) ≥ 4。したがって半径 2 の球は
  Γ の非自明な元で自分自身と交わらない（均等被覆近傍）。
- 基本領域：どの点も [−1, 3) × [0, 2π) の点に Γ で移る。
- Γ 不変性：Ŝ∘γ = Ŝ、F_s∘γ = F_s。
- 法線の同変性：X̂∘γ_{k,m} = (−1)ᵏ X̂、X_{F,s}∘γ_{k,m} = (−1)ᵏ X_{F,s}。指標 (k, m) ↦ (−1)ᵏ は
  M の向きの指標であり、一側性（`no_equivariant_normal`）はこの指標が自明でないことによる。
-/
import ZenoSmale.KleinNormal

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff
open Zeno.Model

/-! ### 群 Γ -/

/-- (−1)ᵏ（整数値）。 -/
def sgnZ (k : ℤ) : ℤ := if Even k then 1 else -1

theorem sgn_eq_sgnZ (k : ℤ) : sgn k = ((sgnZ k : ℤ) : ℝ) := by
  unfold sgn sgnZ
  split_ifs <;> simp

/-- Γ の元 γ_{k,m}(w, v) = (w + 4k, (−1)ᵏ v + 2πm)。 -/
def gam (k m : ℤ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + 4 * (k : ℝ), sgn k * p.2 + (m : ℝ) * (2 * π))

theorem gam_zero (p : ℝ × ℝ) : gam 0 0 p = p := by
  simp [gam, sgn_zero]

/-- 生成元 T。 -/
theorem gam_T (p : ℝ × ℝ) : gam 0 1 p = (p.1, p.2 + 2 * π) := by
  simp [gam, sgn_zero]

/-- 生成元 Ω。 -/
theorem gam_Omega (p : ℝ × ℝ) : gam 1 0 p = (p.1 + 4, -p.2) := by
  simp [gam, sgn_one]

/-- **合成則**：γ_{k,m} ∘ γ_{k′,m′} = γ_{k+k′, m+(−1)ᵏm′}。 -/
theorem gam_comp (k m k' m' : ℤ) (p : ℝ × ℝ) :
    gam k m (gam k' m' p) = gam (k + k') (m + sgnZ k * m') p := by
  simp only [gam]
  rw [sgn_add]
  refine Prod.ext ?_ ?_
  · push_cast; ring
  · simp only [sgn_eq_sgnZ]
    push_cast
    ring

theorem sgnZ_mul_self (k : ℤ) : sgnZ k * sgnZ k = 1 := by
  unfold sgnZ
  split_ifs <;> simp

theorem sgn_neg (k : ℤ) : sgn (-k) = sgn k := by
  unfold sgn
  simp [even_neg]

/-- **逆元**：γ_{−k, −(−1)ᵏm} ∘ γ_{k,m} = id。 -/
theorem gam_inv (k m : ℤ) (p : ℝ × ℝ) : gam (-k) (-(sgnZ k * m)) (gam k m p) = p := by
  simp only [gam]
  refine Prod.ext ?_ ?_
  · push_cast; ring
  · show sgn (-k) * (sgn k * p.2 + (m : ℝ) * (2 * π)) + ((-(sgnZ k * m) : ℤ) : ℝ) * (2 * π) = p.2
    rw [sgn_neg]
    have h := sgn_mul_self k
    simp only [sgn_eq_sgnZ] at h ⊢
    push_cast
    linear_combination p.2 * h

/-- **自由性**：γ_{k,m} が点を固定するなら単位元である。 -/
theorem gam_free {k m : ℤ} {p : ℝ × ℝ} (h : gam k m p = p) : k = 0 ∧ m = 0 := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [gam] at h1 h2
  have hk : (k : ℝ) = 0 := by linarith
  have hk' : k = 0 := by exact_mod_cast hk
  subst hk'
  simp only [sgn_zero, one_mul] at h2
  have hm : (m : ℝ) * (2 * π) = 0 := by linarith
  have hm' : (m : ℝ) = 0 := by
    rcases mul_eq_zero.mp hm with h | h
    · exact h
    · exfalso; linarith [pi_pos]
  exact ⟨rfl, by exact_mod_cast hm'⟩

/-- **一様な離散性**：非自明な元は、どの点も距離 4 以上動かす。 -/
theorem four_le_dist_gam {k m : ℤ} (h : k ≠ 0 ∨ m ≠ 0) (p : ℝ × ℝ) : 4 ≤ dist (gam k m p) p := by
  rw [Prod.dist_eq]
  by_cases hk : k = 0
  · subst hk
    have hm : m ≠ 0 := by tauto
    refine le_trans ?_ (le_max_right _ _)
    simp only [gam, sgn_zero, one_mul, Real.dist_eq]
    have e : p.2 + (m : ℝ) * (2 * π) - p.2 = (m : ℝ) * (2 * π) := by ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    nlinarith [two_le_pi]
  · refine le_trans ?_ (le_max_left _ _)
    simp only [gam, Real.dist_eq]
    have e : p.1 + 4 * (k : ℝ) - p.1 = 4 * (k : ℝ) := by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast this
    linarith

/-- **均等被覆近傍**：半径 2 の開球は、Γ の非自明な元による像と交わらない。 -/
theorem gam_ball_disjoint {k m : ℤ} (h : k ≠ 0 ∨ m ≠ 0) (p : ℝ × ℝ) {q : ℝ × ℝ}
    (hq : q ∈ ball p 2) : gam k m q ∉ ball p 2 := by
  rw [mem_ball] at hq ⊢
  have h4 := four_le_dist_gam h q
  have htri := dist_triangle (gam k m q) p q
  rw [dist_comm p q] at htri
  linarith

/-- **基本領域**：どの点も、Γ の元で [−1, 3) × [0, 2π) の点に移る。 -/
theorem exists_gam_mem_fundamental (p : ℝ × ℝ) :
    ∃ k m : ℤ, (gam k m p).1 ∈ Ico (-1 : ℝ) 3 ∧ (gam k m p).2 ∈ Ico (0 : ℝ) (2 * π) := by
  have h2π : (0 : ℝ) < 2 * π := by positivity
  refine ⟨-kk p.1, -⌊sgn (-kk p.1) * p.2 / (2 * π)⌋, ?_, ?_⟩
  · have hk := (kk_eq_iff (w := p.1) (k := kk p.1)).mp rfl
    simp only [gam, mem_Ico]
    push_cast
    constructor <;> linarith [hk.1, hk.2]
  · have hlo := Int.sub_floor_div_mul_nonneg (sgn (-kk p.1) * p.2) h2π
    have hhi := Int.sub_floor_div_mul_lt (sgn (-kk p.1) * p.2) h2π
    simp only [gam]
    have e : sgn (-kk p.1) * p.2 + ((-⌊sgn (-kk p.1) * p.2 / (2 * π)⌋ : ℤ) : ℝ) * (2 * π) =
        sgn (-kk p.1) * p.2 - (⌊sgn (-kk p.1) * p.2 / (2 * π)⌋ : ℝ) * (2 * π) := by
      push_cast; ring
    rw [e]
    exact ⟨hlo, hhi⟩

/-! ### Γ 不変な写像と Γ 同変な法線 -/

/-- 滑り鏡映での不変性は、Ω のすべての冪での不変性を導く。 -/
theorem glide_int {G : ℝ → ℝ → V3} (hgl : ∀ w v, G (w + 4) (-v) = G w v) (k : ℤ) (w v : ℝ) :
    G (w + 4 * (k : ℝ)) (sgn k * v) = G w v := by
  induction k using Int.induction_on generalizing w v with
  | zero => simp [sgn_zero]
  | succ i ih =>
    have e1 : w + 4 * (((i : ℤ) + 1 : ℤ) : ℝ) = (w + 4 * ((i : ℤ) : ℝ)) + 4 := by
      push_cast; ring
    rw [e1, sgn_succ, neg_mul, hgl, ih]
  | pred i ih =>
    have h := hgl (w + 4 * ((-(i : ℤ) - 1 : ℤ) : ℝ)) (sgn (-(i : ℤ) - 1) * v)
    have e1 : w + 4 * ((-(i : ℤ) - 1 : ℤ) : ℝ) + 4 = w + 4 * ((-(i : ℤ) : ℤ) : ℝ) := by
      push_cast; ring
    have e2 : -(sgn (-(i : ℤ) - 1) * v) = sgn (-(i : ℤ)) * v := by
      have h3 := sgn_succ (-(i : ℤ) - 1)
      rw [sub_add_cancel] at h3
      rw [h3]; ring
    rw [e1, e2] at h
    rw [← h, ih]

theorem periodic_int_curried {G : ℝ → ℝ → V3} (hper : ∀ w v, G w (v + 2 * π) = G w v) (m : ℤ)
    (w v : ℝ) : G w (v + (m : ℝ) * (2 * π)) = G w v := by
  have hp : Function.Periodic (fun v => G w v) (2 * π) := fun v => hper w v
  exact hp.int_mul m v

/-- **Γ 不変性**：T と Ω で不変な写像は Γ のすべての元で不変である。 -/
theorem invariant_gam {G : ℝ → ℝ → V3} (hper : ∀ w v, G w (v + 2 * π) = G w v)
    (hgl : ∀ w v, G (w + 4) (-v) = G w v) (k m : ℤ) (p : ℝ × ℝ) :
    G (gam k m p).1 (gam k m p).2 = G p.1 p.2 := by
  simp only [gam]
  rw [periodic_int_curried hper, glide_int hgl]

/-- 滑り鏡映で符号を変える場は、Ωᵏ で (−1)ᵏ 倍になる。 -/
theorem glide_int_neg {X : ℝ → ℝ → V3} (hgl : ∀ w v, X (w + 4) (-v) = -X w v) (k : ℤ)
    (w v : ℝ) : X (w + 4 * (k : ℝ)) (sgn k * v) = sgn k • X w v := by
  induction k using Int.induction_on generalizing w v with
  | zero => simp [sgn_zero]
  | succ i ih =>
    have e1 : w + 4 * (((i : ℤ) + 1 : ℤ) : ℝ) = (w + 4 * ((i : ℤ) : ℝ)) + 4 := by
      push_cast; ring
    rw [e1, sgn_succ, neg_mul, hgl, ih, neg_smul]
  | pred i ih =>
    have h := hgl (w + 4 * ((-(i : ℤ) - 1 : ℤ) : ℝ)) (sgn (-(i : ℤ) - 1) * v)
    have e1 : w + 4 * ((-(i : ℤ) - 1 : ℤ) : ℝ) + 4 = w + 4 * ((-(i : ℤ) : ℤ) : ℝ) := by
      push_cast; ring
    have h3 := sgn_succ (-(i : ℤ) - 1)
    rw [sub_add_cancel] at h3
    have e2 : -(sgn (-(i : ℤ) - 1) * v) = sgn (-(i : ℤ)) * v := by
      rw [h3]; ring
    rw [e1, e2, ih] at h
    have h4 : X (w + 4 * ((-(i : ℤ) - 1 : ℤ) : ℝ)) (sgn (-(i : ℤ) - 1) * v) =
        -(sgn (-(i : ℤ)) • X w v) := by
      rw [h, neg_neg]
    rw [h4, h3, neg_smul, neg_neg]

/-- **Γ 同変性**：T で不変、Ω で符号を変える場は、γ_{k,m} で (−1)ᵏ 倍になる。 -/
theorem equivariant_gam {X : ℝ → ℝ → V3} (hper : ∀ w v, X w (v + 2 * π) = X w v)
    (hgl : ∀ w v, X (w + 4) (-v) = -X w v) (k m : ℤ) (p : ℝ × ℝ) :
    X (gam k m p).1 (gam k m p).2 = sgn k • X p.1 p.2 := by
  simp only [gam]
  rw [periodic_int_curried hper, glide_int_neg hgl]

/-! ### Ŝ と F_s への適用 -/

/-- Ŝ は Γ 不変である。 -/
theorem Shat_gam (w₀ : ℝ) (k m : ℤ) (p : ℝ × ℝ) :
    Shat w₀ (gam k m p).1 (gam k m p).2 = Shat w₀ p.1 p.2 :=
  invariant_gam (Shat_periodic w₀) (Shat_glide w₀) k m p

section Deck

variable {w₀ ε : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) {F : ℝ → ℝ → ℝ → V3}
  (E : NeckEversion w₀ ε (Shat w₀) F)

include h0 h1 in
/-- X̂ は Γ 同変である：X̂∘γ_{k,m} = (−1)ᵏ X̂。 -/
theorem Xhat_gam (k m : ℤ) (p : ℝ × ℝ) :
    Xhat w₀ (gam k m p).1 (gam k m p).2 = sgn k • Xhat w₀ p.1 p.2 :=
  equivariant_gam (Xhat_periodic h0 h1) (Xhat_glide h0 h1) k m p

include E in
/-- 族の各段 F_s は Γ 不変である。 -/
theorem F_gam (s : ℝ) (k m : ℤ) (p : ℝ × ℝ) : F s (gam k m p).1 (gam k m p).2 = F s p.1 p.2 :=
  invariant_gam (E.periodic s) (E.glide s) k m p

include E in
theorem XF_periodic (s w v : ℝ) : XF F s w (v + 2 * π) = XF F s w v := by
  have e : (fun w v => F s w (v + 2 * π)) = F s := by
    funext w v
    rw [E.periodic]
  have h := normalOf_shift_v (F := F s) (w := w) (v := v) (a := 2 * π)
    (differentiableAt_F E s _)
  rw [e] at h
  simp only [XF]
  exact h.symm

include E in
/-- 動く面の法線は Γ 同変である：X_{F,s}∘γ_{k,m} = (−1)ᵏ X_{F,s}。 -/
theorem XF_gam (s : ℝ) (k m : ℤ) (p : ℝ × ℝ) :
    XF F s (gam k m p).1 (gam k m p).2 = sgn k • XF F s p.1 p.2 :=
  equivariant_gam (XF_periodic E s) (XF_glide E s) k m p

end Deck

/-- **一側性（Γ の形）**：Ω で符号を変える連続で消えない法線 X について、Γ のすべての元で不変な
連続で消えない法線場はない。`no_equivariant_normal` を Γ の元の言葉で述べたもの。 -/
theorem no_gam_invariant_normal {X : ℝ → ℝ → V3}
    (hX : Continuous (fun p : ℝ × ℝ => X p.1 p.2)) (hne : ∀ w v, X w v ≠ wp)
    (hglide : ∀ w v, X (w + 4) (-v) = -X w v) :
    ¬ ∃ n : ℝ × ℝ → V3, Continuous n ∧ (∀ p, n p ≠ wp) ∧
      (∀ p, cross (n p) (X p.1 p.2) = wp) ∧ (∀ (k m : ℤ) (p : ℝ × ℝ), n (gam k m p) = n p) := by
  rintro ⟨n, hn, hn0, hpar, hinv⟩
  refine no_equivariant_normal hX hne hglide ⟨n, hn, hn0, hpar, fun w v => ?_, fun w v => ?_⟩
  · have h := hinv 1 0 (w, v)
    rwa [gam_Omega] at h
  · have h := hinv 0 1 (w, v)
    rwa [gam_T] at h

end Zeno.Smale
