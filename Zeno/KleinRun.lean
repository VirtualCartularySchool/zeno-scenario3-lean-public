/-
# Zeno.KleinRun : 定理 K1（一つの源曲面 Ŝ の上の走者と M1・M2）

定理 6.5（`regular_passage`）の走者を、そのまま Ŝ の上に置く。競走の時間 t ∈ [0, 2t∗] では
|w| ≤ 1 なので Ŝ = Σ であり、定理 6.5 の各結論がそのまま移る。
側のラベルと岸での一致は競走の時間に限って述べる（Ŝ は w で周期的に閉じているので、
全時刻の文は意味をもたない）。

M1：どの連続な法線場でも、首の右岸 [w₀, 1] と左岸 [−1, −w₀] で Φ のラベルが逆になる。
M2：Γ と両立する連続で消えない法線場はない。亀とアキレスの閉路に沿って法線は反転する。
閉路の延長 t ∈ [2t∗, 3t∗] は法線を運ぶための道であり、競走の時間ではない。
-/
import Zeno.Klein

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### 構造体 `KleinPassage` -/

/-- **定理 K1 の結論**。`RegularPassage` の欄を同じ文で置き（側のラベルと岸の一致は競走の時間に限る）、
M1（`reversal`）と M2（`one_sided`、`loop_T`、`loop_A`）を加える。 -/
structure KleinPassage (R : Race) (w₀ c : ℝ) (n₁ : ℕ) (S X : ℝ → ℝ → V3) (Vt Va : ℝ → ℝ) :
    Prop where
  surface : IsKleinSurface w₀ S X
  smooth_T : ContDiff ℝ ∞ (R.runT S Vt)
  smooth_A : ContDiff ℝ ∞ (R.runA S Va)
  /-- M1：首の両岸で Φ のラベルが逆になる（ラベルによらない形）。 -/
  reversal : ∀ n, IsNormalField S n → ∀ w₁ w₂ v₁ v₂, w₀ ≤ w₁ → w₁ ≤ 1 → -1 ≤ w₂ → w₂ ≤ -w₀ →
    side (S w₁ v₁) (n (w₁, v₁)) * side (S w₂ v₂) (n (w₂, v₂)) < 0
  side_T_right : ∀ t ∈ Icc 0 (2 * R.tstar), c ≤ R.r * R.g t →
    Front (R.runT S Vt t) (X (R.r * R.g t) (Vt (R.r * R.g t)))
  side_T_left : ∀ t ∈ Icc 0 (2 * R.tstar), R.r * R.g t ≤ -c →
    Back (R.runT S Vt t) (X (R.r * R.g t) (Vt (R.r * R.g t)))
  side_A_right : ∀ t ∈ Icc 0 (2 * R.tstar), c ≤ R.g t →
    Back (R.runA S Va t) (-X (R.g t) (Va (R.g t)))
  side_A_left : ∀ t ∈ Icc 0 (2 * R.tstar), R.g t ≤ -c →
    Front (R.runA S Va t) (-X (R.g t) (Va (R.g t)))
  agree_T : ∀ t ∈ Icc 0 (2 * R.tstar), c ≤ |R.r * R.g t| → R.runT S Vt t = R.idealT t
  agree_A : ∀ t ∈ Icc 0 (2 * R.tstar), c ≤ |R.g t| → R.runA S Va t = R.idealA t
  step_before : ∀ k < n₁, R.runA S Va (R.tn (k + 1)) = R.runT S Vt (R.tn k)
  step_after : ∀ k < n₁, R.runT S Vt (R.tn' k) = R.runA S Va (R.tn' (k + 1))
  nearer : ∀ t ∈ Icc 0 (2 * R.tstar), t ≠ R.tstar → nsq (R.runT S Vt t) < nsq (R.runA S Va t)
  antipodal : ∃ A₀ B₀ : ℝ, 0 < B₀ ∧ R.runT S Vt R.tstar = (-A₀, 0, B₀) ∧
    R.runA S Va R.tstar = (-A₀, 0, -B₀)
  no_collision : ∀ t ∈ Icc 0 (2 * R.tstar), R.runT S Vt t ≠ R.runA S Va t
  min_dist : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), d ≤ nsq (R.runT S Vt t - R.runA S Va t)
  thick : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), ∀ e₁ e₂ : V3, nsq e₁ < d → nsq e₂ < d →
    R.runT S Vt t + e₁ ≠ R.runA S Va t + e₂
  compare_before : ∀ t, t < R.tstar → R.r * R.g t - R.g t < 0
  compare_after : ∀ t, R.tstar < t → 0 < R.r * R.g t - R.g t
  compare_zero : ∀ t, R.r * R.g t - R.g t = 0 ↔ t = R.tstar
  compare_not_collision : R.r * R.g R.tstar - R.g R.tstar = 0 ∧
    R.runT S Vt R.tstar ≠ R.runA S Va R.tstar
  approach_T : StrictAntiOn (fun t => nsq (R.runT S Vt t)) (Icc 0 R.tstar)
  approach_A : StrictAntiOn (fun t => nsq (R.runA S Va t)) (Icc 0 R.tstar)
  recede_T : StrictMonoOn (fun t => nsq (R.runT S Vt t)) (Icc R.tstar (2 * R.tstar))
  recede_A : StrictMonoOn (fun t => nsq (R.runA S Va t)) (Icc R.tstar (2 * R.tstar))
  follow_before : ∀ s t, 0 ≤ s → s < t → t ≤ R.tstar → R.runT S Vt t ≠ R.runA S Va s
  follow_after : ∀ s t, R.tstar ≤ s → s < t → t ≤ 2 * R.tstar → R.runA S Va t ≠ R.runT S Vt s
  /-- M2：Γ と両立する連続で消えない法線場はない。 -/
  one_sided : ¬ ∃ n : ℝ × ℝ → V3, Continuous n ∧ (∀ p, n p ≠ wp) ∧
    (∀ p, cross (n p) (X p.1 p.2) = wp) ∧
    (∀ w v, n (w + 4, -v) = n (w, v)) ∧ (∀ w v, n (w, v + 2 * π) = n (w, v))
  /-- M2：亀の閉路に沿って法線は反転する。 -/
  loop_T : ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
    (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.r * R.g t, Vt (R.r * R.g t))) ∧
    γ (3 * R.tstar) = ((γ 0).1 - 4, -(γ 0).2) ∧
    (∀ n : ℝ → V3, Continuous n → (∀ s, n s ≠ wp) →
      (∀ s, cross (n s) (X (γ s).1 (γ s).2) = wp) →
      ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0))
  /-- M2：アキレスの閉路に沿って法線は反転する。 -/
  loop_A : ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
    (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.g t, Va (R.g t))) ∧
    γ (3 * R.tstar) = ((γ 0).1 - 4, -(γ 0).2) ∧
    (∀ n : ℝ → V3, Continuous n → (∀ s, n s ≠ wp) →
      (∀ s, cross (n s) (X (γ s).1 (γ s).2) = wp) →
      ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0))

/-! ### 競走の時間では Ŝ = Σ -/

section Transfer

variable (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

theorem Race.abs_r_g_le_one {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) : |R.r * R.g t| ≤ 1 :=
  (R.abs_r_g_le t).trans (R.abs_g_le ht.1 ht.2)

include h0 h1 in
theorem runT_Shat_eq (V : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    R.runT (Shat w₀) V t = R.runT (Sig w₀) V t := by
  simp only [Race.runT]
  exact Shat_neck h0 h1 (R.abs_r_g_le_one ht) _

include h0 h1 in
theorem runA_Shat_eq (V : ℝ → ℝ) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    R.runA (Shat w₀) V t = R.runA (Sig w₀) V t := by
  simp only [Race.runA]
  exact Shat_neck h0 h1 (R.abs_g_le ht.1 ht.2) _

include h0 h1 in
theorem Xhat_eq_Xf_of_abs_le {w : ℝ} (hw : |w| ≤ 1) (v : ℝ) : Xhat w₀ w v = Xf w₀ w v := by
  have := abs_le.mp hw
  have := wa_gt_one h0 h1
  exact Xhat_eq_Xf h0 h1 (by linarith) (by linarith) v

theorem Race.tn_mem (k : ℕ) : R.tn k ∈ Icc 0 (2 * R.tstar) := by
  have hts := R.tstar_pos
  have hr := pow_pos R.r_pos k
  have hr1 : R.r ^ k ≤ 1 := pow_le_one₀ R.r_pos.le R.r_lt_one.le
  simp only [Race.tn]
  constructor <;> nlinarith

theorem Race.tn'_mem (k : ℕ) : R.tn' k ∈ Icc 0 (2 * R.tstar) := by
  have hts := R.tstar_pos
  have hr := pow_pos R.r_pos k
  have hr1 : R.r ^ k ≤ 1 := pow_le_one₀ R.r_pos.le R.r_lt_one.le
  simp only [Race.tn']
  constructor <;> nlinarith

theorem Race.tstar_mem : R.tstar ∈ Icc 0 (2 * R.tstar) := by
  have := R.tstar_pos
  constructor <;> linarith

end Transfer

/-! ### 閉路の延長 -/

/-- 道 p を [0, 2T] の外へ延ばして、t = 3T で Ω⁻¹(p 0) に着く滑らかな道。 -/
def loopExt (p : ℝ → ℝ × ℝ) (T t : ℝ) : ℝ × ℝ :=
  p t + s₀ ((t - 2 * T) / T) • (((p 0).1 - 4, -(p 0).2) - p t)

theorem contDiff_loopExt {p : ℝ → ℝ × ℝ} (hp : ContDiff ℝ ∞ p) (T : ℝ) :
    ContDiff ℝ ∞ (loopExt p T) := by
  unfold loopExt
  have hs : ContDiff ℝ ∞ fun t : ℝ => s₀ ((t - 2 * T) / T) :=
    Real.smoothTransition.contDiff.comp (by fun_prop)
  exact hp.add (hs.smul (contDiff_const.sub hp))

theorem loopExt_of_le {p : ℝ → ℝ × ℝ} {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ≤ 2 * T) :
    loopExt p T t = p t := by
  have : (t - 2 * T) / T ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le
  simp [loopExt, smoothTransition.zero_of_nonpos this]

theorem loopExt_end {p : ℝ → ℝ × ℝ} {T : ℝ} (hT : 0 < T) :
    loopExt p T (3 * T) = ((p 0).1 - 4, -(p 0).2) := by
  have e : (3 * T - 2 * T) / T = 1 := by field_simp; ring
  simp [loopExt, e, smoothTransition.one]

theorem loopExt_zero {p : ℝ → ℝ × ℝ} {T : ℝ} (hT : 0 < T) : loopExt p T 0 = p 0 :=
  loopExt_of_le hT (by linarith)

/-- 滑らかな道 p : [0, 2T] から、M2 の閉路の文を作る。 -/
theorem loop_of_path {X : ℝ → ℝ → V3} (hX : Continuous (fun p : ℝ × ℝ => X p.1 p.2))
    (hne : ∀ w v, X w v ≠ wp) (hglide : ∀ w v, X (w + 4) (-v) = -X w v)
    {p : ℝ → ℝ × ℝ} (hp : ContDiff ℝ ∞ p) {T : ℝ} (hT : 0 < T) :
    ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧ (∀ t ∈ Icc 0 (2 * T), γ t = p t) ∧
      γ (3 * T) = ((γ 0).1 - 4, -(γ 0).2) ∧
      (∀ n : ℝ → V3, Continuous n → (∀ s, n s ≠ wp) →
        (∀ s, cross (n s) (X (γ s).1 (γ s).2) = wp) →
        ∃ κ : ℝ, 0 < κ ∧ n (3 * T) = -(κ • n 0)) := by
  refine ⟨loopExt p T, contDiff_loopExt hp T, fun t ht => loopExt_of_le hT ht.2, ?_, ?_⟩
  · rw [loopExt_end hT, loopExt_zero hT]
  · intro n hn hn0 hperp
    exact side_reverses_along_glide_loop hX hne hglide (contDiff_loopExt hp T).continuous
      (by rw [loopExt_end hT, loopExt_zero hT]) hn hn0 hperp

/-! ### 定理 K1 -/

section Proof

variable (R : Race) {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (n₁ : ℕ) (hc : w₀ ≤ R.r ^ n₁)

local notation "Vt" => VtR (R.r ^ n₁)
local notation "Va" => VaR R.r w₀ (R.r ^ n₁) n₁
local notation "TT" => Race.runT R (Shat w₀) (VtR (R.r ^ n₁))
local notation "AR" => Race.runA R (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁)
local notation "TS" => Race.runT R (Sig w₀) (VtR (R.r ^ n₁))
local notation "AS" => Race.runA R (Sig w₀) (VaR R.r w₀ (R.r ^ n₁) n₁)

include h0 h1 in
theorem klein_smooth_T : ContDiff ℝ ∞ TT := by
  have h := contDiff_Shat h0 h1
  have hrg : ContDiff ℝ ∞ (fun t => R.r * R.g t) := contDiff_const.mul R.contDiff_g
  have hV : ContDiff ℝ ∞ (fun t => Vt (R.r * R.g t)) := (contDiff_VtR _).comp hrg
  exact h.comp (hrg.prodMk hV)

include h0 h1 in
theorem klein_smooth_A : ContDiff ℝ ∞ AR := by
  have h := contDiff_Shat h0 h1
  have hg := R.contDiff_g
  have hV : ContDiff ℝ ∞ (fun t => Va (R.g t)) := (contDiff_VaR R.r h0.ne' _ n₁).comp hg
  exact h.comp (hg.prodMk hV)

include h0 h1 in
/-- M1 の証明：`normal_rigid` と、両岸での Ŝ = G、X̂ = k N。 -/
theorem klein_reversal {n : ℝ × ℝ → V3} (hn : IsNormalField (Shat w₀) n) {w₁ w₂ : ℝ}
    (h₁ : w₀ ≤ w₁) (h₁' : w₁ ≤ 1) (h₂ : -1 ≤ w₂) (h₂' : w₂ ≤ -w₀) (v₁ v₂ : ℝ) :
    side (Shat w₀ w₁ v₁) (n (w₁, v₁)) * side (Shat w₀ w₂ v₂) (n (w₂, v₂)) < 0 := by
  have hK := Shat_isKlein h0 h1
  obtain ⟨c', -, hsm, hs⟩ := normal_rigid hK.normal_cont hK.normal_ne hK.normal hn
  have hh := (side_mul_of_rigid (α := ℝ × ℝ) (n := n) (N₀ := fun p => Xhat w₀ p.1 p.2) (c := c')
    hsm hs (q₁ := Shat w₀ w₁ v₁) (q₂ := Shat w₀ w₂ v₂) (p₁ := (w₁, v₁)) (p₂ := (w₂, v₂))).1
  refine hh (mul_neg_of_pos_of_neg ?_ ?_)
  · have hab : |w₁| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    simp only
    rw [Shat_neck h0 h1 hab, Xhat_eq_Xf_of_abs_le h0 h1 hab]
    obtain ⟨e, k, hk, hX⟩ := (Sig_isNeckSurface h0 h1).right w₁ v₁ h₁
    rw [e, hX]
    exact side_right (by linarith) hk v₁
  · have hab : |w₂| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    simp only
    rw [Shat_neck h0 h1 hab, Xhat_eq_Xf_of_abs_le h0 h1 hab]
    obtain ⟨e, k, hk, hX⟩ := (Sig_isNeckSurface h0 h1).left w₂ v₂ h₂'
    rw [e, hX]
    exact side_left (by linarith) hk _

include h0 h1 hc in
/-- **定理 K1**。 -/
theorem klein_passage :
    KleinPassage R w₀ (R.r ^ n₁) n₁ (Shat w₀) (Xhat w₀) (VtR (R.r ^ n₁))
      (VaR R.r w₀ (R.r ^ n₁) n₁) := by
  have P := regular_passage R h0 h1 n₁ hc
  have eT : ∀ t ∈ Icc 0 (2 * R.tstar), TT t = TS t := fun t ht => runT_Shat_eq R h0 h1 _ ht
  have eA : ∀ t ∈ Icc 0 (2 * R.tstar), AR t = AS t := fun t ht => runA_Shat_eq R h0 h1 _ ht
  have hts := R.tstar_pos
  have hIcc : ∀ t, t ∈ Icc 0 R.tstar → t ∈ Icc 0 (2 * R.tstar) :=
    fun t ht => ⟨ht.1, by linarith [ht.2]⟩
  have hIcc' : ∀ t, t ∈ Icc R.tstar (2 * R.tstar) → t ∈ Icc 0 (2 * R.tstar) :=
    fun t ht => ⟨by linarith [ht.1], ht.2⟩
  exact
  { surface := Shat_isKlein h0 h1
    smooth_T := klein_smooth_T R h0 h1 n₁
    smooth_A := klein_smooth_A R h0 h1 n₁
    reversal := fun n hn w₁ w₂ v₁ v₂ h₁ h₁' h₂ h₂' =>
      klein_reversal h0 h1 hn h₁ h₁' h₂ h₂' v₁ v₂
    side_T_right := fun t ht hct => by
      rw [eT t ht, Xhat_eq_Xf_of_abs_le h0 h1 (R.abs_r_g_le_one ht)]
      exact P.side_T_right t hct
    side_T_left := fun t ht hct => by
      rw [eT t ht, Xhat_eq_Xf_of_abs_le h0 h1 (R.abs_r_g_le_one ht)]
      exact P.side_T_left t hct
    side_A_right := fun t ht hct => by
      rw [eA t ht, Xhat_eq_Xf_of_abs_le h0 h1 (R.abs_g_le ht.1 ht.2)]
      exact P.side_A_right t hct
    side_A_left := fun t ht hct => by
      rw [eA t ht, Xhat_eq_Xf_of_abs_le h0 h1 (R.abs_g_le ht.1 ht.2)]
      exact P.side_A_left t hct
    agree_T := fun t ht hct => by rw [eT t ht]; exact P.agree_T t hct
    agree_A := fun t ht hct => by rw [eA t ht]; exact P.agree_A t hct
    step_before := fun k hk => by
      rw [eA _ (R.tn_mem _), eT _ (R.tn_mem _)]; exact P.step_before k hk
    step_after := fun k hk => by
      rw [eA _ (R.tn'_mem _), eT _ (R.tn'_mem _)]; exact P.step_after k hk
    nearer := fun t ht hne => by rw [eT t ht, eA t ht]; exact P.nearer t ht hne
    antipodal := by
      obtain ⟨A₀, B₀, hB, hT', hA'⟩ := P.antipodal
      exact ⟨A₀, B₀, hB, by rw [eT _ R.tstar_mem]; exact hT', by rw [eA _ R.tstar_mem]; exact hA'⟩
    no_collision := fun t ht => by rw [eT t ht, eA t ht]; exact P.no_collision t ht
    min_dist := by
      obtain ⟨d, hd, hdm⟩ := P.min_dist
      exact ⟨d, hd, fun t ht => by rw [eT t ht, eA t ht]; exact hdm t ht⟩
    thick := by
      obtain ⟨d, hd, hdm⟩ := P.thick
      exact ⟨d, hd, fun t ht e₁ e₂ h₁ h₂ => by rw [eT t ht, eA t ht]; exact hdm t ht e₁ e₂ h₁ h₂⟩
    compare_before := P.compare_before
    compare_after := P.compare_after
    compare_zero := P.compare_zero
    compare_not_collision := ⟨P.compare_not_collision.1, by
      rw [eT _ R.tstar_mem, eA _ R.tstar_mem]; exact P.compare_not_collision.2⟩
    approach_T := fun s hs t ht hst => by
      simp only
      rw [eT s (hIcc s hs), eT t (hIcc t ht)]; exact P.approach_T hs ht hst
    approach_A := fun s hs t ht hst => by
      simp only
      rw [eA s (hIcc s hs), eA t (hIcc t ht)]; exact P.approach_A hs ht hst
    recede_T := fun s hs t ht hst => by
      simp only
      rw [eT s (hIcc' s hs), eT t (hIcc' t ht)]; exact P.recede_T hs ht hst
    recede_A := fun s hs t ht hst => by
      simp only
      rw [eA s (hIcc' s hs), eA t (hIcc' t ht)]; exact P.recede_A hs ht hst
    follow_before := fun s t hs hst ht => by
      rw [eT t ⟨by linarith, by linarith⟩, eA s ⟨hs, by linarith⟩]
      exact P.follow_before s t hs hst ht
    follow_after := fun s t hs hst ht => by
      rw [eA t ⟨by linarith, ht⟩, eT s ⟨by linarith, by linarith⟩]
      exact P.follow_after s t hs hst ht
    one_sided := no_equivariant_normal (continuous_Xhat h0 h1) (Xhat_ne h0 h1) (Xhat_glide h0 h1)
    loop_T := by
      have hp : ContDiff ℝ ∞ (fun t => ((R.r * R.g t, Vt (R.r * R.g t)) : ℝ × ℝ)) := by
        have hrg : ContDiff ℝ ∞ (fun t => R.r * R.g t) := contDiff_const.mul R.contDiff_g
        exact hrg.prodMk ((contDiff_VtR _).comp hrg)
      exact loop_of_path (continuous_Xhat h0 h1) (Xhat_ne h0 h1) (Xhat_glide h0 h1) hp hts
    loop_A := by
      have hp : ContDiff ℝ ∞ (fun t => ((R.g t, Va (R.g t)) : ℝ × ℝ)) :=
        R.contDiff_g.prodMk ((contDiff_VaR R.r h0.ne' _ n₁).comp R.contDiff_g)
      exact loop_of_path (continuous_Xhat h0 h1) (Xhat_ne h0 h1) (Xhat_glide h0 h1) hp hts }

/-! ### D7 の検査の静的な小補題（注意 8.10 の (2″)(1″)） -/

include h0 h1 hc in
/-- (2″)：t∗ で x̂(T) = x̂(A)（静的な面の上で正確）。 -/
theorem compare_xhat : xhat (TT R.tstar) = xhat (AR R.tstar) := by
  rw [runT_Shat_eq R h0 h1 _ R.tstar_mem, runA_Shat_eq R h0 h1 _ R.tstar_mem,
    reg_Ts R h0 hc, reg_As R h0 hc n₁]
  simp only [xhat, nsq, dot]
  ring

include h0 h1 hc in
/-- (1″)：t∗ で断面の座標 (q₂, q₃) の差は (0, 2 bb₀) であり、0 ではない。 -/
theorem cross_section :
    (TT R.tstar).2 - (AR R.tstar).2 = ((0 : ℝ), 2 * BB w₀ 0) ∧ 0 < BB w₀ 0 := by
  rw [runT_Shat_eq R h0 h1 _ R.tstar_mem, runA_Shat_eq R h0 h1 _ R.tstar_mem,
    reg_Ts R h0 hc, reg_As R h0 hc n₁]
  refine ⟨?_, BB_pos h0 h1 0⟩
  simp only [Prod.mk_sub_mk]
  refine Prod.ext ?_ ?_ <;> simp only <;> ring

end Proof

end Zeno.Model
