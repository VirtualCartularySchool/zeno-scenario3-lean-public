/-
# ZenoSmale.KleinDynamic : 定理 K3⁺（走者の通過と連成した首の動的な裏返し）

第 3 版 §2.7 の `DynamicPassage` と `dynamic_passage`。

同一の源曲面 Ŝ の上で、首だけを動かす正則ホモトピー F（`neck_eversion`）を、
走者の時刻の対応 sched（窓 [t₁, t₂]、t∗ が中心）で動かす。走者の軌道は
dynT(t) = F(sched t, r g(t), Vt(r g(t)))、dynA(t) = F(sched t, g(t), Va(g(t))) である。

- 窓の外（t ≤ t₁、t ≥ t₂）では F は Ŝ または −Ŝ∘φ に等しく、走者は静的な走者（または
  その φ による反転）に正確に一致する。ゼノンの段階、岸での理想形との一致、側のラベルは、
  走者が首の動く部分の外にいる時刻なので正確に成り立つ。
- 窓の中では、基底 B の上の走者（`baseT`・`baseA`）に ε で近い。非衝突・追従は基底の最小距離
  m₁・m_b・m_a と ε の選択で F に移る。
- 中央円の外在的な側は反転する（`flips_middle`）。M2 は族のどの段でも成り立つ（`one_sided_all`）。
-/
import ZenoSmale.KleinEversion
import Zeno.KleinMain

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff
open Zeno.Model

/-! ### 動く面の上の走者と法線 -/

/-- 動く面の上の亀。 -/
def dynT (R : Race) (w₀ : ℝ) (F : ℝ → ℝ → ℝ → V3) (Vt : ℝ → ℝ) (t : ℝ) : V3 :=
  F (sched R w₀ t) (R.r * R.g t) (Vt (R.r * R.g t))

/-- 動く面の上のアキレス。 -/
def dynA (R : Race) (w₀ : ℝ) (F : ℝ → ℝ → ℝ → V3) (Va : ℝ → ℝ) (t : ℝ) : V3 :=
  F (sched R w₀ t) (R.g t) (Va (R.g t))

/-- 動く面の法線 X_{F,s} = ∂ᵥF_s × ∂wF_s。 -/
def XF (F : ℝ → ℝ → ℝ → V3) (s : ℝ) : ℝ → ℝ → V3 := normalOf (F s)

/-! ### 一般の滑らかな面の法線：連続性、非零性、降下 -/

section NormalGen

variable {G : ℝ → ℝ → V3} {w v : ℝ}

theorem deriv_partial_v_eq (hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => G p.1 p.2) (w, v)) :
    deriv (fun v => G w v) v = fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) (w, v) ((0 : ℝ), (1 : ℝ)) := by
  have hl : HasDerivAt (fun x : ℝ => ((w, x) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) v :=
    (hasDerivAt_const v w).prodMk (hasDerivAt_id' v)
  exact (hd.hasFDerivAt.comp_hasDerivAt v hl).deriv

theorem deriv_partial_w_eq (hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => G p.1 p.2) (w, v)) :
    deriv (fun w => G w v) w = fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) (w, v) ((1 : ℝ), (0 : ℝ)) := by
  have hl : HasDerivAt (fun x : ℝ => ((x, v) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) w :=
    (hasDerivAt_id' w).prodMk (hasDerivAt_const w v)
  exact (hd.hasFDerivAt.comp_hasDerivAt w hl).deriv

/-- 滑らかな面の法線は連続である。 -/
theorem continuous_normalOf (hG : ContDiff ℝ ∞ (fun p : ℝ × ℝ => G p.1 p.2)) :
    Continuous (fun p : ℝ × ℝ => normalOf G p.1 p.2) := by
  have hd : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun p : ℝ × ℝ => G p.1 p.2) p :=
    fun p => hG.differentiable (by simp) p
  have hf : Continuous (fun p : ℝ × ℝ => fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) p) :=
    hG.continuous_fderiv (by simp)
  have e : (fun p : ℝ × ℝ => normalOf G p.1 p.2) = fun p =>
      cross (fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) p ((0 : ℝ), (1 : ℝ)))
        (fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) p ((1 : ℝ), (0 : ℝ))) := by
    funext p
    obtain ⟨w, v⟩ := p
    simp only [normalOf]
    rw [deriv_partial_v_eq (hd (w, v)), deriv_partial_w_eq (hd (w, v))]
  rw [e]
  exact continuous_cross.comp ((hf.clm_apply continuous_const).prodMk (hf.clm_apply continuous_const))

/-- はめ込みの法線は消えない。 -/
theorem normalOf_ne_of_injective (hd : DifferentiableAt ℝ (fun p : ℝ × ℝ => G p.1 p.2) (w, v))
    (hinj : Injective (fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) (w, v))) : normalOf G w v ≠ wp := by
  intro h
  have hw := (differentiableAt_partial_w hd).hasDerivAt
  have hv := (differentiableAt_partial_v hd).hasDerivAt
  set W := deriv (fun w => G w v) w
  set V := deriv (fun v => G w v) v
  have hcross : cross V W = wp := h
  have hsm := smul_of_cross_eq hcross
  -- ξ := (−⟨V, W⟩, ⟨W, W⟩) は核に入る
  have hξ : fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) (w, v) (-(dot V W), dot W W) = 0 := by
    rw [fderiv_apply_of_partials hd hw hv]
    simp only
    rw [neg_smul, hsm]
    abel
  have h0 := hinj (hξ.trans (map_zero _).symm)
  have hWW : dot W W = 0 := congrArg Prod.snd h0
  have hW : W = wp := by
    by_contra hne
    exact dot_self_ne hne hWW
  have h1 : fderiv ℝ (fun p : ℝ × ℝ => G p.1 p.2) (w, v) ((1 : ℝ), (0 : ℝ)) = 0 := by
    rw [fderiv_apply_of_partials hd hw hv]
    simp [hW, wp]
  have := hinj (h1.trans (map_zero _).symm)
  have := congrArg Prod.fst this
  simp at this

/-- Γ 同変な面の法線は降下する：X(w + 4, −v) = −X(w, v)。 -/
theorem normalOf_glide (hd : ∀ p : ℝ × ℝ, DifferentiableAt ℝ (fun p : ℝ × ℝ => G p.1 p.2) p)
    (hgl : ∀ w v, G (w + 4) (-v) = G w v) (w v : ℝ) :
    normalOf G (w + 4) (-v) = -normalOf G w v := by
  have e : (fun w v => G (w + 4) (-1 * v)) = G := by
    funext w v
    rw [neg_one_mul, hgl]
  have h := normalOf_affine (F := G) (c := 4) (s := -1) (w := w) (v := v) (hd _)
  rw [e] at h
  simp only [neg_one_mul] at h ⊢
  rw [h, neg_one_smul]
  simp

end NormalGen

/-! ### 補助：導線の φ 対称性、g の反転、周期性 -/

section Aux

theorem smoothTransition_one_sub (x : ℝ) :
    Real.smoothTransition (1 - x) = 1 - Real.smoothTransition x := by
  unfold Real.smoothTransition
  have h := Real.smoothTransition.pos_denom x
  rw [sub_sub_cancel, add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x), eq_sub_iff_add_eq,
    ← add_div, add_comm (expNegInvGlue (1 - x)) (expNegInvGlue x), div_self h.ne']

theorem ell_neg {c : ℝ} (hc : 0 < c) (w : ℝ) : ell c (-w) = 1 - ell c w := by
  simp only [ell]
  have e : (-w + c) / (2 * c) = 1 - (w + c) / (2 * c) := by
    field_simp; ring
  rw [e, smoothTransition_one_sub]

theorem VtR_neg {c : ℝ} (hc : 0 < c) (w : ℝ) : VtR c (-w) = -π - VtR c w := by
  simp only [VtR, ell_neg hc]
  ring

theorem thetaSm_neg (r w₀ w : ℝ) : thetaSm r w₀ (-w) = thetaSm r w₀ w := by
  simp only [thetaSm, rho_neg]

theorem VaR_neg {r w₀ c : ℝ} (hc : 0 < c) (n₁ : ℕ) (w : ℝ) :
    VaR r w₀ c n₁ (-w) = π + 4 * π * n₁ - VaR r w₀ c n₁ w := by
  simp only [VaR, ell_neg hc, thetaSm_neg]
  ring

theorem _root_.Zeno.Model.Race.g_reflect (R : Race) (t : ℝ) : R.g (2 * R.tstar - t) = -R.g t := by
  have h := R.tstar_pos.ne'
  rw [R.g_eq, R.g_eq]
  field_simp
  ring

theorem Shat_periodic_int (w₀ w v : ℝ) (k : ℤ) : Shat w₀ w (v + k * (2 * π)) = Shat w₀ w v := by
  have hp : Function.Periodic (fun v => Shat w₀ w v) (2 * π) := fun v => Shat_periodic w₀ w v
  exact hp.int_mul k v

/-- |w| ∈ [9w₀/10, 1] なら、どの平行移動でも |w − 4k| ≥ 9w₀/10。 -/
theorem far_of_abs {w₀ w : ℝ} (h1 : w₀ < 1) (hw : w₀ * (9 / 10) ≤ |w|) (hw1 : |w| ≤ 1) (k : ℤ) :
    (9 / 10) * w₀ ≤ |w - 4 * (k : ℝ)| := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; simp; linarith
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast this
    have h := abs_sub_abs_le_abs_sub (4 * (k : ℝ)) w
    rw [abs_sub_comm (4 * (k : ℝ)) w, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h
    nlinarith [abs_nonneg w]

end Aux

/-! ### 中央円の法線と外在的な側 -/

section Middle

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 in
theorem deriv_AA_zero : deriv (AA w₀) 0 = -(deriv (kap w₀) 0 * BB w₀ 0) := by
  rw [(hasDerivAt_AA h0.ne' 0).deriv]
  simp only [uu, vv, drho, kap_zero', cos_zero, sin_zero, BB_zero]
  ring

include h0 in
theorem deriv_BB_zero : deriv (BB w₀) 0 = deriv (kap w₀) 0 * AA w₀ 0 := by
  rw [(hasDerivAt_BB h0.ne' 0).deriv]
  simp only [uu, vv, drho, kap_zero', cos_zero, sin_zero, AA_zero]
  ring

include h0 in
theorem deriv_psi_zero : deriv (psi w₀) 0 = 0 := by
  by_contra hd
  obtain ⟨h2, -⟩ := deriv_psi_ne h0 hd
  linarith

include h0 h1 in
/-- 中央円の法線：X̂(0, v) = −κ′(0) bb₀ Σ(0, v)（径方向で内向き）。 -/
theorem Xhat_zero (v : ℝ) :
    Xhat w₀ 0 v = -(deriv (kap w₀) 0 * BB w₀ 0) • Sig w₀ 0 v := by
  have hwa := wa_gt_one h0 h1
  rw [Xhat_eq_Xf h0 h1 (by linarith) (by linarith), Xf, cross_sig, deriv_AA_zero h0, deriv_BB_zero h0,
    deriv_psi_zero h0, Sig, sigmaOf, ← rot2_smul]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;> ring

theorem dot_gradPhi_self (q : V3) :
    dot (gradPhi q) q = 4 * q.1 ^ 2 * (q.2.1 ^ 2 + q.2.2 ^ 2) - 8 * nsq q ^ 4 := by
  simp only [gradPhi, dot, nsq]
  ring

include h0 in
theorem Sig_zero_sq (v : ℝ) :
    (Sig w₀ 0 v).1 ^ 2 = AA w₀ 0 ^ 2 ∧
      (Sig w₀ 0 v).2.1 ^ 2 + (Sig w₀ 0 v).2.2 ^ 2 = BB w₀ 0 ^ 2 := by
  rw [Sig_zero h0]
  constructor
  · simp
  · simp only
    linear_combination BB w₀ 0 ^ 2 * cos_sq_add_sin_sq v

include h0 in
theorem AA_sq_mul_BB_sq_zero : AA w₀ 0 ^ 2 * BB w₀ 0 ^ 2 = (nsq (Sig w₀ 0 0)) ^ 4 := by
  obtain ⟨e1, e2⟩ := Sig_zero_sq h0 0
  have hN : nsq (Sig w₀ 0 0) = AA w₀ 0 ^ 2 + BB w₀ 0 ^ 2 := by
    simp only [nsq, dot]
    nlinarith [e1, e2]
  rw [hN, AA_zero, BB_zero]
  have := lemniscate (rho w₀ 0)
  nlinarith [this]

include h0 in
theorem nsq_Sig_zero_const (v : ℝ) : nsq (Sig w₀ 0 v) = nsq (Sig w₀ 0 0) := by
  rw [nsq_Sig h0.ne', nsq_Sig h0.ne']

include h0 h1 in
/-- **中央円の外在的な側**：side(Σ(0, v), X̂(0, v)) = 4 κ′(0) bb₀ N₀⁴ > 0。 -/
theorem side_middle (v : ℝ) :
    side (Sig w₀ 0 v) (Xhat w₀ 0 v) = 4 * deriv (kap w₀) 0 * BB w₀ 0 * (nsq (Sig w₀ 0 v)) ^ 4 := by
  rw [Xhat_zero h0 h1, side, dot_smul_right', dot_gradPhi_self]
  obtain ⟨e1, e2⟩ := Sig_zero_sq h0 v
  have hN : nsq (Sig w₀ 0 v) = AA w₀ 0 ^ 2 + BB w₀ 0 ^ 2 := by
    simp only [nsq, dot]
    nlinarith [e1, e2]
  have hprod := AA_sq_mul_BB_sq_zero h0
  rw [← nsq_Sig_zero_const h0 v] at hprod
  rw [e1, e2]
  linear_combination (-(4 * deriv (kap w₀) 0 * BB w₀ 0)) * hprod

include h0 h1 in
theorem side_middle_pos (v : ℝ) : 0 < side (Sig w₀ 0 v) (Xhat w₀ 0 v) := by
  rw [side_middle h0 h1]
  have hk : 0 < deriv (kap w₀) 0 := by
    rw [deriv_kap_zero h0.ne']
    exact div_pos (rsq_pos h0.ne') (by positivity)
  have hb := BB_pos h0 h1 0
  have hN := nsq_pos_of_ne (Sig_ne_wp h0.ne' 0 v)
  positivity

end Middle

/-! ### 構造体 `DynamicPassage` -/

/-- **定理 K3⁺ の結論**（第 3 版 §2.7）。側のラベルと岸の一致は競走の時間に限る。 -/
structure DynamicPassage (R : Race) (w₀ c ε : ℝ) (n₁ : ℕ) (S X : ℝ → ℝ → V3)
    (F : ℝ → ℝ → ℝ → V3) (Vt Va : ℝ → ℝ) : Prop where
  eversion : NeckEversion w₀ ε S F
  /-- 連成：窓の中では二人とも動く首の深部にいる。 -/
  rides : ∀ t, t1 R w₀ < t → t < t2 R w₀ →
    0 < sched R w₀ t ∧ sched R w₀ t < 1 ∧ |R.g t| ≤ w₀ / 4
  /-- t∗ は窓の中心である。 -/
  centred : sched R w₀ R.tstar = 1 / 2
  /-- t∗ で走者は静的な位置から動いている。 -/
  moved : dynT R w₀ F Vt R.tstar ≠ R.runT S Vt R.tstar ∧
    dynA R w₀ F Va R.tstar ≠ R.runA S Va R.tstar
  smooth_T : ContDiff ℝ ∞ (dynT R w₀ F Vt)
  smooth_A : ContDiff ℝ ∞ (dynA R w₀ F Va)
  static_before : ∀ t, t ≤ t1 R w₀ →
    dynT R w₀ F Vt t = R.runT S Vt t ∧ dynA R w₀ F Va t = R.runA S Va t
  static_after : ∀ t, t2 R w₀ ≤ t → t ≤ 2 * R.tstar →
    dynT R w₀ F Vt t = -(R.runT S Vt (2 * R.tstar - t)) ∧
      dynA R w₀ F Va t = -(R.runA S Va (2 * R.tstar - t))
  no_collision : ∀ t ∈ Icc 0 (2 * R.tstar), dynT R w₀ F Vt t ≠ dynA R w₀ F Va t
  min_dist : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), d ≤ nsq (dynT R w₀ F Vt t - dynA R w₀ F Va t)
  thick : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), ∀ e₁ e₂ : V3, nsq e₁ < d → nsq e₂ < d →
    dynT R w₀ F Vt t + e₁ ≠ dynA R w₀ F Va t + e₂
  step_before : ∀ k < n₁, dynA R w₀ F Va (R.tn (k + 1)) = dynT R w₀ F Vt (R.tn k)
  step_after : ∀ k < n₁, dynT R w₀ F Vt (R.tn' k) = dynA R w₀ F Va (R.tn' (k + 1))
  agree_T : ∀ t ∈ Icc 0 (2 * R.tstar), c ≤ |R.r * R.g t| → dynT R w₀ F Vt t = R.idealT t
  agree_A : ∀ t ∈ Icc 0 (2 * R.tstar), c ≤ |R.g t| → dynA R w₀ F Va t = R.idealA t
  side_T_right : ∀ t ∈ Icc 0 (2 * R.tstar), c ≤ R.r * R.g t →
    Front (dynT R w₀ F Vt t) (X (R.r * R.g t) (Vt (R.r * R.g t)))
  side_T_left : ∀ t ∈ Icc 0 (2 * R.tstar), R.r * R.g t ≤ -c →
    Back (dynT R w₀ F Vt t) (X (R.r * R.g t) (Vt (R.r * R.g t)))
  side_A_right : ∀ t ∈ Icc 0 (2 * R.tstar), c ≤ R.g t →
    Back (dynA R w₀ F Va t) (-X (R.g t) (Va (R.g t)))
  side_A_left : ∀ t ∈ Icc 0 (2 * R.tstar), R.g t ≤ -c →
    Front (dynA R w₀ F Va t) (-X (R.g t) (Va (R.g t)))
  follow_before : ∀ s t, 0 ≤ s → s < t → t ≤ R.tstar → dynT R w₀ F Vt t ≠ dynA R w₀ F Va s
  follow_after : ∀ s t, R.tstar ≤ s → s < t → t ≤ 2 * R.tstar →
    dynA R w₀ F Va t ≠ dynT R w₀ F Vt s
  compare_before : ∀ t, t < R.tstar → R.r * R.g t - R.g t < 0
  compare_after : ∀ t, R.tstar < t → 0 < R.r * R.g t - R.g t
  compare_zero : ∀ t, R.r * R.g t - R.g t = 0 ↔ t = R.tstar
  compare_not_collision : R.r * R.g R.tstar - R.g R.tstar = 0 ∧
    dynT R w₀ F Vt R.tstar ≠ dynA R w₀ F Va R.tstar
  /-- ℘ への接近と後退：窓の外では厳密。 -/
  approach_T : StrictAntiOn (fun t => nsq (dynT R w₀ F Vt t)) (Icc 0 (t1 R w₀))
  approach_A : StrictAntiOn (fun t => nsq (dynA R w₀ F Va t)) (Icc 0 (t1 R w₀))
  recede_T : StrictMonoOn (fun t => nsq (dynT R w₀ F Vt t)) (Icc (t2 R w₀) (2 * R.tstar))
  recede_A : StrictMonoOn (fun t => nsq (dynA R w₀ F Va t)) (Icc (t2 R w₀) (2 * R.tstar))
  /-- 窓の中：℘ への距離は静的な走者の径に ε で近い。 -/
  sandwich_T : ∀ t ∈ Icc (t1 R w₀) (t2 R w₀),
    |√(nsq (dynT R w₀ F Vt t)) - √(nsq (Sig w₀ (R.r * R.g t) 0))| ≤ ε
  sandwich_A : ∀ t ∈ Icc (t1 R w₀) (t2 R w₀),
    |√(nsq (dynA R w₀ F Va t)) - √(nsq (Sig w₀ (R.g t) 0))| ≤ ε
  near_T : ∀ t ∈ Icc 0 (2 * R.tstar), √(nsq (dynT R w₀ F Vt t - baseT R w₀ c t)) ≤ ε
  near_A : ∀ t ∈ Icc 0 (2 * R.tstar), √(nsq (dynA R w₀ F Va t - baseA R w₀ c n₁ t)) ≤ ε
  /-- t∗ の位置：基底は正確。 -/
  base_tstar : baseT R w₀ c R.tstar = (BB w₀ 0, 0, AA w₀ 0) ∧
    baseA R w₀ c n₁ R.tstar = (-(BB w₀ 0), 0, AA w₀ 0)
  base_rotation : baseT R w₀ c R.tstar = rot2 (π / 2) (R.runT S Vt R.tstar) ∧
    baseA R w₀ c n₁ R.tstar = rot2 (π / 2) (R.runA S Va R.tstar)
  /-- 裏返しの効果：中央円の外在的な側が反転する（枠の法則 E、規約 X = ∂ᵥ × ∂w）。 -/
  flips_middle : ∀ v, side (F 1 0 v) (XF F 1 0 v) = -(side (S 0 v) (X 0 v)) ∧
    side (S 0 v) (X 0 v) = 4 * deriv (kap w₀) 0 * BB w₀ 0 * (nsq (S 0 v)) ^ 4 ∧
    0 < side (S 0 v) (X 0 v)
  /-- M2 は族のどの段でも成り立つ。 -/
  one_sided_all : ∀ s, ¬ ∃ n : ℝ × ℝ → V3, Continuous n ∧ (∀ p, n p ≠ wp) ∧
    (∀ p, cross (n p) (XF F s p.1 p.2) = wp) ∧
    (∀ w v, n (w + 4, -v) = n (w, v)) ∧ (∀ w v, n (w, v + 2 * π) = n (w, v))

/-! ### 裏返し F の一般的な性質 -/

section FProps

variable {w₀ ε : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) {F : ℝ → ℝ → ℝ → V3}
  (E : NeckEversion w₀ ε (Shat w₀) F)

theorem NeckEversion.mono (h0 : 0 < w₀) {ε' : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ ε')
    (E : NeckEversion w₀ ε (Shat w₀) F) : NeckEversion w₀ ε' (Shat w₀) F where
  smooth := E.smooth
  immersion := E.immersion
  periodic := E.periodic
  glide := E.glide
  start := E.start
  finish := E.finish
  support := E.support
  ball := fun s w v hw => by
    have h := E.ball s w v hw
    nlinarith
  nearBase := fun s w v hw => (E.nearBase s w v hw).trans hε

include E in
theorem differentiableAt_F (s : ℝ) (p : ℝ × ℝ) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ => F s p.1 p.2) p := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F s p.1 p.2) :=
    E.smooth.comp ((contDiff_const (c := s)).prodMk contDiff_id)
  exact h.differentiable (by simp) p

include E in
theorem continuous_XF (s : ℝ) : Continuous (fun p : ℝ × ℝ => XF F s p.1 p.2) :=
  continuous_normalOf (E.smooth.comp ((contDiff_const (c := s)).prodMk contDiff_id))

include E in
theorem XF_ne (s w v : ℝ) : XF F s w v ≠ wp :=
  normalOf_ne_of_injective (differentiableAt_F E s (w, v)) (E.immersion s (w, v))

include E in
theorem XF_glide (s w v : ℝ) : XF F s (w + 4) (-v) = -XF F s w v :=
  normalOf_glide (differentiableAt_F E s) (E.glide s) w v

include E in
/-- M2 は族のどの段でも成り立つ。 -/
theorem one_sided_all (s : ℝ) : ¬ ∃ n : ℝ × ℝ → V3, Continuous n ∧ (∀ p, n p ≠ wp) ∧
    (∀ p, cross (n p) (XF F s p.1 p.2) = wp) ∧
    (∀ w v, n (w + 4, -v) = n (w, v)) ∧ (∀ w v, n (w, v + 2 * π) = n (w, v)) :=
  no_equivariant_normal (continuous_XF E s) (XF_ne E s) (XF_glide E s)

include h0 h1 E in
/-- 端点の首の法線：X_{F,1}(0, v) = X̂(0, π − v)。 -/
theorem XF_one_zero (v : ℝ) : XF F 1 0 v = Xhat w₀ 0 (π - v) := by
  have hd := differentiableAt_Shat h0 h1
  simp only [XF, normalOf, Xhat]
  -- ∂ᵥ
  have ev : (fun v' => F 1 0 v') = fun v' => -(Shat w₀ 0 (π - v')) := by
    funext v'
    rw [E.finish 1 0 v' le_rfl (by simp), neg_zero]
  have hv : deriv (fun v' => F 1 0 v') v = deriv (fun v => Shat w₀ 0 v) (π - v) := by
    rw [ev]
    have h := (differentiableAt_partial_v (hd (0, π - v))).hasDerivAt
    have hl : HasDerivAt (fun v' : ℝ => π - v') (-1) v := (hasDerivAt_id v).const_sub π
    have h2 : HasDerivAt (fun v' => -(Shat w₀ 0 (π - v')))
        (-((-1 : ℝ) • deriv (fun v => Shat w₀ 0 v) (π - v))) v := (h.scomp v hl).neg
    rw [h2.deriv, neg_one_smul, neg_neg]
  -- ∂w
  have ew : (fun w => F 1 w v) =ᶠ[𝓝 0] fun w => -(Shat w₀ (-w) (π - v)) := by
    have hopen : IsOpen {w : ℝ | |w| < 1} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds (by simp)] with w hw
    exact E.finish 1 w v le_rfl (le_of_lt hw)
  have hw : deriv (fun w => F 1 w v) 0 = deriv (fun w => Shat w₀ w (π - v)) 0 := by
    rw [ew.deriv_eq]
    have h : HasDerivAt (fun w => Shat w₀ w (π - v)) (deriv (fun w => Shat w₀ w (π - v)) 0) (-0) := by
      rw [neg_zero]
      exact (differentiableAt_partial_w (hd (0, π - v))).hasDerivAt
    have hl : HasDerivAt (fun w : ℝ => -w) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
    have h2 : HasDerivAt (fun w => -(Shat w₀ (-w) (π - v)))
        (-((-1 : ℝ) • deriv (fun w => Shat w₀ w (π - v)) 0)) 0 := (h.scomp (0 : ℝ) hl).neg
    rw [h2.deriv, neg_one_smul, neg_neg]
  rw [hv, hw]

include h0 h1 E in
/-- **中央円の反転**。 -/
theorem flips_middle (v : ℝ) :
    side (F 1 0 v) (XF F 1 0 v) = -(side (Shat w₀ 0 v) (Xhat w₀ 0 v)) ∧
      side (Shat w₀ 0 v) (Xhat w₀ 0 v) =
        4 * deriv (kap w₀) 0 * BB w₀ 0 * (nsq (Shat w₀ 0 v)) ^ 4 ∧
      0 < side (Shat w₀ 0 v) (Xhat w₀ 0 v) := by
  have hS : ∀ u, Shat w₀ 0 u = Sig w₀ 0 u := fun u => Shat_neck h0 h1 (by simp) u
  refine ⟨?_, ?_, ?_⟩
  · rw [XF_one_zero h0 h1 E, E.finish 1 0 v le_rfl (by simp), neg_zero, side_neg_pos, hS, hS,
      side_middle h0 h1, side_middle h0 h1, nsq_Sig_zero_const h0 (π - v), nsq_Sig_zero_const h0 v]
  · rw [hS, side_middle h0 h1]
  · rw [hS]; exact side_middle_pos h0 h1 v

end FProps

/-! ### 走者の移行 -/

section Dynamic

variable (R : Race) {w₀ ε : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (n₁ : ℕ) (hc : w₀ ≤ R.r ^ n₁)
  {F : ℝ → ℝ → ℝ → V3} (E : NeckEversion w₀ ε (Shat w₀) F)

local notation "Vt" => VtR (R.r ^ n₁)
local notation "Va" => VaR R.r w₀ (R.r ^ n₁) n₁
local notation "TT" => Race.runT R (Shat w₀) (VtR (R.r ^ n₁))
local notation "AR" => Race.runA R (Shat w₀) (VaR R.r w₀ (R.r ^ n₁) n₁)
local notation "DT" => dynT R w₀ F (VtR (R.r ^ n₁))
local notation "DA" => dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁)
local notation "BT" => baseT R w₀ (R.r ^ n₁)
local notation "BA" => baseA R w₀ (R.r ^ n₁) n₁

include h0 hc in
theorem hc_pos : 0 < R.r ^ n₁ := lt_of_lt_of_le h0 hc

include h0 E in
theorem dyn_before {t : ℝ} (ht : t ≤ t1 R w₀) : DT t = TT t ∧ DA t = AR t := by
  have hs := sched_le_zero h0 R ht
  exact ⟨E.start _ _ _ hs, E.start _ _ _ hs⟩

include h0 h1 hc E in
theorem dyn_after {t : ℝ} (ht2 : t2 R w₀ ≤ t) (ht : t ≤ 2 * R.tstar) :
    DT t = -(TT (2 * R.tstar - t)) ∧ DA t = -(AR (2 * R.tstar - t)) := by
  have hs := sched_ge_one h0 R ht2
  have hts := R.tstar_pos
  have ht0 : 0 ≤ t := by linarith [t1_pos R h1, t1_lt_tstar R h0, tstar_lt_t2 R h0]
  have hcp := hc_pos R h0 n₁ hc
  constructor
  · rw [dynT, E.finish _ _ _ hs (R.abs_r_g_le_one ⟨ht0, ht⟩), Race.runT, R.g_reflect, mul_neg,
      VtR_neg hcp]
    have e : π - VtR (R.r ^ n₁) (R.r * R.g t) =
        (-π - VtR (R.r ^ n₁) (R.r * R.g t)) + ((1 : ℤ) : ℝ) * (2 * π) := by
      push_cast; ring
    rw [e, Shat_periodic_int]
  · rw [dynA, E.finish _ _ _ hs (R.abs_g_le ht0 ht), Race.runA, R.g_reflect, VaR_neg hcp]
    have e : π - VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t) =
        (π + 4 * π * n₁ - VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t)) +
          (((-(2 * (n₁ : ℤ))) : ℤ) : ℝ) * (2 * π) := by
      push_cast; ring
    rw [e, Shat_periodic_int w₀ _ _ (-(2 * (n₁ : ℤ)))]

include E in
theorem dyn_support {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) (hw : w₀ * (9 / 10) ≤ |R.g t|)
    (h1 : w₀ < 1) : DA t = AR t := by
  simp only [dynA, Race.runA]
  exact E.support _ _ _ (far_of_abs h1 hw (R.abs_g_le ht.1 ht.2))

include E in
theorem dynT_support {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) (hw : w₀ * (9 / 10) ≤ |R.r * R.g t|)
    (h1 : w₀ < 1) : DT t = TT t := by
  simp only [dynT, Race.runT]
  exact E.support _ _ _ (far_of_abs h1 hw (R.abs_r_g_le_one ht))

include E in
theorem dyn_near_T {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) : en (DT t - BT t) ≤ ε :=
  E.nearBase _ _ _ (R.abs_r_g_le_one ht)

include E in
theorem dyn_near_A {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) : en (DA t - BA t) ≤ ε :=
  E.nearBase _ _ _ (R.abs_g_le ht.1 ht.2)

include E in
theorem smooth_DT : ContDiff ℝ ∞ DT := by
  have hrg : ContDiff ℝ ∞ (fun t => R.r * R.g t) := contDiff_const.mul R.contDiff_g
  have hV : ContDiff ℝ ∞ (fun t => VtR (R.r ^ n₁) (R.r * R.g t)) := (contDiff_VtR _).comp hrg
  have hs : ContDiff ℝ ∞ (sched R w₀) := by
    unfold sched; fun_prop
  have h := E.smooth.comp (hs.prodMk (hrg.prodMk hV))
  exact h

include h0 E in
theorem smooth_DA : ContDiff ℝ ∞ DA := by
  have hV : ContDiff ℝ ∞ (fun t => VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t)) :=
    (contDiff_VaR R.r h0.ne' _ n₁).comp R.contDiff_g
  have hs : ContDiff ℝ ∞ (sched R w₀) := by
    unfold sched; fun_prop
  have h := E.smooth.comp (hs.prodMk (R.contDiff_g.prodMk hV))
  exact h

/-! #### ゼノンの段階、岸の一致、側のラベル：走者は首の動く部分の外にいる -/

include h0 hc in
theorem pow_ge_w0 {k : ℕ} (hk : k ≤ n₁) : w₀ * (9 / 10) ≤ |R.r ^ k| := by
  have hle : R.r ^ n₁ ≤ R.r ^ k := pow_le_pow_of_le_one R.r_pos.le R.r_lt_one.le hk
  rw [abs_of_pos (pow_pos R.r_pos k)]
  nlinarith

include h0 h1 hc E in
theorem dyn_step_before {k : ℕ} (hk : k < n₁) : DA (R.tn (k + 1)) = DT (R.tn k) := by
  have P := klein_passage R h0 h1 n₁ hc
  have e1 : DA (R.tn (k + 1)) = AR (R.tn (k + 1)) := by
    apply dyn_support R n₁ E (R.tn_mem _) _ h1
    rw [R.g_tn]
    exact pow_ge_w0 R h0 n₁ hc (by omega)
  have e2 : DT (R.tn k) = TT (R.tn k) := by
    apply dynT_support R n₁ E (R.tn_mem _) _ h1
    rw [R.g_tn, ← pow_succ']
    exact pow_ge_w0 R h0 n₁ hc (by omega)
  rw [e1, e2]
  exact P.step_before k hk

include h0 h1 hc E in
theorem dyn_step_after {k : ℕ} (hk : k < n₁) : DT (R.tn' k) = DA (R.tn' (k + 1)) := by
  have P := klein_passage R h0 h1 n₁ hc
  have e1 : DT (R.tn' k) = TT (R.tn' k) := by
    apply dynT_support R n₁ E (R.tn'_mem _) _ h1
    rw [R.g_tn', mul_neg, abs_neg, ← pow_succ']
    exact pow_ge_w0 R h0 n₁ hc (by omega)
  have e2 : DA (R.tn' (k + 1)) = AR (R.tn' (k + 1)) := by
    apply dyn_support R n₁ E (R.tn'_mem _) _ h1
    rw [R.g_tn', abs_neg]
    exact pow_ge_w0 R h0 n₁ hc (by omega)
  rw [e1, e2]
  exact P.step_after k hk

include h0 h1 hc E in
theorem dynT_eq_of_shore {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) (hw : R.r ^ n₁ ≤ |R.r * R.g t|) :
    DT t = TT t :=
  dynT_support R n₁ E ht (by nlinarith) h1

include h0 h1 hc E in
theorem dynA_eq_of_shore {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) (hw : R.r ^ n₁ ≤ |R.g t|) :
    DA t = AR t :=
  dyn_support R n₁ E ht (by nlinarith) h1

/-! #### 距離の評価：基底から F へ -/

theorem en_sub_le' (x y : V3) : en (x - y) ≤ en x + en y := by
  have := en_add_le x (-y)
  rwa [en_neg, ← sub_eq_add_neg] at this

theorem en_lower {a b a' b' : V3} {d ε : ℝ} (hd : d ≤ nsq (a - b)) (ha : en (a' - a) ≤ ε)
    (hb : en (b' - b) ≤ ε) : √d - 2 * ε ≤ en (a' - b') := by
  have e : a - b = (a' - b') - ((a' - a) - (b' - b)) := by abel
  have h1' : en (a - b) ≤ en (a' - b') + en ((a' - a) - (b' - b)) := by
    rw [e]; exact en_sub_le' _ _
  have h2 : en ((a' - a) - (b' - b)) ≤ en (a' - a) + en (b' - b) := en_sub_le' _ _
  have h3 : √d ≤ en (a - b) := Real.sqrt_le_sqrt hd
  linarith

theorem ne_of_en_pos {a b : V3} (h : 0 < en (a - b)) : a ≠ b := by
  intro e
  rw [e, sub_self] at h
  have h0 : en (0 : V3) = 0 := (en_eq_zero_iff 0).mpr rfl
  linarith

theorem en_lt_of_nsq_lt {e : V3} {ε : ℝ} (hε : 0 ≤ ε) (h : nsq e < ε ^ 2) : en e < ε := by
  have h' := Real.sqrt_lt_sqrt (nsq_nonneg e) h
  rw [Real.sqrt_sq hε] at h'
  exact h'

/-! #### 定理 K3⁺ の本体 -/

include h0 h1 hc E in
/-- **定理 K3⁺（本体）**：裏返し F が基底から ε だけ離れ、ε が基底の最小距離 m₁・m_b・m_a と
t∗ での基底と静的な位置の距離に比べて小さければ、`DynamicPassage` が成り立つ。 -/
theorem dynamic_passage_of (hε : 0 < ε) {ε₁ : ℝ} (hεε : ε ≤ ε₁) {m₁ m_b m_a : ℝ}
    (hm₁ : ∀ t ∈ Icc 0 (2 * R.tstar), m₁ ≤ nsq (BT t - BA t)) (h4₁ : 4 * ε ≤ √m₁)
    (hmb : ∀ s t, 0 ≤ s → s ≤ t → t ≤ R.tstar → m_b ≤ nsq (BT t - BA s)) (h4b : 4 * ε ≤ √m_b)
    (hma : ∀ s t, R.tstar ≤ s → s ≤ t → t ≤ 2 * R.tstar → m_a ≤ nsq (BA t - BT s))
    (h4a : 4 * ε ≤ √m_a)
    (hDT : ε < en (BT R.tstar - TT R.tstar)) (hDA : ε < en (BA R.tstar - AR R.tstar)) :
    DynamicPassage R w₀ (R.r ^ n₁) ε₁ n₁ (Shat w₀) (Xhat w₀) F Vt Va := by
  have P := klein_passage R h0 h1 n₁ hc
  have hts := R.tstar_pos
  have hcol : ∀ t ∈ Icc 0 (2 * R.tstar), 2 * ε ≤ en (DT t - DA t) := fun t ht => by
    have := en_lower (hm₁ t ht) (dyn_near_T R n₁ E ht) (dyn_near_A R n₁ E ht)
    linarith
  have hnc : ∀ t ∈ Icc 0 (2 * R.tstar), DT t ≠ DA t := fun t ht =>
    ne_of_en_pos (lt_of_lt_of_le (by positivity) (hcol t ht))
  exact
  { eversion := E.mono h0 hε.le hεε
    rides := fun t ht1 ht2 =>
      ⟨sched_pos h0 R ht1, sched_lt_one h0 R ht2, abs_g_le_of_window R ht1.le ht2.le⟩
    centred := sched_tstar h0 R
    moved := ⟨fun h => by
        have h' := dyn_near_T R n₁ E R.tstar_mem
        rw [h, ← en_neg, neg_sub] at h'
        linarith, fun h => by
        have h' := dyn_near_A R n₁ E R.tstar_mem
        rw [h, ← en_neg, neg_sub] at h'
        linarith⟩
    smooth_T := smooth_DT R n₁ E
    smooth_A := smooth_DA R h0 n₁ E
    static_before := fun t ht => dyn_before R h0 n₁ E ht
    static_after := fun t ht2 ht => dyn_after R h0 h1 n₁ hc E ht2 ht
    no_collision := hnc
    min_dist := ⟨4 * ε ^ 2, by positivity, fun t ht => by
      have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 * ε) (hcol t ht) 2
      rw [en_sq] at h
      linarith⟩
    thick := ⟨ε ^ 2, by positivity, fun t ht e₁ e₂ h₁ h₂ h => by
      have hn := hcol t ht
      have e : DT t - DA t = e₂ - e₁ := by
        calc DT t - DA t = (DT t + e₁) - DA t - e₁ := by abel
          _ = (DA t + e₂) - DA t - e₁ := by rw [h]
          _ = e₂ - e₁ := by abel
      have h1' : en e₁ < ε := en_lt_of_nsq_lt hε.le h₁
      have h2' : en e₂ < ε := en_lt_of_nsq_lt hε.le h₂
      have h3 := en_sub_le' e₂ e₁
      rw [e] at hn
      linarith⟩
    step_before := fun k hk => dyn_step_before R h0 h1 n₁ hc E hk
    step_after := fun k hk => dyn_step_after R h0 h1 n₁ hc E hk
    agree_T := fun t ht hw => by
      rw [dynT_eq_of_shore R h0 h1 n₁ hc E ht hw]; exact P.agree_T t ht hw
    agree_A := fun t ht hw => by
      rw [dynA_eq_of_shore R h0 h1 n₁ hc E ht hw]; exact P.agree_A t ht hw
    side_T_right := fun t ht hw => by
      rw [dynT_eq_of_shore R h0 h1 n₁ hc E ht (le_abs.mpr (Or.inl hw))]
      exact P.side_T_right t ht hw
    side_T_left := fun t ht hw => by
      rw [dynT_eq_of_shore R h0 h1 n₁ hc E ht (le_abs.mpr (Or.inr (by linarith)))]
      exact P.side_T_left t ht hw
    side_A_right := fun t ht hw => by
      rw [dynA_eq_of_shore R h0 h1 n₁ hc E ht (le_abs.mpr (Or.inl hw))]
      exact P.side_A_right t ht hw
    side_A_left := fun t ht hw => by
      rw [dynA_eq_of_shore R h0 h1 n₁ hc E ht (le_abs.mpr (Or.inr (by linarith)))]
      exact P.side_A_left t ht hw
    follow_before := fun s t hs hst ht => by
      have := en_lower (hmb s t hs hst.le ht) (dyn_near_T R n₁ E ⟨by linarith, by linarith⟩)
        (dyn_near_A R n₁ E ⟨hs, by linarith⟩)
      exact ne_of_en_pos (by linarith)
    follow_after := fun s t hs hst ht => by
      have := en_lower (hma s t hs hst.le ht) (dyn_near_A R n₁ E ⟨by linarith, ht⟩)
        (dyn_near_T R n₁ E ⟨by linarith, by linarith⟩)
      exact ne_of_en_pos (by linarith)
    compare_before := P.compare_before
    compare_after := P.compare_after
    compare_zero := P.compare_zero
    compare_not_collision := ⟨P.compare_not_collision.1, hnc R.tstar R.tstar_mem⟩
    approach_T := fun s hs t ht hst => by
      have h2 := (t1_lt_tstar R h0).le
      show nsq (DT t) < nsq (DT s)
      rw [(dyn_before R h0 n₁ E ht.2).1, (dyn_before R h0 n₁ E hs.2).1]
      exact P.approach_T ⟨hs.1, hs.2.trans h2⟩ ⟨ht.1, ht.2.trans h2⟩ hst
    approach_A := fun s hs t ht hst => by
      have h2 := (t1_lt_tstar R h0).le
      show nsq (DA t) < nsq (DA s)
      rw [(dyn_before R h0 n₁ E ht.2).2, (dyn_before R h0 n₁ E hs.2).2]
      exact P.approach_A ⟨hs.1, hs.2.trans h2⟩ ⟨ht.1, ht.2.trans h2⟩ hst
    recede_T := fun s hs t ht hst => by
      have h2 := (tstar_lt_t2 R h0).le
      show nsq (DT s) < nsq (DT t)
      rw [(dyn_after R h0 h1 n₁ hc E hs.1 hs.2).1, (dyn_after R h0 h1 n₁ hc E ht.1 ht.2).1,
        nsq_neg, nsq_neg]
      exact P.approach_T ⟨by linarith [ht.2], by linarith [ht.1]⟩
        ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by linarith)
    recede_A := fun s hs t ht hst => by
      have h2 := (tstar_lt_t2 R h0).le
      show nsq (DA s) < nsq (DA t)
      rw [(dyn_after R h0 h1 n₁ hc E hs.1 hs.2).2, (dyn_after R h0 h1 n₁ hc E ht.1 ht.2).2,
        nsq_neg, nsq_neg]
      exact P.approach_A ⟨by linarith [ht.2], by linarith [ht.1]⟩
        ⟨by linarith [hs.2], by linarith [hs.1]⟩ (by linarith)
    sandwich_T := fun t ht => by
      have ht' : t ∈ Icc 0 (2 * R.tstar) :=
        ⟨(t1_pos R h1).le.trans ht.1, ht.2.trans (t2_lt R h1).le⟩
      have h := (abs_en_sub_en_le (DT t) (BT t)).trans ((dyn_near_T R n₁ E ht').trans hεε)
      have e : en (BT t) = √(nsq (Sig w₀ (R.r * R.g t) 0)) := by
        rw [en, nsq_baseT h0 R ht']
      rw [e] at h
      exact h
    sandwich_A := fun t ht => by
      have ht' : t ∈ Icc 0 (2 * R.tstar) :=
        ⟨(t1_pos R h1).le.trans ht.1, ht.2.trans (t2_lt R h1).le⟩
      have h := (abs_en_sub_en_le (DA t) (BA t)).trans ((dyn_near_A R n₁ E ht').trans hεε)
      have e : en (BA t) = √(nsq (Sig w₀ (R.g t) 0)) := by
        rw [en, nsq_baseA h0 R ht']
      rw [e] at h
      exact h
    near_T := fun t ht => (dyn_near_T R n₁ E ht).trans hεε
    near_A := fun t ht => (dyn_near_A R n₁ E ht).trans hεε
    base_tstar := Model.base_tstar h0 R (hc_pos R h0 n₁ hc) n₁
    base_rotation := Model.base_rotation h0 h1 R hc n₁
    flips_middle := fun v => flips_middle h0 h1 E v
    one_sided_all := fun s => one_sided_all E s }

include h0 h1 hc in
/-- **定理 K3⁺（存在）**：w₀ ≤ rⁿ¹、ε > 0 について、`DynamicPassage` を満たす裏返し F がある。
ε′ := min(ε, √m₁/4, √m_b/4, √m_a/4, D_T/2, D_A/2) で `neck_eversion` を使う。 -/
theorem dynamic_passage_gen (hε : 0 < ε) :
    ∃ F : ℝ → ℝ → ℝ → V3, DynamicPassage R w₀ (R.r ^ n₁) ε n₁ (Shat w₀) (Xhat w₀) F Vt Va := by
  have hcp := hc_pos R h0 n₁ hc
  obtain ⟨m₁, hm₁, hm₁'⟩ := base_min h0 h1 R hcp n₁
  obtain ⟨m_b, hmb, hmb'⟩ := base_follow_min_before h0 h1 R hcp n₁
  obtain ⟨m_a, hma, hma'⟩ := base_follow_min_after h0 h1 R hcp n₁
  have hAA : 0 < AA w₀ 0 := by rw [AA_zero]; exact aa_pos (rho_pos h0.ne' 0)
  have hBB : 0 < BB w₀ 0 := BB_pos h0 h1 0
  obtain ⟨eT, eA⟩ := Model.base_tstar h0 R hcp n₁
  have hT : BT R.tstar ≠ TT R.tstar := by
    rw [eT, runT_Shat_eq R h0 h1 _ R.tstar_mem, reg_Ts R h0 hc]
    intro h
    have := congrArg Prod.fst h
    simp only at this
    linarith
  have hA : BA R.tstar ≠ AR R.tstar := by
    rw [eA, runA_Shat_eq R h0 h1 _ R.tstar_mem, reg_As R h0 hc n₁]
    intro h
    have := congrArg (fun q : V3 => q.2.2) h
    simp only at this
    linarith
  have hDT : 0 < en (BT R.tstar - TT R.tstar) := en_pos_of_ne (sub_ne_zero.mpr hT)
  have hDA : 0 < en (BA R.tstar - AR R.tstar) := en_pos_of_ne (sub_ne_zero.mpr hA)
  have hs₁ : 0 < √m₁ := Real.sqrt_pos.mpr hm₁
  have hsb : 0 < √m_b := Real.sqrt_pos.mpr hmb
  have hsa : 0 < √m_a := Real.sqrt_pos.mpr hma
  -- ε′ の選択
  have hm₁0 : 0 < m₁ := hm₁
  have hmb0 : 0 < m_b := hmb
  have hma0 : 0 < m_a := hma
  obtain ⟨ε', hε'pos, hε'ε, h4₁, h4b, h4a, hDT', hDA'⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
      4 * ε' ≤ √m₁ ∧ 4 * ε' ≤ √m_b ∧ 4 * ε' ≤ √m_a ∧
      ε' < en (BT R.tstar - TT R.tstar) ∧ ε' < en (BA R.tstar - AR R.tstar) := by
    generalize hD₁ : en (BT R.tstar - TT R.tstar) = D₁ at hDT ⊢
    generalize hD₂ : en (BA R.tstar - AR R.tstar) = D₂ at hDA ⊢
    refine ⟨min ε (min (√m₁ / 4) (min (√m_b / 4) (min (√m_a / 4) (min (D₁ / 2) (D₂ / 2))))),
      ?_, min_le_left _ _, ?_, ?_, ?_, ?_, ?_⟩
    · exact lt_min hε (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity)
        (lt_min (by positivity) (by positivity)))))
    · have h : min ε (min (√m₁ / 4) (min (√m_b / 4) (min (√m_a / 4) (min (D₁ / 2) (D₂ / 2))))) ≤
          √m₁ / 4 := min_le_of_right_le (min_le_left _ _)
      linarith
    · have h : min ε (min (√m₁ / 4) (min (√m_b / 4) (min (√m_a / 4) (min (D₁ / 2) (D₂ / 2))))) ≤
          √m_b / 4 := min_le_of_right_le (min_le_of_right_le (min_le_left _ _))
      linarith
    · have h : min ε (min (√m₁ / 4) (min (√m_b / 4) (min (√m_a / 4) (min (D₁ / 2) (D₂ / 2))))) ≤
          √m_a / 4 :=
        min_le_of_right_le (min_le_of_right_le (min_le_of_right_le (min_le_left _ _)))
      linarith
    · have h : min ε (min (√m₁ / 4) (min (√m_b / 4) (min (√m_a / 4) (min (D₁ / 2) (D₂ / 2))))) ≤
          D₁ / 2 :=
        min_le_of_right_le (min_le_of_right_le (min_le_of_right_le (min_le_of_right_le
          (min_le_left _ _))))
      linarith
    · have h : min ε (min (√m₁ / 4) (min (√m_b / 4) (min (√m_a / 4) (min (D₁ / 2) (D₂ / 2))))) ≤
          D₂ / 2 :=
        min_le_of_right_le (min_le_of_right_le (min_le_of_right_le (min_le_of_right_le
          (min_le_right _ _))))
      linarith
  obtain ⟨F, E⟩ := neck_eversion h0 h1 hε'pos
  exact ⟨F, dynamic_passage_of R h0 h1 n₁ hc E hε'pos hε'ε hm₁' h4₁ hmb' h4b hma' h4a hDT' hDA'⟩

end Dynamic

/-! ### 定理 K3⁺：w₀ = c = rⁿ¹ -/

/-- **定理 K3⁺**：n₁ ≥ 1 と ε > 0 について、w₀ = c = rⁿ¹ の首の裏返し F で `DynamicPassage` が成り立つ。 -/
theorem dynamic_passage (R : Race) {n₁ : ℕ} (hn : 1 ≤ n₁) {ε : ℝ} (hε : 0 < ε) :
    ∃ F : ℝ → ℝ → ℝ → V3, DynamicPassage R (R.r ^ n₁) (R.r ^ n₁) ε n₁ (Shat (R.r ^ n₁))
      (Xhat (R.r ^ n₁)) F (VtR (R.r ^ n₁)) (VaR R.r (R.r ^ n₁) (R.r ^ n₁) n₁) :=
  dynamic_passage_gen R (pow_pos R.r_pos n₁) (R.pow_lt_one hn) n₁ le_rfl hε

/-- **t∗ での分離**：F の上の二人の差は (2 bb₀, 0, 0) に 2ε で近い（`base_tstar` と `near_T`・`near_A`）。 -/
theorem DynamicPassage.separation {R : Race} {w₀ c ε : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3}
    {F : ℝ → ℝ → ℝ → V3} {Vt Va : ℝ → ℝ} (P : DynamicPassage R w₀ c ε n₁ S X F Vt Va) :
    √(nsq (dynT R w₀ F Vt R.tstar - dynA R w₀ F Va R.tstar - (2 * BB w₀ 0, 0, 0))) ≤ 2 * ε := by
  obtain ⟨eT, eA⟩ := P.base_tstar
  have hT : en (dynT R w₀ F Vt R.tstar - baseT R w₀ c R.tstar) ≤ ε := P.near_T R.tstar R.tstar_mem
  have hA : en (dynA R w₀ F Va R.tstar - baseA R w₀ c n₁ R.tstar) ≤ ε :=
    P.near_A R.tstar R.tstar_mem
  have e : dynT R w₀ F Vt R.tstar - dynA R w₀ F Va R.tstar - (2 * BB w₀ 0, 0, 0) =
      (dynT R w₀ F Vt R.tstar - baseT R w₀ c R.tstar) -
        (dynA R w₀ F Va R.tstar - baseA R w₀ c n₁ R.tstar) := by
    rw [eT, eA]
    simp only [Prod.ext_iff, Prod.fst_sub, Prod.snd_sub]
    refine ⟨?_, ?_, ?_⟩ <;> ring
  show en _ ≤ 2 * ε
  rw [e]
  have := en_sub_le' (dynT R w₀ F Vt R.tstar - baseT R w₀ c R.tstar)
    (dynA R w₀ F Va R.tstar - baseA R w₀ c n₁ R.tstar)
  linarith

end Zeno.Smale
