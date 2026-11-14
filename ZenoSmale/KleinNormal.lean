/-
# ZenoSmale.KleinNormal : 動く面の法線、走者に沿う側の運搬、各段の M1

`DynamicPassage` の側のラベルの欄（`side_*`）は、助変数の点での静的な法線 X̂ で述べてある。
本ファイルは、それが動く面 F_s 自身の法線 X_{F,s} = ∂ᵥF_s × ∂wF_s に等しいことを証明し、
走者に沿って運んだ動く面の法線について次を示す。

- s ≤ 0 と、首の動く部分の外（9w₀/10 < |w| ≤ 1）では X_{F,s} = X̂。s ≥ 1 の首では X_{F,s}(p) = X̂(φp)。
- X_{F,s}(w, v) は (s, w, v) について連続である。
- 走者に沿う法線 Y_T(t) := X_{F,sched t}(p_T(t)) は連続で消えず、右岸で Front、左岸で Back である
  （動く面の法線での M1）。その間に side = 0 となる時刻があり、そのとき走者は首の中にいる。
- 走者が立つ側と Y の内積の符号は全時刻で変わらない（(P1) の実例）。
- 族の各段 F_s で、左右のホーンは動かず（F_s = G）、どの連続な法線場についても両岸のラベルは逆である
  （各段の M1）。
- 中央円の各点について、side が 0 になる段 s ∈ (0, 1) がある。
-/
import ZenoSmale.KleinDynamic

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff
open Zeno.Model

/-! ### 補助 -/

/-- |w| ∈ [9w₀/10, 2] なら、どの平行移動でも |w − 4k| ≥ 9w₀/10。 -/
theorem far_of_abs_two {w₀ w : ℝ} (h1 : w₀ < 1) (hw : w₀ * (9 / 10) ≤ |w|) (hw2 : |w| ≤ 2)
    (k : ℤ) : (9 / 10) * w₀ ≤ |w - 4 * (k : ℝ)| := by
  rcases eq_or_ne k 0 with hk | hk
  · subst hk; simp; linarith
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast this
    have h := abs_sub_abs_le_abs_sub (4 * (k : ℝ)) w
    rw [abs_sub_comm (4 * (k : ℝ)) w, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h
    nlinarith [abs_nonneg w]

theorem continuous_gradPhi : Continuous gradPhi := by
  unfold gradPhi nsq dot
  fun_prop

theorem continuous_side : Continuous (fun p : V3 × V3 => side p.1 p.2) := by
  have h : (fun p : V3 × V3 => side p.1 p.2) =
      (fun p : V3 × V3 => dot p.1 p.2) ∘ (fun p : V3 × V3 => (gradPhi p.1, p.2)) := rfl
  rw [h]
  exact continuous_dot.comp ((continuous_gradPhi.comp continuous_fst).prodMk continuous_snd)

/-! ### 動く面の法線の同定 -/

section XFid

variable {w₀ ε : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) {F : ℝ → ℝ → ℝ → V3}
  (E : NeckEversion w₀ ε (Shat w₀) F)

include E in
/-- s ≤ 0 では動く面の法線は静的な法線である。 -/
theorem XF_of_start {s : ℝ} (hs : s ≤ 0) (w v : ℝ) : XF F s w v = Xhat w₀ w v := by
  have e : F s = Shat w₀ := by
    funext w' v'
    exact E.start s w' v' hs
  show normalOf (F s) w v = normalOf (Shat w₀) w v
  rw [e]

include h1 E in
/-- 首の動く部分の外（9w₀/10 < |w| < 2）では、どの段でも動く面の法線は静的な法線である。 -/
theorem XF_of_shore (s : ℝ) {w : ℝ} (hw : w₀ * (9 / 10) < |w|) (hw2 : |w| < 2) (v : ℝ) :
    XF F s w v = Xhat w₀ w v := by
  have hopen : IsOpen {p : ℝ × ℝ | w₀ * (9 / 10) < |p.1| ∧ |p.1| < 2} :=
    (isOpen_lt continuous_const (continuous_abs.comp continuous_fst)).inter
      (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const)
  have he : (fun p : ℝ × ℝ => F s p.1 p.2) =ᶠ[𝓝 (w, v)] fun p => Shat w₀ p.1 p.2 := by
    filter_upwards [hopen.mem_nhds (show (w, v) ∈ {p : ℝ × ℝ | w₀ * (9 / 10) < |p.1| ∧ |p.1| < 2}
      from ⟨hw, hw2⟩)] with p hp
    exact E.support s p.1 p.2 (far_of_abs_two h1 hp.1.le hp.2.le)
  exact normalOf_congr (q := (w, v)) he

include h0 h1 E in
/-- s ≥ 1 の首では X_{F,s}(w, v) = X̂(−w, π − v)。端点の首は Ŝ の首の枠つきの像を E で写したものである。 -/
theorem XF_of_finish {s : ℝ} (hs : 1 ≤ s) {w : ℝ} (hw : |w| < 1) (v : ℝ) :
    XF F s w v = Xhat w₀ (-w) (π - v) := by
  have hd := differentiableAt_Shat h0 h1
  simp only [XF, normalOf, Xhat]
  -- ∂ᵥ
  have ev : (fun v' => F s w v') = fun v' => -(Shat w₀ (-w) (π - v')) := by
    funext v'
    exact E.finish s w v' hs hw.le
  have hv : deriv (fun v' => F s w v') v = deriv (fun v => Shat w₀ (-w) v) (π - v) := by
    rw [ev]
    have h := (differentiableAt_partial_v (hd (-w, π - v))).hasDerivAt
    have hl : HasDerivAt (fun v' : ℝ => π - v') (-1) v := (hasDerivAt_id v).const_sub π
    have h2 : HasDerivAt (fun v' => -(Shat w₀ (-w) (π - v')))
        (-((-1 : ℝ) • deriv (fun v => Shat w₀ (-w) v) (π - v))) v := (h.scomp v hl).neg
    rw [h2.deriv, neg_one_smul, neg_neg]
  -- ∂w
  have ew : (fun w' => F s w' v) =ᶠ[𝓝 w] fun w' => -(Shat w₀ (-w') (π - v)) := by
    have hopen : IsOpen {w' : ℝ | |w'| < 1} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds (show w ∈ {w' : ℝ | |w'| < 1} from hw)] with w' hw'
    exact E.finish s w' v hs (le_of_lt hw')
  have hw' : deriv (fun w' => F s w' v) w = deriv (fun w => Shat w₀ w (π - v)) (-w) := by
    rw [ew.deriv_eq]
    have h := (differentiableAt_partial_w (hd (-w, π - v))).hasDerivAt
    have hl : HasDerivAt (fun w' : ℝ => -w') (-1) w := (hasDerivAt_id w).neg
    have h2 : HasDerivAt (fun w' => -(Shat w₀ (-w') (π - v)))
        (-((-1 : ℝ) • deriv (fun w => Shat w₀ w (π - v)) (-w))) w := (h.scomp w hl).neg
    rw [h2.deriv, neg_one_smul, neg_neg]
  rw [hv, hw']

include E in
/-- **動く面の法線は (s, w, v) について連続である**。 -/
theorem continuous_XF_joint : Continuous (fun q : ℝ × ℝ × ℝ => XF F q.1 q.2.1 q.2.2) := by
  have hsm := E.smooth
  have hd : ∀ q : ℝ × ℝ × ℝ, DifferentiableAt ℝ (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) q :=
    fun q => hsm.differentiable (by simp) q
  have hf : Continuous (fun q : ℝ × ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) q) :=
    hsm.continuous_fderiv (by simp)
  have e : (fun q : ℝ × ℝ × ℝ => XF F q.1 q.2.1 q.2.2) = fun q =>
      cross (fderiv ℝ (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) q ((0 : ℝ), (0 : ℝ), (1 : ℝ)))
        (fderiv ℝ (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) q ((0 : ℝ), (1 : ℝ), (0 : ℝ))) := by
    funext q
    obtain ⟨s, w, v⟩ := q
    simp only [XF, normalOf]
    have hlv : HasDerivAt (fun x : ℝ => ((s, w, x) : ℝ × ℝ × ℝ)) ((0 : ℝ), (0 : ℝ), (1 : ℝ)) v :=
      (hasDerivAt_const v s).prodMk ((hasDerivAt_const v w).prodMk (hasDerivAt_id' v))
    have hlw : HasDerivAt (fun x : ℝ => ((s, x, v) : ℝ × ℝ × ℝ)) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) w :=
      (hasDerivAt_const w s).prodMk ((hasDerivAt_id' w).prodMk (hasDerivAt_const w v))
    have h1' := ((hd (s, w, v)).hasFDerivAt.comp_hasDerivAt v hlv).deriv
    have h2' := ((hd (s, w, v)).hasFDerivAt.comp_hasDerivAt w hlw).deriv
    have e1 : (fun v' => F s w v') =
        (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) ∘ (fun x : ℝ => ((s, w, x) : ℝ × ℝ × ℝ)) := rfl
    have e2 : (fun w' => F s w' v) =
        (fun q : ℝ × ℝ × ℝ => F q.1 q.2.1 q.2.2) ∘ (fun x : ℝ => ((s, x, v) : ℝ × ℝ × ℝ)) := rfl
    rw [e1, e2, h1', h2']
  rw [e]
  exact continuous_cross.comp ((hf.clm_apply continuous_const).prodMk (hf.clm_apply continuous_const))

end XFid

/-! ### 静的な面の岸での側 -/

section Shore

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
/-- 右岸 w ∈ [w₀, 1] では、静的な法線 X̂ の側は表（外側）である。 -/
theorem side_Shat_right {w : ℝ} (hw : w₀ ≤ w) (hw1 : w ≤ 1) (v : ℝ) :
    0 < side (Shat w₀ w v) (Xhat w₀ w v) := by
  have hab : |w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [Shat_neck h0 h1 hab, Xhat_eq_Xf_of_abs_le h0 h1 hab]
  obtain ⟨e, k, hk, hX⟩ := (Sig_isNeckSurface h0 h1).right w v hw
  rw [e, hX]
  exact side_right (by linarith) hk v

include h0 h1 in
/-- 左岸 w ∈ [−1, −w₀] では、静的な法線 X̂ の側は裏（内側）である。 -/
theorem side_Shat_left {w : ℝ} (hw1 : -1 ≤ w) (hw : w ≤ -w₀) (v : ℝ) :
    side (Shat w₀ w v) (Xhat w₀ w v) < 0 := by
  have hab : |w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  rw [Shat_neck h0 h1 hab, Xhat_eq_Xf_of_abs_le h0 h1 hab]
  obtain ⟨e, k, hk, hX⟩ := (Sig_isNeckSurface h0 h1).left w v hw
  rw [e, hX]
  exact side_left (by linarith) hk _

end Shore

/-! ### 各段の M1 と中央円 -/

section Stage

variable {w₀ ε : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) {F : ℝ → ℝ → ℝ → V3}
  (E : NeckEversion w₀ ε (Shat w₀) F)

include h0 h1 E in
/-- **右のホーンは動かない**：族のどの段でも、w ∈ [w₀, 1] で F_s = G。 -/
theorem F_horn_right (s : ℝ) {w : ℝ} (hw : w₀ ≤ w) (hw1 : w ≤ 1) (v : ℝ) : F s w v = G w v := by
  have hab : |w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hfar : w₀ * (9 / 10) < |w| := by rw [abs_of_pos (by linarith)]; nlinarith
  rw [E.support s w v (far_of_abs h1 hfar.le hab), Shat_neck h0 h1 hab]
  exact ((Sig_isNeckSurface h0 h1).right w v hw).1

include h0 h1 E in
/-- **左のホーンは動かない**：族のどの段でも、w ∈ [−1, −w₀] で F_s(w, v) = G(w, π − v)。 -/
theorem F_horn_left (s : ℝ) {w : ℝ} (hw1 : -1 ≤ w) (hw : w ≤ -w₀) (v : ℝ) :
    F s w v = G w (π - v) := by
  have hab : |w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hfar : w₀ * (9 / 10) < |w| := by rw [abs_of_neg (by linarith)]; nlinarith
  rw [E.support s w v (far_of_abs h1 hfar.le hab), Shat_neck h0 h1 hab]
  exact ((Sig_isNeckSurface h0 h1).left w v hw).1

include h0 h1 E in
/-- 各段の右岸：動く面の法線の側は表である。 -/
theorem side_F_right (s : ℝ) {w : ℝ} (hw : w₀ ≤ w) (hw1 : w ≤ 1) (v : ℝ) :
    0 < side (F s w v) (XF F s w v) := by
  have hab : |w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hfar : w₀ * (9 / 10) < |w| := by rw [abs_of_pos (by linarith)]; nlinarith
  rw [E.support s w v (far_of_abs h1 hfar.le hab), XF_of_shore h1 E s hfar (by linarith) v]
  exact side_Shat_right h0 h1 hw hw1 v

include h0 h1 E in
/-- 各段の左岸：動く面の法線の側は裏である。 -/
theorem side_F_left (s : ℝ) {w : ℝ} (hw1 : -1 ≤ w) (hw : w ≤ -w₀) (v : ℝ) :
    side (F s w v) (XF F s w v) < 0 := by
  have hab : |w| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hfar : w₀ * (9 / 10) < |w| := by rw [abs_of_neg (by linarith)]; nlinarith
  rw [E.support s w v (far_of_abs h1 hfar.le hab), XF_of_shore h1 E s hfar (by linarith) v]
  exact side_Shat_left h0 h1 hw1 hw v

include h0 h1 E in
/-- **各段の M1**：族のどの段 F_s でも、どの連続な法線場についても、右岸と左岸で Φ のラベルは逆である。 -/
theorem reversal_all (s : ℝ) {n : ℝ × ℝ → V3} (hn : IsNormalField (F s) n) {w₁ w₂ : ℝ}
    (h₁ : w₀ ≤ w₁) (h₁' : w₁ ≤ 1) (h₂ : -1 ≤ w₂) (h₂' : w₂ ≤ -w₀) (v₁ v₂ : ℝ) :
    side (F s w₁ v₁) (n (w₁, v₁)) * side (F s w₂ v₂) (n (w₂, v₂)) < 0 := by
  obtain ⟨c', -, hsm, hs⟩ := normal_rigid (S := F s) (X := XF F s) (continuous_XF E s)
    (XF_ne E s) (fun _ _ => rfl) hn
  have hh := (side_mul_of_rigid (α := ℝ × ℝ) (n := n) (N₀ := fun p => XF F s p.1 p.2) (c := c')
    hsm hs (q₁ := F s w₁ v₁) (q₂ := F s w₂ v₂) (p₁ := (w₁, v₁)) (p₂ := (w₂, v₂))).1
  exact hh (mul_neg_of_pos_of_neg (side_F_right h0 h1 E s h₁ h₁' v₁)
    (side_F_left h0 h1 E s h₂ h₂' v₂))

include h0 h1 E in
/-- **中央円の反転の途中**：中央円の各点について、動く面の法線の side が 0 になる段 s ∈ (0, 1) がある。 -/
theorem flips_stage (v : ℝ) : ∃ s ∈ Ioo (0 : ℝ) 1, side (F s 0 v) (XF F s 0 v) = 0 := by
  have hc : Continuous (fun s : ℝ => side (F s 0 v) (XF F s 0 v)) := by
    have hF : Continuous (fun s : ℝ => F s 0 v) := by
      have h := E.smooth.continuous.comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const) :
          Continuous (fun s : ℝ => ((s, (0 : ℝ), v) : ℝ × ℝ × ℝ)))
      exact h
    have hX : Continuous (fun s : ℝ => XF F s 0 v) := by
      have h := (continuous_XF_joint E).comp
        (continuous_id.prodMk (continuous_const.prodMk continuous_const) :
          Continuous (fun s : ℝ => ((s, (0 : ℝ), v) : ℝ × ℝ × ℝ)))
      exact h
    have h := continuous_side.comp (hF.prodMk hX)
    exact h
  have h0' : 0 < side (F 0 0 v) (XF F 0 0 v) := by
    rw [E.start 0 0 v le_rfl, XF_of_start E le_rfl]
    exact (flips_middle h0 h1 E v).2.2
  have h1' : side (F 1 0 v) (XF F 1 0 v) < 0 := by
    have h := flips_middle h0 h1 E v
    rw [h.1]
    linarith [h.2.2]
  have hivt := intermediate_value_Ioo' (zero_le_one' ℝ) hc.continuousOn
  obtain ⟨s, hs, hval⟩ := hivt (show (0 : ℝ) ∈ Ioo (side (F 1 0 v) (XF F 1 0 v))
    (side (F 0 0 v) (XF F 0 0 v)) from ⟨h1', h0'⟩)
  exact ⟨s, hs, hval⟩

end Stage

/-! ### 走者に沿う動く面の法線 -/

/-- 亀の足もとの、動く面の法線 Y_T(t) = X_{F,sched t}(r g(t), Vt(r g(t)))。 -/
def dynNT (R : Race) (w₀ : ℝ) (F : ℝ → ℝ → ℝ → V3) (Vt : ℝ → ℝ) (t : ℝ) : V3 :=
  XF F (sched R w₀ t) (R.r * R.g t) (Vt (R.r * R.g t))

/-- アキレスの足もとの、動く面の法線 Y_A(t) = X_{F,sched t}(g(t), Va(g(t)))。 -/
def dynNA (R : Race) (w₀ : ℝ) (F : ℝ → ℝ → ℝ → V3) (Va : ℝ → ℝ) (t : ℝ) : V3 :=
  XF F (sched R w₀ t) (R.g t) (Va (R.g t))

section Carry

variable (R : Race) {w₀ ε : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) (n₁ : ℕ) (hc : w₀ ≤ R.r ^ n₁)
  {F : ℝ → ℝ → ℝ → V3} (E : NeckEversion w₀ ε (Shat w₀) F)

local notation "Vt" => VtR (R.r ^ n₁)
local notation "Va" => VaR R.r w₀ (R.r ^ n₁) n₁
local notation "DT" => dynT R w₀ F (VtR (R.r ^ n₁))
local notation "DA" => dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁)
local notation "YT" => dynNT R w₀ F (VtR (R.r ^ n₁))
local notation "YA" => dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁)

include E in
theorem continuous_dynNT : Continuous YT := by
  have hrg : Continuous (fun t => R.r * R.g t) := continuous_const.mul R.continuous_g
  have hV : Continuous (fun t => VtR (R.r ^ n₁) (R.r * R.g t)) :=
    (contDiff_VtR _).continuous.comp hrg
  have h := (continuous_XF_joint E).comp ((continuous_sched R w₀).prodMk (hrg.prodMk hV))
  exact h

include h0 E in
theorem continuous_dynNA : Continuous YA := by
  have hV : Continuous (fun t => VaR R.r w₀ (R.r ^ n₁) n₁ (R.g t)) :=
    (contDiff_VaR R.r h0.ne' _ n₁).continuous.comp R.continuous_g
  have h := (continuous_XF_joint E).comp
    ((continuous_sched R w₀).prodMk (R.continuous_g.prodMk hV))
  exact h

include E in
theorem dynNT_ne (t : ℝ) : YT t ≠ wp := XF_ne E _ _ _

include E in
theorem dynNA_ne (t : ℝ) : YA t ≠ wp := XF_ne E _ _ _

include h0 h1 hc E in
/-- 岸では、亀の足もとの動く面の法線は静的な法線である。 -/
theorem dynNT_of_shore {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) (hw : R.r ^ n₁ ≤ |R.r * R.g t|) :
    YT t = Xhat w₀ (R.r * R.g t) (Vt (R.r * R.g t)) :=
  XF_of_shore h1 E _ (by nlinarith) (lt_of_le_of_lt (R.abs_r_g_le_one ht) (by norm_num)) _

include h0 h1 hc E in
/-- 岸では、アキレスの足もとの動く面の法線は静的な法線である。 -/
theorem dynNA_of_shore {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) (hw : R.r ^ n₁ ≤ |R.g t|) :
    YA t = Xhat w₀ (R.g t) (Va (R.g t)) :=
  XF_of_shore h1 E _ (by nlinarith) (lt_of_le_of_lt (R.abs_g_le ht.1 ht.2) (by norm_num)) _

include E in
/-- **(P1) の実例**：亀が立つ側 n（連続で消えず、動く面の法線に平行）と動く面の法線の内積は、
裏返しの窓の中を含む全時刻で符号を変えない。 -/
theorem dyn_intrinsic_T {n : ℝ → V3} (hn : Continuous n) (hn0 : ∀ t, n t ≠ wp)
    (hpar : ∀ t, cross (n t) (YT t) = wp) :
    (∀ t, 0 < dot (n t) (YT t)) ∨ (∀ t, dot (n t) (YT t) < 0) :=
  intrinsic_side_const (continuous_dynNT R n₁ E) (dynNT_ne R n₁ E) hn hn0 hpar

include h0 E in
/-- **(P1) の実例**（アキレス）。 -/
theorem dyn_intrinsic_A {n : ℝ → V3} (hn : Continuous n) (hn0 : ∀ t, n t ≠ wp)
    (hpar : ∀ t, cross (n t) (YA t) = wp) :
    (∀ t, 0 < dot (n t) (YA t)) ∨ (∀ t, dot (n t) (YA t) < 0) :=
  intrinsic_side_const (continuous_dynNA R h0 n₁ E) (dynNA_ne R n₁ E) hn hn0 hpar

end Carry

/-! ### `DynamicPassage` の帰結：動く面の法線での側のラベル -/

section Labels

variable {R : Race} {w₀ ε : ℝ} {n₁ : ℕ} {F : ℝ → ℝ → ℝ → V3}

local notation "Vt" => VtR (R.r ^ n₁)
local notation "Va" => VaR R.r w₀ (R.r ^ n₁) n₁
local notation "DT" => dynT R w₀ F (VtR (R.r ^ n₁))
local notation "DA" => dynA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁)
local notation "YT" => dynNT R w₀ F (VtR (R.r ^ n₁))
local notation "YA" => dynNA R w₀ F (VaR R.r w₀ (R.r ^ n₁) n₁)

variable (h0 : 0 < w₀) (h1 : w₀ < 1) (hc : w₀ ≤ R.r ^ n₁)
  (P : DynamicPassage R w₀ (R.r ^ n₁) ε n₁ (Shat w₀) (Xhat w₀) F (VtR (R.r ^ n₁))
    (VaR R.r w₀ (R.r ^ n₁) n₁))

include h0 h1 hc P in
/-- **動く面の法線での M1（亀、右岸）**。 -/
theorem DynamicPassage.side_T_right_dyn {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar))
    (hw : R.r ^ n₁ ≤ R.r * R.g t) : Front (DT t) (YT t) := by
  rw [dynNT_of_shore R h0 h1 n₁ hc P.eversion ht (le_abs.mpr (Or.inl hw))]
  exact P.side_T_right t ht hw

include h0 h1 hc P in
/-- **動く面の法線での M1（亀、左岸）**。 -/
theorem DynamicPassage.side_T_left_dyn {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar))
    (hw : R.r * R.g t ≤ -R.r ^ n₁) : Back (DT t) (YT t) := by
  rw [dynNT_of_shore R h0 h1 n₁ hc P.eversion ht (le_abs.mpr (Or.inr (by linarith)))]
  exact P.side_T_left t ht hw

include h0 h1 hc P in
/-- **動く面の法線での M1（アキレス、右岸）**。アキレスは −Y の側に立つ。 -/
theorem DynamicPassage.side_A_right_dyn {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar))
    (hw : R.r ^ n₁ ≤ R.g t) : Back (DA t) (-YA t) := by
  rw [dynNA_of_shore R h0 h1 n₁ hc P.eversion ht (le_abs.mpr (Or.inl hw))]
  exact P.side_A_right t ht hw

include h0 h1 hc P in
/-- **動く面の法線での M1（アキレス、左岸）**。 -/
theorem DynamicPassage.side_A_left_dyn {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar))
    (hw : R.g t ≤ -R.r ^ n₁) : Front (DA t) (-YA t) := by
  rw [dynNA_of_shore R h0 h1 n₁ hc P.eversion ht (le_abs.mpr (Or.inr (by linarith)))]
  exact P.side_A_left t ht hw

include h0 h1 hc P in
/-- **側のラベルの交換の時刻（亀）**：亀の足もとで動く面の法線の side が 0 になる時刻があり、
そのとき亀は首の中（|r g| < rⁿ¹）にいる。n₁ ≥ 1 を使う。 -/
theorem DynamicPassage.side_zero_T (hn : 1 ≤ n₁) :
    ∃ t ∈ Ioo 0 (2 * R.tstar), |R.r * R.g t| < R.r ^ n₁ ∧ side (DT t) (YT t) = 0 := by
  have hts := R.tstar_pos
  have hr0 := R.r_pos
  have hpow : R.r ^ n₁ ≤ R.r := by
    have := pow_le_pow_of_le_one hr0.le R.r_lt_one.le hn
    simpa using this
  have hcont : Continuous (fun t => side (DT t) (YT t)) := by
    have h := continuous_side.comp
      (P.smooth_T.continuous.prodMk (continuous_dynNT R n₁ P.eversion))
    exact h
  have hg0 : R.g 0 = 1 := by rw [R.g_eq]; simp
  have hg2 : R.g (2 * R.tstar) = -1 := by
    rw [R.g_eq]; field_simp; ring
  have ha : 0 < side (DT 0) (YT 0) :=
    P.side_T_right_dyn h0 h1 hc ⟨le_rfl, by linarith⟩ (by rw [hg0, mul_one]; exact hpow)
  have hb : side (DT (2 * R.tstar)) (YT (2 * R.tstar)) < 0 :=
    P.side_T_left_dyn h0 h1 hc ⟨by linarith, le_rfl⟩ (by rw [hg2]; linarith)
  have hivt := intermediate_value_Ioo' (by linarith : (0 : ℝ) ≤ 2 * R.tstar) hcont.continuousOn
  obtain ⟨t, ht, hval⟩ := hivt (show (0 : ℝ) ∈ Ioo (side (DT (2 * R.tstar)) (YT (2 * R.tstar)))
    (side (DT 0) (YT 0)) from ⟨hb, ha⟩)
  refine ⟨t, ht, ?_, hval⟩
  have htI : t ∈ Icc 0 (2 * R.tstar) := ⟨ht.1.le, ht.2.le⟩
  rw [abs_lt]
  constructor
  · by_contra hcon
    push Not at hcon
    have := P.side_T_left_dyn h0 h1 hc htI hcon
    simp only [Back] at this
    linarith
  · by_contra hcon
    push Not at hcon
    have := P.side_T_right_dyn h0 h1 hc htI hcon
    simp only [Front] at this
    linarith

include h0 h1 hc P in
/-- **側のラベルの交換の時刻（アキレス）**。 -/
theorem DynamicPassage.side_zero_A :
    ∃ t ∈ Ioo 0 (2 * R.tstar), |R.g t| < R.r ^ n₁ ∧ side (DA t) (-YA t) = 0 := by
  have hts := R.tstar_pos
  have hr0 := R.r_pos
  have hpow : R.r ^ n₁ ≤ 1 := pow_le_one₀ hr0.le R.r_lt_one.le
  have hcont : Continuous (fun t => side (DA t) (-YA t)) := by
    have h := continuous_side.comp
      (P.smooth_A.continuous.prodMk (continuous_dynNA R h0 n₁ P.eversion).neg)
    exact h
  have hg0 : R.g 0 = 1 := by rw [R.g_eq]; simp
  have hg2 : R.g (2 * R.tstar) = -1 := by
    rw [R.g_eq]; field_simp; ring
  have ha : side (DA 0) (-YA 0) < 0 :=
    P.side_A_right_dyn h0 h1 hc ⟨le_rfl, by linarith⟩ (by rw [hg0]; exact hpow)
  have hb : 0 < side (DA (2 * R.tstar)) (-YA (2 * R.tstar)) :=
    P.side_A_left_dyn h0 h1 hc ⟨by linarith, le_rfl⟩ (by rw [hg2]; linarith)
  have hivt := intermediate_value_Ioo (by linarith : (0 : ℝ) ≤ 2 * R.tstar) hcont.continuousOn
  obtain ⟨t, ht, hval⟩ := hivt (show (0 : ℝ) ∈ Ioo (side (DA 0) (-YA 0))
    (side (DA (2 * R.tstar)) (-YA (2 * R.tstar))) from ⟨ha, hb⟩)
  refine ⟨t, ht, ?_, hval⟩
  have htI : t ∈ Icc 0 (2 * R.tstar) := ⟨ht.1.le, ht.2.le⟩
  rw [abs_lt]
  constructor
  · by_contra hcon
    push Not at hcon
    have := P.side_A_left_dyn h0 h1 hc htI hcon
    simp only [Front] at this
    linarith
  · by_contra hcon
    push Not at hcon
    have := P.side_A_right_dyn h0 h1 hc htI hcon
    simp only [Back] at this
    linarith

end Labels

end Zeno.Smale
