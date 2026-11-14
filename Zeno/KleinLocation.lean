/-
# Zeno.KleinLocation : 命題 S（自己交差の位置）

S1：外側 w ∈ [w₀, 4 − w₀] で Ŝ は単射（v は 2π を法として）。
外側の子午線は角 Θ(w) の極座標のグラフで、Θ は狭義増加する。
S2：首 |w| < w₀ は球 |q| < |G(w₀, 0)| の中、外側はその外（境界は w = w₀、4 − w₀ だけ）。
S4：首の中の繊維。Σ(w, v) = Σ(w′, v′) なら w′ = ±w で、w′ = w なら v′ ≡ v。

これらは、Ŝ の自己交差がすべて首 |w| < w₀ の中にあることを言う。
-/
import Zeno.Klein

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology

/-! ### 角の等式 -/

theorem exists_int_of_cos_sin {v v' : ℝ} (hc : cos v = cos v') (hs : sin v = sin v') :
    ∃ k : ℤ, v' = v + k * (2 * π) := by
  have h := Real.Angle.cos_sin_inj hc hs
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp h
  refine ⟨-k, ?_⟩
  push_cast
  linarith

/-! ### 極座標の形 -/

/-- 回転面の点 (r cos Θ, r sin Θ cos v, r sin Θ sin v)。 -/
def polar (r Θ v : ℝ) : V3 := (r * cos Θ, r * sin Θ * cos v, r * sin Θ * sin v)

theorem nsq_polar (r Θ v : ℝ) : nsq (polar r Θ v) = r ^ 2 := by
  simp only [nsq, dot, polar]
  have h1 := sin_sq_add_cos_sq Θ
  have h2 := sin_sq_add_cos_sq v
  linear_combination (r ^ 2) * h1 + (r ^ 2 * sin Θ ^ 2) * h2

theorem G_eq_polar (w v : ℝ) : G w v = polar (rG w) (fl w) v := by
  rw [G_eq_aa_bb, ← rG_mul_cos, ← rG_mul_sin]
  rfl

/-- 外側の角 Θ(w)：ホーンで arctan(w²)、管で θ(w)、左のホーンで π − arctan((4 − w)²)。 -/
def oTh (w₀ w : ℝ) : ℝ := if w ≤ 1 then fl w else if w ≤ 3 then thT w₀ w else π - fl (4 - w)

/-- 外側の半径。 -/
def oR (w₀ w : ℝ) : ℝ := if w ≤ 1 then rG w else if w ≤ 3 then RP w₀ (thT w₀ w) else rG (4 - w)

section Outer

variable {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1)

include h0 h1 in
theorem oTh_pos {w : ℝ} (hw0 : 0 < w) : 0 < oTh w₀ w := by
  simp only [oTh]
  split_ifs with ha hb
  · exact arctan_pos.mpr (by positivity)
  · linarith [(thT_mem h0 h1 (by linarith) hb).1, pi_pos]
  · linarith [fl_lt_pi_div_two (4 - w), pi_pos]

include h0 h1 in
theorem oTh_lt_pi {w : ℝ} (hw4 : w < 4) : oTh w₀ w < π := by
  simp only [oTh]
  split_ifs with ha hb
  · linarith [fl_lt_pi_div_two w, pi_pos]
  · linarith [(thT_mem h0 h1 (by linarith) hb).2, pi_pos]
  · push Not at hb
    have h4 : 0 < 4 - w := by linarith
    have : 0 < fl (4 - w) := arctan_pos.mpr (by positivity)
    linarith

include h0 h1 in
theorem oTh_strictMonoOn : StrictMonoOn (oTh w₀) (Icc 0 4) := by
  have hfl := fl_strictMonoOn
  have hth := thT_strictMonoOn h0 h1
  have hfl1 : fl 1 = π / 4 := fl_one
  have hth1 : thT w₀ 1 = π / 4 := thT_one h0 h1
  have hth3 : thT w₀ 3 = 3 * π / 4 := thT_three h0 h1
  intro x hx y hy hxy
  simp only [oTh]
  split_ifs with hx1 hy1 hy3 hx3 hy1' hy3' hy1'' hy3''
  · exact hfl hx.1 hy.1 hxy
  · -- x ≤ 1 < y ≤ 3
    push Not at hy1
    calc fl x ≤ fl 1 := hfl.monotoneOn hx.1 (by norm_num) hx1
      _ = thT w₀ 1 := by rw [hfl1, hth1]
      _ < thT w₀ y := hth ⟨by norm_num, by norm_num⟩ ⟨by linarith, by linarith⟩ hy1
  · -- x ≤ 1, y > 3
    push Not at hy1 hy3
    have h1' : fl x ≤ π / 4 := by rw [← hfl1]; exact hfl.monotoneOn hx.1 (by norm_num) hx1
    have h2' : fl (4 - y) < π / 4 := by
      rw [← hfl1]
      exact hfl (show (0 : ℝ) ≤ 4 - y by linarith [hy.2]) (show (0 : ℝ) ≤ 1 by norm_num)
        (by linarith)
    linarith [pi_pos]
  · exfalso; push Not at hx1; linarith
  · -- 1 < x < y ≤ 3
    push Not at hx1
    exact hth ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hxy
  · -- 1 < x ≤ 3 < y
    push Not at hx1 hy3'
    have h1' : thT w₀ x ≤ 3 * π / 4 := by
      rw [← hth3]; exact hth.monotoneOn ⟨by linarith, by linarith⟩ ⟨by norm_num, by norm_num⟩ hx3
    have h2' : fl (4 - y) < π / 4 := by
      rw [← hfl1]
      exact hfl (show (0 : ℝ) ≤ 4 - y by linarith [hy.2]) (show (0 : ℝ) ≤ 1 by norm_num)
        (by linarith)
    linarith [pi_pos]
  · exfalso; push Not at hx1 hx3; linarith
  · exfalso; push Not at hx1 hx3; linarith
  · -- 3 < x < y
    push Not at hx1 hx3
    have : fl (4 - y) < fl (4 - x) :=
      hfl (show (0 : ℝ) ≤ 4 - y by linarith [hy.2]) (show (0 : ℝ) ≤ 4 - x by linarith [hy.2])
        (by linarith)
    linarith

include h0 h1 in
theorem oTh_injOn : InjOn (oTh w₀) (Icc 0 4) := (oTh_strictMonoOn h0 h1).injOn

include h0 h1 in
theorem oR_pos {w : ℝ} (hw0 : 0 < w) (hw4 : w < 4) : 0 < oR w₀ w := by
  simp only [oR]
  split_ifs with ha hb
  · exact rG_pos hw0
  · exact RP_thT_pos h0 h1 (by linarith) hb
  · exact rG_pos (by linarith)

include h0 h1 in
/-- 外側では Ŝ は極座標の形で書ける。 -/
theorem Shat_eq_polar {w : ℝ} (hw1 : w₀ ≤ w) (hw2 : w ≤ 4 - w₀) (v : ℝ) :
    Shat w₀ w v = polar (oR w₀ w) (oTh w₀ w) v := by
  simp only [oR, oTh]
  split_ifs with ha hb
  · -- ホーン
    rw [Shat_neck h0 h1 (by rw [abs_le]; constructor <;> linarith),
      Sig_right h0 (by nlinarith), G_eq_polar]
  · -- 管
    push Not at ha
    rw [Shat_tube h0 h1 ha.le hb]
    simp only [Tube, sigmaOf, rot2_zero, tubeA, tubeB, polar]
  · -- 左のホーン
    push Not at ha hb
    have hk : kk w = 1 := kk_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    simp only [Shat, hk, Int.cast_one, mul_one, sgn_one, neg_one_mul]
    rw [Strip_eq_Sig_of h0 h1 (by linarith [wa_gt_one h0 h1]), Sig_left h0 (by nlinarith),
      G_eq_aa_bb]
    have e : w - 4 = -(4 - w) := by ring
    rw [e, aa_neg, bb_neg, ← rG_mul_cos, ← rG_mul_sin]
    simp only [polar, cos_pi_sub, sin_pi_sub, cos_neg, sin_neg]
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

include h0 h1 in
theorem sin_oTh_pos {w : ℝ} (hw0 : 0 < w) (hw4 : w < 4) : 0 < sin (oTh w₀ w) :=
  sin_pos_of_pos_of_lt_pi (oTh_pos h0 h1 hw0) (oTh_lt_pi h0 h1 hw4)

include h0 h1 in
/-- **S1**：外側 w ∈ [w₀, 4 − w₀] で Ŝ は単射（v は 2π を法として）。 -/
theorem outer_injective {w w' v v' : ℝ} (hw1 : w₀ ≤ w) (hw2 : w ≤ 4 - w₀) (hw1' : w₀ ≤ w')
    (hw2' : w' ≤ 4 - w₀) (he : Shat w₀ w v = Shat w₀ w' v') :
    w = w' ∧ ∃ k : ℤ, v' = v + k * (2 * π) := by
  rw [Shat_eq_polar h0 h1 hw1 hw2, Shat_eq_polar h0 h1 hw1' hw2'] at he
  have hr : 0 < oR w₀ w := oR_pos h0 h1 (by linarith) (by linarith)
  have hr' : 0 < oR w₀ w' := oR_pos h0 h1 (by linarith) (by linarith)
  -- 半径が等しい
  have hn := congrArg nsq he
  rw [nsq_polar, nsq_polar] at hn
  have hrr : oR w₀ w = oR w₀ w' := (pow_left_inj₀ hr.le hr'.le two_ne_zero).mp hn
  -- 角が等しい
  have h1c := congrArg Prod.fst he
  simp only [polar] at h1c
  rw [hrr] at h1c
  have hcos : cos (oTh w₀ w) = cos (oTh w₀ w') := by
    have := mul_left_cancel₀ hr'.ne' h1c
    exact this
  have hth : oTh w₀ w = oTh w₀ w' :=
    injOn_cos ⟨(oTh_pos h0 h1 (by linarith)).le, (oTh_lt_pi h0 h1 (by linarith)).le⟩
      ⟨(oTh_pos h0 h1 (by linarith)).le, (oTh_lt_pi h0 h1 (by linarith)).le⟩ hcos
  have hww : w = w' :=
    oTh_injOn h0 h1 ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ hth
  refine ⟨hww, ?_⟩
  subst hww
  -- 円の上の角
  have hs : 0 < oR w₀ w * sin (oTh w₀ w) := mul_pos hr (sin_oTh_pos h0 h1 (by linarith) (by linarith))
  have h2c := congrArg (fun q : V3 => q.2.1) he
  have h3c := congrArg (fun q : V3 => q.2.2) he
  simp only [polar] at h2c h3c
  exact exists_int_of_cos_sin (mul_left_cancel₀ hs.ne' h2c) (mul_left_cancel₀ hs.ne' h3c)

/-! ### S2：首は球の中、外側は球の外 -/

theorem nsq_G_w0 (w₀ : ℝ) : nsq (G w₀ 0) = Rad (w₀ ^ 2) := by
  rw [nsq_G]
  simp only [Rad, D]
  congr 1; ring

include h0 h1 in
/-- **S2（首）**：|w| < w₀ で |Ŝ(w, v)| < |G(w₀, 0)|。 -/
theorem neck_inside {w : ℝ} (hw : |w| < w₀) (v : ℝ) : nsq (Shat w₀ w v) < nsq (G w₀ 0) := by
  have hw1 : |w| ≤ 1 := by linarith
  rw [Shat_neck h0 h1 hw1, ← Sig_right h0 (w := w₀) (by nlinarith) 0]
  exact nsq_Sig_lt h0.ne' (by nlinarith) (by rwa [abs_of_pos h0]) (by rw [abs_of_pos h0]; exact h1.le) v 0

include h0 h1 in
/-- **S2（外側）**：w ∈ [w₀, 4 − w₀] で |G(w₀, 0)| ≤ |Ŝ(w, v)|、等号は w = w₀ または w = 4 − w₀ に限る。 -/
theorem outer_outside {w : ℝ} (hw1 : w₀ ≤ w) (hw2 : w ≤ 4 - w₀) (v : ℝ) :
    nsq (G w₀ 0) ≤ nsq (Shat w₀ w v) ∧
      (nsq (G w₀ 0) = nsq (Shat w₀ w v) → w = w₀ ∨ w = 4 - w₀) := by
  rw [nsq_G_w0]
  by_cases ha : w ≤ 1
  · -- ホーン
    rw [Shat_neck h0 h1 (by rw [abs_le]; constructor <;> linarith), Sig_right h0 (by nlinarith),
      nsq_G]
    have e : w ^ 2 / D w = Rad (w ^ 2) := by simp only [Rad, D]; congr 1; ring
    rw [e]
    rcases eq_or_lt_of_le hw1 with heq | hlt
    · subst heq; exact ⟨le_rfl, fun _ => Or.inl rfl⟩
    · have hlt' : Rad (w₀ ^ 2) < Rad (w ^ 2) :=
        Rad_lt (by positivity) (by nlinarith) (by nlinarith)
      exact ⟨hlt'.le, fun h => absurd h hlt'.ne⟩
  · push Not at ha
    by_cases hb : w ≤ 3
    · -- 管
      rw [Shat_tube h0 h1 ha.le hb]
      have hlt := nsq_Tube_gt h0 h1 ha.le hb v
      exact ⟨hlt.le, fun h => absurd h hlt.ne⟩
    · -- 左のホーン
      push Not at hb
      have hk : kk w = 1 := kk_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
      simp only [Shat, hk, Int.cast_one, mul_one, sgn_one, neg_one_mul]
      rw [Strip_eq_Sig_of h0 h1 (by linarith [wa_gt_one h0 h1]), Sig_left h0 (by nlinarith), nsq_G]
      have e : (w - 4) ^ 2 / D (w - 4) = Rad ((4 - w) ^ 2) := by
        simp only [Rad, D]; congr 1 <;> ring
      rw [e]
      rcases eq_or_lt_of_le hw2 with heq | hlt
      · subst heq
        have e2 : (4 - (4 - w₀)) = w₀ := by ring
        rw [e2]
        exact ⟨le_rfl, fun _ => Or.inr rfl⟩
      · have hlt' : Rad (w₀ ^ 2) < Rad ((4 - w) ^ 2) :=
          Rad_lt (by positivity) (by nlinarith) (by nlinarith)
        exact ⟨hlt'.le, fun h => absurd h hlt'.ne⟩

/-! ### S4：首の繊維 -/

theorem rot2_sub (ψ : ℝ) (a b : V3) : rot2 ψ (a - b) = rot2 ψ a - rot2 ψ b := by
  simp only [rot2, Prod.fst_sub, Prod.snd_sub]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_sub, Prod.snd_sub] <;> ring

theorem rot2_injective (ψ : ℝ) : Function.Injective (rot2 ψ) := by
  intro a b h
  have h2 : rot2 ψ (a - b) = wp := by
    rw [rot2_sub, h, sub_self]
    rfl
  have := rot2_eq_wp h2
  have h3 : a - b = 0 := this
  exact sub_eq_zero.mp h3

include h0 h1 in
/-- **S4**：Σ(w, v) = Σ(w′, v′)、|w|, |w′| ≤ w₀ なら w′ = ±w で、w′ = w なら v′ ≡ v (mod 2π)。 -/
theorem neck_fibre {w w' v v' : ℝ} (hw : |w| ≤ w₀) (hw' : |w'| ≤ w₀)
    (he : Sig w₀ w v = Sig w₀ w' v') :
    (w' = w ∨ w' = -w) ∧ (w' = w → ∃ k : ℤ, v' = v + k * (2 * π)) := by
  have hne := h0.ne'
  -- 半径：Rad(hh(w²)) = Rad(hh(w′²))
  have hn := congrArg nsq he
  rw [nsq_Sig hne, nsq_Sig hne] at hn
  have hsq : w ^ 2 ≤ w₀ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hw 2
  have hsq' : w' ^ 2 ≤ w₀ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hw' 2
  have hbound : ∀ x, x ≤ w₀ ^ 2 → hh w₀ x ≤ 1 := fun x hx => by
    calc hh w₀ x ≤ hh w₀ (w₀ ^ 2) := (hh_strictMono hne).monotone hx
      _ = w₀ ^ 2 := hh_of_ge hne (by nlinarith)
      _ ≤ 1 := by nlinarith
  have hhh : hh w₀ (w ^ 2) = hh w₀ (w' ^ 2) := by
    by_contra hc
    rcases lt_or_gt_of_ne hc with hlt | hgt
    · exact absurd hn (Rad_lt (hh_pos hne (sq_nonneg _)).le hlt (hbound _ hsq')).ne
    · exact absurd hn (Rad_lt (hh_pos hne (sq_nonneg _)).le hgt (hbound _ hsq)).ne'
  have hww : w ^ 2 = w' ^ 2 := (hh_strictMono hne).injective hhh
  refine ⟨?_, ?_⟩
  · rcases sq_eq_sq_iff_eq_or_eq_neg.mp hww.symm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hw''
    rw [hw''] at he
    simp only [Sig, sigmaOf] at he
    have h2 := rot2_injective _ he
    have hB := BB_pos h0 h1 w
    have hc : BB w₀ w * cos v = BB w₀ w * cos v' := congrArg (fun q : V3 => q.2.1) h2
    have hs : BB w₀ w * sin v = BB w₀ w * sin v' := congrArg (fun q : V3 => q.2.2) h2
    exact exists_int_of_cos_sin (mul_left_cancel₀ hB.ne' hc) (mul_left_cancel₀ hB.ne' hs)

end Outer

end Zeno.Model
