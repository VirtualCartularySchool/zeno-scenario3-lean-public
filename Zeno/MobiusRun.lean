/-
# Zeno.MobiusRun : 射影平面の面と、その上の走者（読み M2）

平面 α のはめ込み f（ホーンと中心では γ、芯の近くでは C∘y⁻¹）から、円柱の上の面
  S(w, v) = f(e^{iv}/w)（w ≠ 0）、S(0, v) = C(0, v)
を作る。S は τ(w, v) = (−w, v + π) で不変で、法線 X は τ で反転する。
面の性質を構造体 `IsMobiusSurface` にまとめ、走者の定理はこの構造体だけから証明する。
-/
import Zeno.Mobius

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

/-! ### 偏微分 -/

theorem fderiv_apply_of_partials' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {w v : ℝ} {W V : F}
    (hf : DifferentiableAt ℝ f (w, v))
    (hw : HasDerivAt (fun w => f (w, v)) W w) (hv : HasDerivAt (fun v => f (w, v)) V v)
    (ξ : ℝ × ℝ) : fderiv ℝ f (w, v) ξ = ξ.1 • W + ξ.2 • V := by
  have h1 : fderiv ℝ f (w, v) (1, 0) = W := by
    have hl : HasDerivAt (fun x : ℝ => ((x, v) : ℝ × ℝ)) (1, 0) w :=
      (hasDerivAt_id' w).prodMk (hasDerivAt_const w v)
    exact (hf.hasFDerivAt.comp_hasDerivAt w hl).unique hw
  have h2 : fderiv ℝ f (w, v) (0, 1) = V := by
    have hl : HasDerivAt (fun x : ℝ => ((w, x) : ℝ × ℝ)) (0, 1) v :=
      (hasDerivAt_const v w).prodMk (hasDerivAt_id' v)
    exact (hf.hasFDerivAt.comp_hasDerivAt v hl).unique hv
  have e : ξ = ξ.1 • ((1, 0) : ℝ × ℝ) + ξ.2 • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  conv_lhs => rw [e]
  rw [map_add, map_smul, map_smul, h1, h2]

/-- 微分可能な面の偏導関数は全微分の値である。 -/
theorem deriv_w_eq {f : ℝ × ℝ → V3} {w v : ℝ} (hf : DifferentiableAt ℝ f (w, v)) :
    deriv (fun w => f (w, v)) w = fderiv ℝ f (w, v) (1, 0) := by
  have hl : HasDerivAt (fun x : ℝ => ((x, v) : ℝ × ℝ)) (1, 0) w :=
    (hasDerivAt_id' w).prodMk (hasDerivAt_const w v)
  exact (hf.hasFDerivAt.comp_hasDerivAt w hl).deriv

theorem deriv_v_eq {f : ℝ × ℝ → V3} {w v : ℝ} (hf : DifferentiableAt ℝ f (w, v)) :
    deriv (fun v => f (w, v)) v = fderiv ℝ f (w, v) (0, 1) := by
  have hl : HasDerivAt (fun x : ℝ => ((w, x) : ℝ × ℝ)) (0, 1) v :=
    (hasDerivAt_const v w).prodMk (hasDerivAt_id' v)
  exact (hf.hasFDerivAt.comp_hasDerivAt v hl).deriv

/-! ### 射影平面の面 -/

/-- 面 S。w ≠ 0 では平面 α の点 y = e^{iv}/w の像、w = 0（無限遠直線）では芯の円。 -/
def mobS (f : ℝ × ℝ → V3) (k : ℝ) (w v : ℝ) : V3 :=
  if w = 0 then mobC k 0 v else f (Ypp (w, v))

/-- S の法線 ∂S/∂v × ∂S/∂w。 -/
def mobX (f : ℝ × ℝ → V3) (k : ℝ) (w v : ℝ) : V3 :=
  cross (deriv (fun v => mobS f k w v) v) (deriv (fun w => mobS f k w v) w)

/-- **読み M2 の面の条件**。 -/
structure IsMobiusSurface (k δ w₀ ε : ℝ) (S X : ℝ → ℝ → V3) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × ℝ => S p.1 p.2)
  periodic : ∀ w v, S w (v + 2 * π) = S w v
  deck : ∀ w v, S (-w) (v + π) = S w v
  normal : ∀ w v, X w v = cross (deriv (fun v => S w v) v) (deriv (fun w => S w v) w)
  normal_cont : Continuous (fun p : ℝ × ℝ => X p.1 p.2)
  normal_ne : ∀ w v, X w v ≠ wp
  normal_deck : ∀ w v, X (-w) (v + π) = -X w v
  immersion : ∀ p, Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => S p.1 p.2) p)
  core : ∀ w v, |w| ≤ δ → S w v = mobC k w v
  horn : ∀ w v, w₀ ≤ |w| → w ^ 2 ≤ 2 → S w v = foldG w v
  near : ∀ w v, w ≠ 0 → dist (S w v) (bsM k δ w₀ (Ypp (w, v))) ≤ ε

/-- 平面の条件（h 原理の結論の形）。 -/
structure IsMobPlane (k δ w₀ ε : ℝ) (f : ℝ × ℝ → V3) : Prop where
  smooth : ContDiff ℝ ∞ f
  immersion : ∀ y, Function.Injective (fderiv ℝ f y)
  fixed : ∀ y, (tau y ≤ mT0 w₀ ∨ mT0 w₀ + 5 * mDl δ w₀ ≤ tau y) → f y = bsM k δ w₀ y
  close : ∀ y, dist (f y) (bsM k δ w₀ y) ≤ ε

section Surface

variable {k δ w₀ ε : ℝ} {f : ℝ × ℝ → V3}

theorem mobS_core (hok : MobOK k δ w₀) (hf : IsMobPlane k δ w₀ ε f) {w : ℝ} (hw : |w| ≤ δ)
    (v : ℝ) : mobS f k w v = mobC k w v := by
  unfold mobS
  split_ifs with h0
  · rw [h0]
  · have ht : tau (Ypp (w, v)) = 1 / w ^ 2 := tau_Ypp h0 v
    have hw2 : w ^ 2 ≤ δ ^ 2 := by rw [← sq_abs w]; exact pow_le_pow_left₀ (abs_nonneg w) hw 2
    have hge : 1 / δ ^ 2 ≤ tau (Ypp (w, v)) := by
      rw [ht]; exact one_div_le_one_div_of_le (by positivity) hw2
    have h5 : mT0 w₀ + 5 * mDl δ w₀ = 1 / δ ^ 2 := MobOK.T5_eq
    rw [hf.fixed _ (Or.inr (by linarith)),
      bsM_eq_mobCy hok (by linarith [hok.dl_pos]), mobCy_Ypp k h0 v]

theorem mobS_horn (hok : MobOK k δ w₀) (hf : IsMobPlane k δ w₀ ε f) {w : ℝ} (hw : w₀ ≤ |w|)
    (h2 : w ^ 2 ≤ 2) (v : ℝ) : mobS f k w v = foldG w v := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, abs_zero] at hw; linarith [hok.w₀_pos]
  unfold mobS
  simp only [hw0, ite_false]
  have ht : tau (Ypp (w, v)) = 1 / w ^ 2 := tau_Ypp hw0 v
  have hw2 : w₀ ^ 2 ≤ w ^ 2 := by rw [← sq_abs w]; exact pow_le_pow_left₀ hok.w₀_pos.le hw 2
  have hle : tau (Ypp (w, v)) ≤ mT0 w₀ := by
    rw [ht, mT0]; exact one_div_le_one_div_of_le (by have := hok.w₀_pos; positivity) hw2
  rw [hf.fixed _ (Or.inl hle), bsM_eq_planeG hok (by linarith [hok.dl_pos]), planeG_Ypp hw0 h2 v]

theorem mobS_near (hf : IsMobPlane k δ w₀ ε f) {w : ℝ} (hw : w ≠ 0) (v : ℝ) :
    dist (mobS f k w v) (bsM k δ w₀ (Ypp (w, v))) ≤ ε := by
  unfold mobS; simp only [hw, ite_false]; exact hf.close _

theorem mobS_deck (w v : ℝ) : mobS f k (-w) (v + π) = mobS f k w v := by
  unfold mobS
  by_cases h0 : w = 0
  · subst h0
    have := mobC_deck k 0 v
    simp only [neg_zero] at this
    simp [this]
  · simp only [neg_eq_zero, h0, ite_false, Ypp_deck]

theorem mobS_periodic (w v : ℝ) : mobS f k w (v + 2 * π) = mobS f k w v := by
  unfold mobS
  split_ifs
  · exact mobC_periodic k 0 v
  · simp only [Ypp, cos_add_two_pi, sin_add_two_pi]

theorem mobS_eventually_core (hok : MobOK k δ w₀) (hf : IsMobPlane k δ w₀ ε f) {p : ℝ × ℝ}
    (hp : |p.1| < δ) :
    (fun q : ℝ × ℝ => mobS f k q.1 q.2) =ᶠ[𝓝 p] fun q => mobC k q.1 q.2 := by
  have hop : ∀ᶠ q in 𝓝 p, |q.1| < δ :=
    (continuous_abs.comp continuous_fst).continuousAt.eventually (gt_mem_nhds hp)
  filter_upwards [hop] with q hq
  exact mobS_core hok hf hq.le q.2

theorem mobS_eventually_plane {p : ℝ × ℝ} (hp : p.1 ≠ 0) :
    (fun q : ℝ × ℝ => mobS f k q.1 q.2) =ᶠ[𝓝 p] fun q => f (Ypp q) := by
  have hop : ∀ᶠ q in 𝓝 p, q.1 ≠ 0 := continuous_fst.continuousAt.eventually (isOpen_ne.mem_nhds hp)
  filter_upwards [hop] with q hq
  unfold mobS; simp only [hq, ite_false]

theorem contDiff_mobS (hok : MobOK k δ w₀) (hf : IsMobPlane k δ w₀ ε f) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => mobS f k p.1 p.2) := by
  refine contDiff_iff_contDiffAt.mpr fun p => ?_
  by_cases hp : p.1 = 0
  · have hp' : |p.1| < δ := by rw [hp, abs_zero]; exact hok.δ_pos
    exact (contDiff_mobC k).contDiffAt.congr_of_eventuallyEq (mobS_eventually_core hok hf hp')
  · exact (hf.smooth.contDiffAt.comp p (contDiffAt_Ypp hp)).congr_of_eventuallyEq
      (mobS_eventually_plane hp)

theorem fderiv_Ypp_apply {w v : ℝ} (hw : w ≠ 0) (ξ : ℝ × ℝ) :
    fderiv ℝ Ypp (w, v) ξ = ξ.1 • dYw w v + ξ.2 • dYv w v :=
  fderiv_apply_of_partials' ((contDiffAt_Ypp (p := (w, v)) hw).differentiableAt (by simp))
    (hasDerivAt_Ypp_w hw v) (hasDerivAt_Ypp_v w v) ξ

theorem mobC_fderiv_apply (k w v : ℝ) (ξ : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => mobC k q.1 q.2) (w, v) ξ = ξ.1 • mobCw v + ξ.2 • mobCv k w v :=
  fderiv_apply_of_partials ((contDiff_mobC k).differentiable (by simp) _)
    (hasDerivAt_mobC_w k w v) (hasDerivAt_mobC_v k w v) ξ

theorem mobC_immersion {k : ℝ} (hk : k ≠ 0) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (fun q : ℝ × ℝ => mobC k q.1 q.2) p) := by
  refine (injective_iff_map_eq_zero _).mpr fun ξ hξ => ?_
  obtain ⟨w, v⟩ := p
  rw [mobC_fderiv_apply] at hξ
  have h1 : dot (ξ.1 • mobCw v + ξ.2 • mobCv k w v) (mobCw v) = 0 := by rw [hξ]; simp [dot]
  have e1 : dot (ξ.1 • mobCw v + ξ.2 • mobCv k w v) (mobCw v) =
      ξ.1 * dot (mobCw v) (mobCw v) + ξ.2 * dot (mobCv k w v) (mobCw v) := by
    simp only [dot, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]; ring
  rw [e1, dot_mobCw_self, dot_mobCv_mobCw] at h1
  have ha : ξ.1 = 0 := by linarith
  have h2 : ξ.2 • mobCv k w v = 0 := by rw [ha, zero_smul, zero_add] at hξ; exact hξ
  have hb : ξ.2 = 0 := by
    by_contra hb
    have hv0 : mobCv k w v = 0 := (smul_eq_zero.mp h2).resolve_left hb
    have := dot_mobCv_self k w v
    rw [hv0] at this
    simp only [dot, Prod.fst_zero, Prod.snd_zero, mul_zero, add_zero] at this
    have hw : w = 0 := by nlinarith [sq_nonneg w, sq_nonneg (k + w * sin v)]
    subst hw
    have : k ^ 2 = 0 := by nlinarith [sq_nonneg k]
    exact hk (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  exact Prod.ext ha hb

theorem mobS_immersion (hok : MobOK k δ w₀) (hf : IsMobPlane k δ w₀ ε f) (p : ℝ × ℝ) :
    Function.Injective (fderiv ℝ (fun p : ℝ × ℝ => mobS f k p.1 p.2) p) := by
  by_cases hp : p.1 = 0
  · have hp' : |p.1| < δ := by rw [hp, abs_zero]; exact hok.δ_pos
    rw [(mobS_eventually_core hok hf hp').fderiv_eq]
    exact mobC_immersion hok.k_pos.ne' p
  · rw [(mobS_eventually_plane hp).fderiv_eq]
    have hY : DifferentiableAt ℝ Ypp p := (contDiffAt_Ypp hp).differentiableAt (by simp)
    have hF : DifferentiableAt ℝ f (Ypp p) := hf.smooth.differentiable (by simp) _
    rw [show (fun q : ℝ × ℝ => f (Ypp q)) = f ∘ Ypp from rfl, fderiv_comp p hF hY]
    refine (hf.immersion (Ypp p)).comp ?_
    refine (injective_iff_map_eq_zero _).mpr fun ξ hξ => ?_
    obtain ⟨w, v⟩ := p
    have hw' : w ≠ 0 := hp
    have hξ' : fderiv ℝ Ypp (w, v) ξ = 0 := hξ
    rw [fderiv_Ypp_apply hw'] at hξ'
    obtain ⟨h1, h2⟩ := dY_indep hw' v hξ'
    exact Prod.ext h1 h2

theorem cross_ne_of_inj' {L : ℝ × ℝ →L[ℝ] V3} (hL : Function.Injective L) :
    cross (L (0, 1)) (L (1, 0)) ≠ wp := by
  intro h
  have hs := smul_of_cross_eq h
  have hne : L (1, 0) ≠ 0 := by
    intro h0
    have : ((1, 0) : ℝ × ℝ) = 0 := hL (by rw [h0, map_zero])
    simp at this
  have hd : dot (L (1, 0)) (L (1, 0)) ≠ 0 := dot_self_ne (fun h' => hne (by rw [h']; rfl))
  have hz : L ((-dot (L (0, 1)) (L (1, 0)), dot (L (1, 0)) (L (1, 0)))) = 0 := by
    have e : ((-dot (L (0, 1)) (L (1, 0)), dot (L (1, 0)) (L (1, 0))) : ℝ × ℝ) =
        dot (L (1, 0)) (L (1, 0)) • ((0, 1) : ℝ × ℝ) +
          (-dot (L (0, 1)) (L (1, 0))) • ((1, 0) : ℝ × ℝ) := by
      ext <;> simp
    rw [e, map_add, map_smul, map_smul, hs, neg_smul, add_neg_cancel]
  have := hL (hz.trans (map_zero L).symm)
  exact hd (congrArg Prod.snd this)

theorem mobS_isMobius (hok : MobOK k δ w₀) (hf : IsMobPlane k δ w₀ ε f) :
    IsMobiusSurface k δ w₀ ε (mobS f k) (mobX f k) where
  smooth := contDiff_mobS hok hf
  periodic := mobS_periodic
  deck := mobS_deck
  normal := fun _ _ => rfl
  normal_cont := by
    have hS := contDiff_mobS hok hf
    have hd : Continuous (fderiv ℝ (fun p : ℝ × ℝ => mobS f k p.1 p.2)) :=
      hS.continuous_fderiv (by simp)
    have e : (fun p : ℝ × ℝ => mobX f k p.1 p.2) = fun p =>
        cross (fderiv ℝ (fun p : ℝ × ℝ => mobS f k p.1 p.2) p (0, 1))
          (fderiv ℝ (fun p : ℝ × ℝ => mobS f k p.1 p.2) p (1, 0)) := by
      funext p
      have hdp : DifferentiableAt ℝ (fun p : ℝ × ℝ => mobS f k p.1 p.2) (p.1, p.2) :=
        hS.differentiable (by simp) _
      simp only [mobX]
      rw [deriv_v_eq hdp, deriv_w_eq hdp]
    rw [e]
    exact continuous_cross.comp ((hd.clm_apply continuous_const).prodMk
      (hd.clm_apply continuous_const))
  normal_ne := by
    intro w v
    have hS := contDiff_mobS hok hf
    have hdp : DifferentiableAt ℝ (fun p : ℝ × ℝ => mobS f k p.1 p.2) (w, v) :=
      hS.differentiable (by simp) _
    simp only [mobX]
    rw [deriv_v_eq hdp, deriv_w_eq hdp]
    exact cross_ne_of_inj' (mobS_immersion hok hf (w, v))
  normal_deck := by
    intro w v
    simp only [mobX]
    have e1 : (fun v' => mobS f k (-w) v') = fun v' => mobS f k w (v' - π) := by
      funext v'
      have := mobS_deck (f := f) (k := k) w (v' - π)
      rw [sub_add_cancel] at this
      exact this
    have e2 : (fun w' => mobS f k w' (v + π)) = fun w' => mobS f k (-w') v := by
      funext w'
      have := mobS_deck (f := f) (k := k) (-w') v
      rw [neg_neg] at this
      exact this
    have d1 : deriv (fun v' => mobS f k (-w) v') (v + π) = deriv (fun v' => mobS f k w v') v := by
      rw [e1, deriv_comp_sub_const (f := fun u => mobS f k w u), add_sub_cancel_right]
    have d2 : deriv (fun w' => mobS f k w' (v + π)) (-w) = -deriv (fun w' => mobS f k w' v) w := by
      rw [e2, deriv_comp_neg (f := fun u => mobS f k u v), neg_neg]
    rw [d1, d2, cross_neg_right]
  immersion := mobS_immersion hok hf
  core := fun w v hw => mobS_core hok hf hw v
  horn := fun w v hw h2 => mobS_horn hok hf hw h2 v
  near := fun w v hw => mobS_near hf hw v

end Surface

/-! ### 面の一般的な性質 -/

section General

variable {k δ w₀ ε : ℝ} {S X : ℝ → ℝ → V3}

theorem IsMobiusSurface.isNormalField (h : IsMobiusSurface k δ w₀ ε S X) :
    IsNormalField S (fun p => X p.1 p.2) where
  cont := h.normal_cont
  ne := fun p => h.normal_ne p.1 p.2
  perp := fun p => by
    simp only [h.normal p.1 p.2]
    exact ⟨dot_cross_left _ _, dot_cross_right _ _⟩

theorem IsMobiusSurface.normal_periodic (h : IsMobiusSurface k δ w₀ ε S X) (w v : ℝ) :
    X w (v + 2 * π) = X w v := by
  rw [h.normal, h.normal]
  have e1 : (fun v' => S w v') = fun v' => S w (v' + 2 * π) := by
    funext v'; rw [h.periodic]
  have e2 : (fun w' => S w' (v + 2 * π)) = fun w' => S w' v := by
    funext w'; rw [h.periodic]
  rw [e2]
  congr 1
  conv_rhs => rw [e1]
  rw [deriv_comp_add_const (f := fun u => S w u)]

theorem IsMobiusSurface.periodic_nat (h : IsMobiusSurface k δ w₀ ε S X) (w v : ℝ) (n : ℕ) :
    S w (v + n * (2 * π)) = S w v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show v + ((n + 1 : ℕ) : ℝ) * (2 * π) = (v + n * (2 * π)) + 2 * π by push_cast; ring,
      h.periodic, ih]

/-- **一つの側しか持たない**：τ と両立する連続な法線場（α̂ の上の連続な側）は存在しない。 -/
theorem IsMobiusSurface.no_side (h : IsMobiusSurface k δ w₀ ε S X) :
    ¬∃ n : ℝ × ℝ → V3, IsNormalField S n ∧ ∀ w v, n (-w, v + π) = n (w, v) := by
  rintro ⟨n, hn, hinv⟩
  obtain ⟨c, -, hsm, hs⟩ := normal_rigid h.normal_cont h.normal_ne h.normal hn
  have e := hinv 0 0
  rw [hsm, hsm] at e
  simp only at e
  rw [h.normal_deck] at e
  have hX := h.normal_ne 0 0
  have h1 : (c (-0, 0 + π) + c (0, 0)) • X 0 0 = 0 := by
    rw [add_smul, ← e, smul_neg, add_neg_cancel]
  have h2 : c (-0, 0 + π) + c (0, 0) = 0 := by
    rcases smul_eq_zero.mp h1 with h2 | h2
    · exact h2
    · exact absurd h2 (fun h' => hX (by rw [h']; rfl))
  rcases hs with hp | hp
  · linarith [hp (-0, 0 + π), hp (0, 0)]
  · linarith [hp (-0, 0 + π), hp (0, 0)]

/-- **モノドロミー**：無限遠直線を一度横切る閉路（p(1) = τ(p(0))）に沿って連続に運んだ側は、
同じ点に反対の向きで戻る。 -/
theorem IsMobiusSurface.monodromy (h : IsMobiusSurface k δ w₀ ε S X) {γ : ℝ → ℝ × ℝ}
    (hγ : Continuous γ) {n : ℝ → V3} (hn : Continuous n) (hn0 : ∀ s, n s ≠ wp)
    (hpar : ∀ s, cross (n s) (X (γ s).1 (γ s).2) = wp)
    (hloop : γ 1 = (-(γ 0).1, (γ 0).2 + π)) :
    S (γ 1).1 (γ 1).2 = S (γ 0).1 (γ 0).2 ∧ ∃ κ : ℝ, 0 < κ ∧ n 1 = -(κ • n 0) := by
  have hX : Continuous fun s => X (γ s).1 (γ s).2 :=
    h.normal_cont.comp hγ
  obtain ⟨c, -, hsm, hs⟩ := rigid_normal hX (fun s => h.normal_ne _ _) hn hn0 dense_univ
    (fun s _ => hpar s)
  refine ⟨by rw [hloop, h.deck], ?_⟩
  have h1 : n 1 = -(c 1 • X (γ 0).1 (γ 0).2) := by
    rw [hsm 1, hloop, h.normal_deck, smul_neg]
  have hc0 : c 0 ≠ 0 := by rcases hs with hp | hp <;> [exact (hp 0).ne'; exact (hp 0).ne]
  refine ⟨c 1 / c 0, ?_, ?_⟩
  · rcases hs with hp | hp
    · exact div_pos (hp 1) (hp 0)
    · exact div_pos_of_neg_of_neg (hp 1) (hp 0)
  · rw [h1, hsm 0, smul_smul, div_mul_cancel₀ _ hc0]

end General

/-- **両側の面では M2 は起きない**：連結な助変数の空間の上に連続で消えない法線場 N₀ があれば、
どの道に沿って連続に運んだ側も、N₀ に対する向きを変えない。特に閉じた道で反対の側に戻ることはない。 -/
theorem two_sided_no_exchange {α : Type*} [TopologicalSpace α] {N₀ : α → V3}
    (hN : Continuous N₀) (hN0 : ∀ p, N₀ p ≠ wp) {γ : ℝ → α} (hγ : Continuous γ)
    {n : ℝ → V3} (hn : Continuous n) (hn0 : ∀ s, n s ≠ wp)
    (hpar : ∀ s, cross (n s) (N₀ (γ s)) = wp) (hloop : γ 1 = γ 0) :
    ∃ κ : ℝ, 0 < κ ∧ n 1 = κ • n 0 := by
  obtain ⟨c, -, hsm, hs⟩ := rigid_normal (hN.comp hγ) (fun s => hN0 _) hn hn0 dense_univ
    (fun s _ => hpar s)
  have hc0 : c 0 ≠ 0 := by rcases hs with hp | hp <;> [exact (hp 0).ne'; exact (hp 0).ne]
  refine ⟨c 1 / c 0, ?_, ?_⟩
  · rcases hs with hp | hp
    · exact div_pos (hp 1) (hp 0)
    · exact div_pos_of_neg_of_neg (hp 1) (hp 0)
  · rw [hsm 1, hsm 0]
    simp only [Function.comp_apply, hloop, smul_smul, div_mul_cancel₀ _ hc0]

/-! ### ホーンの上の表裏（読み M1） -/

theorem cross_mirror (a b : V3) : cross (mirror a) (mirror b) = -mirror (cross a b) := by
  simp only [cross, mirror]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [Prod.fst_neg, Prod.snd_neg] <;> ring

theorem gradPhi_mirror (q : V3) : gradPhi (mirror q) = mirror (gradPhi q) := by
  simp only [gradPhi, mirror, nsq, dot]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem side_mirror (q n : V3) : side (mirror q) (mirror n) = side q n := by
  simp only [side]; rw [gradPhi_mirror]; simp only [dot, mirror]; ring

theorem nsq_foldG (w v : ℝ) : nsq (foldG w v) = w ^ 2 / D w := by
  rw [← nsq_G w v]
  simp only [nsq, dot, foldG, G]
  rw [show |w| / D w * (|w| / D w) = w / D w * (w / D w) by
    rw [← sq, ← sq, div_pow, div_pow, sq_abs]]

/-- 鏡映の線形写像。 -/
def mirrorL : V3 →L[ℝ] V3 :=
  (-(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))).prod (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

theorem mirrorL_apply (q : V3) : mirrorL q = mirror q := rfl

theorem hasDerivAt_mirror {f : ℝ → V3} {f' : V3} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => mirror (f t)) (mirror f') x := by
  have := mirrorL.hasFDerivAt.comp_hasDerivAt x h
  simpa only [Function.comp_def, mirrorL_apply] using this

theorem mirror_smul (c : ℝ) (q : V3) : mirror (c • q) = c • mirror q := by
  simp only [mirror, Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  refine Prod.ext ?_ rfl; simp only; ring

section Horn

variable {k δ w₀ ε : ℝ} {S X : ℝ → ℝ → V3}

theorem IsMobiusSurface.eventually_horn (h : IsMobiusSurface k δ w₀ ε S X) {w : ℝ}
    (h1 : w₀ < |w|) (h2 : w ^ 2 < 2) (v : ℝ) :
    ∀ᶠ p in 𝓝 ((w, v) : ℝ × ℝ), S p.1 p.2 = foldG p.1 p.2 := by
  have hop : ∀ᶠ p in 𝓝 ((w, v) : ℝ × ℝ), w₀ < |p.1| ∧ p.1 ^ 2 < 2 := by
    have c1 : Continuous fun p : ℝ × ℝ => |p.1| := continuous_abs.comp continuous_fst
    have c2 : Continuous fun p : ℝ × ℝ => p.1 ^ 2 := continuous_fst.pow 2
    exact (c1.continuousAt.eventually (lt_mem_nhds h1)).and
      (c2.continuousAt.eventually (gt_mem_nhds h2))
  filter_upwards [hop] with p hp
  exact h.horn p.1 p.2 hp.1.le hp.2.le

theorem IsMobiusSurface.X_right (h : IsMobiusSurface k δ w₀ ε S X) {w : ℝ} (h0 : 0 < w₀)
    (h1 : w₀ < w) (h2 : w ^ 2 < 2) (v : ℝ) :
    S w v = G w v ∧ X w v = (w ^ 3 / D w ^ 3) • N w v := by
  have hw : 0 < w := h0.trans h1
  refine ⟨by rw [h.horn w v (by rw [abs_of_pos hw]; exact h1.le) h2.le, foldG_of_pos hw.le], ?_⟩
  have hev := h.eventually_horn (w := w) (by rw [abs_of_pos hw]; exact h1) h2 v
  have dv : deriv (fun v' => S w v') v = Tv w v := by
    have hv : (fun v' => S w v') =ᶠ[𝓝 v] fun v' => G w v' := by
      have hc : Continuous fun v' : ℝ => ((w, v') : ℝ × ℝ) := continuous_const.prodMk continuous_id
      have := (hc.tendsto v).eventually hev
      filter_upwards [this] with v' hv'
      rw [hv', foldG_of_pos hw.le]
    rw [hv.deriv_eq]; exact (hasDerivAt_G_v w v).deriv
  have dw : deriv (fun w' => S w' v) w = Tw w v := by
    have hw' : (fun w' => S w' v) =ᶠ[𝓝 w] fun w' => G w' v := by
      have hc : Continuous fun w' : ℝ => ((w', v) : ℝ × ℝ) := continuous_id.prodMk continuous_const
      have h3 := (hc.tendsto w).eventually hev
      have h4 : ∀ᶠ w' in 𝓝 w, 0 < w' := lt_mem_nhds hw
      filter_upwards [h3, h4] with w' hw' hpos
      rw [hw', foldG_of_pos hpos.le]
    rw [hw'.deriv_eq]; exact (hasDerivAt_G_w w v).deriv
  rw [h.normal, dv, dw, cross_Tv_Tw]
  rfl

theorem IsMobiusSurface.X_left (h : IsMobiusSurface k δ w₀ ε S X) {w : ℝ} (h0 : 0 < w₀)
    (h1 : w < -w₀) (h2 : w ^ 2 < 2) (v : ℝ) :
    S w v = mirror (G w v) ∧ X w v = (-(w ^ 3 / D w ^ 3)) • mirror (N w v) := by
  have hw : w < 0 := by linarith
  have habs : w₀ < |w| := by rw [abs_of_neg hw]; linarith
  refine ⟨by rw [h.horn w v habs.le h2.le, foldG_of_neg hw.le], ?_⟩
  have hev := h.eventually_horn habs h2 v
  have dv : deriv (fun v' => S w v') v = mirror (Tv w v) := by
    have hv : (fun v' => S w v') =ᶠ[𝓝 v] fun v' => mirror (G w v') := by
      have hc : Continuous fun v' : ℝ => ((w, v') : ℝ × ℝ) := continuous_const.prodMk continuous_id
      have := (hc.tendsto v).eventually hev
      filter_upwards [this] with v' hv'
      rw [hv', foldG_of_neg hw.le]
    rw [hv.deriv_eq]
    exact (hasDerivAt_mirror (hasDerivAt_G_v w v)).deriv
  have dw : deriv (fun w' => S w' v) w = mirror (Tw w v) := by
    have hw' : (fun w' => S w' v) =ᶠ[𝓝 w] fun w' => mirror (G w' v) := by
      have hc : Continuous fun w' : ℝ => ((w', v) : ℝ × ℝ) := continuous_id.prodMk continuous_const
      have h3 := (hc.tendsto w).eventually hev
      have h4 : ∀ᶠ w' in 𝓝 w, w' < 0 := gt_mem_nhds hw
      filter_upwards [h3, h4] with w' hw' hneg
      rw [hw', foldG_of_neg hneg.le]
    rw [hw'.deriv_eq]
    exact (hasDerivAt_mirror (hasDerivAt_G_w w v)).deriv
  rw [h.normal, dv, dw, cross_mirror, cross_Tv_Tw]
  simp only [mirror, Prod.smul_mk, smul_eq_mul, Prod.neg_mk]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem IsMobiusSurface.front_right (h : IsMobiusSurface k δ w₀ ε S X) {w : ℝ} (h0 : 0 < w₀)
    (h1 : w₀ < w) (h2 : w ^ 2 < 2) (v : ℝ) : 0 < side (S w v) (X w v) := by
  obtain ⟨e1, e2⟩ := h.X_right h0 h1 h2 v
  have hw : 0 < w := h0.trans h1
  rw [e1, e2]
  exact side_right hw (by have := D_pos w; positivity) v

theorem IsMobiusSurface.back_left (h : IsMobiusSurface k δ w₀ ε S X) {w : ℝ} (h0 : 0 < w₀)
    (h1 : w < -w₀) (h2 : w ^ 2 < 2) (v : ℝ) : side (S w v) (X w v) < 0 := by
  obtain ⟨e1, e2⟩ := h.X_left h0 h1 h2 v
  have hw : w < 0 := by linarith
  rw [e1, e2, ← mirror_smul, side_mirror]
  have hk : 0 < -(w ^ 3 / D w ^ 3) := by
    have : w ^ 3 < 0 := Odd.pow_neg (by decide) hw
    have := D_pos w
    rw [neg_pos]; exact div_neg_of_neg_of_pos (by assumption) (by positivity)
  exact side_left hw hk v

/-- **M1 の反転**（どの法線場でも）。 -/
theorem IsMobiusSurface.reversal (h : IsMobiusSurface k δ w₀ ε S X) (h0 : 0 < w₀)
    {n : ℝ × ℝ → V3} (hn : IsNormalField S n) {w₁ w₂ : ℝ} (h₁ : w₀ < w₁) (h₁' : w₁ ^ 2 < 2)
    (h₂ : w₂ < -w₀) (h₂' : w₂ ^ 2 < 2) (v₁ v₂ : ℝ) :
    side (S w₁ v₁) (n (w₁, v₁)) * side (S w₂ v₂) (n (w₂, v₂)) < 0 := by
  obtain ⟨c, -, hsm, hs⟩ := normal_rigid h.normal_cont h.normal_ne h.normal hn
  have hh := (side_mul_of_rigid (α := ℝ × ℝ) (n := n) (N₀ := fun p => X p.1 p.2) (c := c) hsm hs
    (q₁ := S w₁ v₁) (q₂ := S w₂ v₂) (p₁ := (w₁, v₁)) (p₂ := (w₂, v₂))).1
  exact hh (mul_neg_of_pos_of_neg (h.front_right h0 h₁ h₁' v₁) (h.back_left h0 h₂ h₂' v₂))

end Horn

end Zeno.Model
