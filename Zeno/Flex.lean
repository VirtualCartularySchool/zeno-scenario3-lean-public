/-
# Zeno.Flex : 定理 C2（動く面の上の走者）と、平面の裏返しの帰結

α 全体が時刻とともに動く読みである。走者は各時刻に同じ面 f(s(t), ·) の上にいて、ホーンの部分を歩く。
そこでは面は傘の明示式 κ U(φ) に等しい（Smale–Hirsch はホーンを動かさない）。

傘の明示式は複素数の式に書ける：κ U(φ)(1/ρ, v) = κ 𝔾(ρ e^{iφ}, v)。𝔾 の実軸は G である。
比較の差 zₐ − zₜ = (1 − r) z は決して 0 にならないが、実部は符号を変える。
中間値の定理は実部に効き、等号の時刻がある。しかしその時刻に二人は同じ点にいない。
-/
import Zeno.Plane
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology
open scoped ContDiff

local notation "s₀" => Real.smoothTransition

/-! ### 階段の ½ -/

theorem e_lt {x y : ℝ} (hy : 0 < y) (hxy : x < y) : expNegInvGlue x < expNegInvGlue y := by
  by_cases hx : x ≤ 0
  · rw [expNegInvGlue.zero_of_nonpos hx]
    exact expNegInvGlue.pos_of_pos hy
  · push Not at hx
    simp only [expNegInvGlue, not_le.mpr hx, not_le.mpr hy, ite_false]
    apply Real.exp_lt_exp.mpr
    have := inv_strictAnti₀ hx hxy
    linarith

theorem s0_lt_half {x : ℝ} (h : x < 1 / 2) : s₀ x < 1 / 2 := by
  unfold Real.smoothTransition
  have hd := Real.smoothTransition.pos_denom x
  rw [div_lt_iff₀ hd]
  have := e_lt (x := x) (y := 1 - x) (by linarith) (by linarith)
  linarith

theorem s0_gt_half {x : ℝ} (h : 1 / 2 < x) : 1 / 2 < s₀ x := by
  unfold Real.smoothTransition
  have hd := Real.smoothTransition.pos_denom x
  rw [lt_div_iff₀ hd]
  have := e_lt (x := 1 - x) (y := x) (by linarith) (by linarith)
  linarith

/-! ### 平面の裏返し -/

/-- **C3**：平面 α の裏返し。Smale–Hirsch から得られる性質だけを述べる。 -/
structure IsPlaneEversion (κ₀ ε : ℝ) (f : ℝ → ℝ × ℝ → V3) : Prop where
  smooth : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2)
  immersion : ∀ s y, Function.Injective (fderiv ℝ (f s) y)
  fixed : ∀ s y, (s ≤ 0 ∨ 1 ≤ s ∨ 1 ≤ tau y) → f s y = bsP κ₀ s y
  close : ∀ s y, dist (f s y) (bsP κ₀ s y) ≤ ε

/-- 面 f(s, ·) の法線場 ∂₁f × ∂₂f。 -/
def XF (f : ℝ → ℝ × ℝ → V3) (s : ℝ) (y : ℝ × ℝ) : V3 :=
  cross (fderiv ℝ (f s) y (1, 0)) (fderiv ℝ (f s) y (0, 1))

/-- 族の連続な法線場。 -/
structure IsFamilyNormal (f : ℝ → ℝ × ℝ → V3) (n : ℝ × (ℝ × ℝ) → V3) : Prop where
  cont : Continuous n
  ne : ∀ p, n p ≠ wp
  perp : ∀ p ξ, dot (n p) (fderiv ℝ (f p.1) p.2 ξ) = 0

/-- **C3 の帰結**。 -/
structure FamilyFacts (κ₀ ε : ℝ) (f : ℝ → ℝ × ℝ → V3) : Prop where
  /-- 端の時刻では g と −g である。 -/
  start : ∀ s, s ≤ 0 → f s = planeG
  finish : ∀ s, 1 ≤ s → f s = -planeG
  /-- ホーンでは傘の明示式に等しい。 -/
  horn : ∀ s y, 1 ≤ tau y → f s y = kapS κ₀ s • Lam (phiS s) (planeG y)
  /-- ある時刻に α 全体が ℘ の小さな球の中に入る。 -/
  ball : ∀ y, nsq (f (1 / 2) y) ≤ κ₀ ^ 2 + 6 * ε ^ 2
  /-- y → ∞ で ℘ へ、s について一様に。 -/
  decay : ∀ s y, 1 ≤ tau y → nsq (f s y) ≤ 1 / tau y
  /-- 法線場は連続で消えない。 -/
  normal_cont : Continuous (fun p : ℝ × (ℝ × ℝ) => XF f p.1 p.2)
  normal_ne : ∀ s y, XF f s y ≠ wp
  normal_field : IsFamilyNormal f (fun p => XF f p.1 p.2)
  /-- 端の枠の法則は E である：(q, n) ↦ (−q, n)。 -/
  frame_law : ∀ s₁ s₂ y, s₁ ≤ 0 → 1 ≤ s₂ → (f s₂ y, XF f s₂ y) = Everse (f s₁ y, XF f s₁ y)
  /-- 表裏（ラベルによらない形）。 -/
  reversal : ∀ n, IsFamilyNormal f n → ∀ s₁ s₂ y₁ y₂, s₁ ≤ 0 → 1 ≤ s₂ → 1 ≤ tau y₁ → 1 ≤ tau y₂ →
    side (f s₁ y₁) (n (s₁, y₁)) * side (f s₂ y₂) (n (s₂, y₂)) < 0

theorem nsq_smul (k : ℝ) (q : V3) : nsq (k • q) = k ^ 2 * nsq q := by
  simp only [nsq, dot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem nsq_le_of_dist {a b : V3} {ε : ℝ} (h : dist a b ≤ ε) :
    nsq a ≤ 2 * nsq b + 6 * ε ^ 2 := by
  have h1 : |a.1 - b.1| ≤ ε := by
    have : dist a.1 b.1 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_left _ _
    rw [Real.dist_eq] at this
    exact this.trans h
  have h2 : |a.2.1 - b.2.1| ≤ ε := by
    have h3 : dist a.2 b.2 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_right _ _
    have h4 : dist a.2.1 b.2.1 ≤ dist a.2 b.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
    rw [Real.dist_eq] at h4
    exact h4.trans (h3.trans h)
  have h3 : |a.2.2 - b.2.2| ≤ ε := by
    have h3 : dist a.2 b.2 ≤ dist a b := by rw [Prod.dist_eq]; exact le_max_right _ _
    have h4 : dist a.2.2 b.2.2 ≤ dist a.2 b.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
    rw [Real.dist_eq] at h4
    exact h4.trans (h3.trans h)
  have s1 : (a.1 - b.1) ^ 2 ≤ ε ^ 2 := sq_le_sq' (abs_le.mp h1).1 (abs_le.mp h1).2
  have s2 : (a.2.1 - b.2.1) ^ 2 ≤ ε ^ 2 := sq_le_sq' (abs_le.mp h2).1 (abs_le.mp h2).2
  have s3 : (a.2.2 - b.2.2) ^ 2 ≤ ε ^ 2 := sq_le_sq' (abs_le.mp h3).1 (abs_le.mp h3).2
  simp only [nsq, dot]
  nlinarith [sq_nonneg (a.1 - 2 * b.1), sq_nonneg (a.2.1 - 2 * b.2.1),
    sq_nonneg (a.2.2 - 2 * b.2.2)]

/-- 極座標。 -/
theorem exists_polar {y : ℝ × ℝ} (hy : 0 < tau y) :
    ∃ ρ v : ℝ, 0 < ρ ∧ ρ ^ 2 = 1 / tau y ∧ y = (cos v / ρ, sin v / ρ) := by
  let z : ℂ := ⟨y.1, y.2⟩
  have hz : Complex.normSq z = tau y := by
    simp [Complex.normSq_apply, z, tau]; ring
  have hn : ‖z‖ ^ 2 = tau y := by
    rw [← Complex.normSq_eq_norm_sq, hz]
  have hnpos : 0 < ‖z‖ := by
    by_contra h
    have h0 : ‖z‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [h0] at hn
    simp at hn
    linarith
  refine ⟨1 / ‖z‖, Complex.arg z, by positivity, ?_, ?_⟩
  · rw [← hn]; field_simp
  · have h1 : ‖z‖ * cos (Complex.arg z) = z.re := Complex.norm_mul_cos_arg z
    have h2 : ‖z‖ * sin (Complex.arg z) = z.im := Complex.norm_mul_sin_arg z
    refine Prod.ext ?_ ?_
    · have : cos (Complex.arg z) / (1 / ‖z‖) = z.re := by
        rw [← h1]; field_simp
      rw [this]
    · have : sin (Complex.arg z) / (1 / ‖z‖) = z.im := by
        rw [← h2]; field_simp
      rw [this]

/-- ホーンの部分で hn₀ は N の正の倍で、G との組で表（外向き）である。 -/
theorem side_plane_pos {ρ : ℝ} (hρ : 0 < ρ) (h : ρ ^ 2 < 2) (v : ℝ) :
    0 < side (G ρ v) (hC (tau (cos v / ρ, sin v / ρ)) • n0 (cos v / ρ, sin v / ρ)) := by
  rw [n0_polar hρ h, smul_smul]
  refine side_right hρ (mul_pos (hC_pos _) ?_) v
  have := D_pos ρ
  positivity

theorem side_planeG_pos {y : ℝ × ℝ} (hy : 1 ≤ tau y) :
    0 < side (planeG y) (hC (tau y) • n0 y) := by
  obtain ⟨ρ, v, hρ, h2, rfl⟩ := exists_polar (lt_of_lt_of_le one_pos hy)
  have hle : ρ ^ 2 ≤ 1 := by
    rw [h2]
    rw [div_le_one (by linarith)]
    exact hy
  rw [planeG_polar hρ (by linarith)]
  exact side_plane_pos hρ (by linarith) v

theorem planeD_e1 (y : ℝ × ℝ) : planeD y (1, 0) = D1 y := by
  rw [← planeD_eq]; simp

theorem planeD_e2 (y : ℝ × ℝ) : planeD y (0, 1) = D2 y := by
  rw [← planeD_eq]; simp

theorem cross_anti' (a b : V3) : cross a b = -cross b a := by
  simp only [cross]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [Prod.fst_neg]; ring
  · simp only [Prod.fst_neg, Prod.snd_neg]; ring
  · simp only [Prod.snd_neg]; ring

theorem cross_neg_neg' (a b : V3) : cross (-a) (-b) = cross a b := by
  rw [cross_neg_left, cross_neg_right, neg_neg]

/-- 外積が消えると全微分は単射でない。 -/
theorem cross_ne_of_injective {L : ℝ × ℝ →L[ℝ] V3} (h : Function.Injective L) :
    cross (L (1, 0)) (L (0, 1)) ≠ wp := by
  intro hc
  set a := L (1, 0) with ha
  set b := L (0, 1) with hb
  have ha0 : a ≠ wp := by
    intro h0
    have : ((1 : ℝ), (0 : ℝ)) = 0 := h (by rw [map_zero, ← ha]; exact h0)
    have h1 : (1 : ℝ) = 0 := congrArg Prod.fst this
    exact one_ne_zero h1
  have hc' : cross b a = wp := by
    rw [cross_anti', hc]
    simp [wp]
  have e := smul_of_cross_eq hc'
  have hdd := dot_self_ne ha0
  have hξ : L (-dot b a, dot a a) = 0 := by
    have e1 : ((-dot b a, dot a a) : ℝ × ℝ) =
        (-dot b a) • ((1 : ℝ), (0 : ℝ)) + dot a a • ((0 : ℝ), (1 : ℝ)) := by
      simp
    rw [e1, map_add, map_smul, map_smul, ← ha, ← hb, e]
    simp
  have h0 : ((-dot b a, dot a a) : ℝ × ℝ) = 0 := h (by rw [hξ, map_zero])
  exact hdd (congrArg Prod.snd h0)

section Family

variable {κ₀ ε : ℝ} {f : ℝ → ℝ × ℝ → V3}

theorem hasFDerivAt_section (hf : IsPlaneEversion κ₀ ε f) (s : ℝ) (y : ℝ × ℝ) :
    HasFDerivAt (f s)
      ((fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2) (s, y)).comp
        (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ))) y := by
  have hF : HasFDerivAt (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2)
      (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2) (s, y)) (s, y) :=
    (hf.smooth.differentiable (by simp) (s, y)).hasFDerivAt
  have hl : HasFDerivAt (fun z : ℝ × ℝ => ((s, z) : ℝ × (ℝ × ℝ)))
      (ContinuousLinearMap.inr ℝ ℝ (ℝ × ℝ)) y := hasFDerivAt_prodMk_right s y
  exact HasFDerivAt.comp (g := fun p : ℝ × (ℝ × ℝ) => f p.1 p.2) y hF hl

theorem continuous_fderiv_section (hf : IsPlaneEversion κ₀ ε f) (e : ℝ × ℝ) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (f p.1) p.2 e) := by
  have hF : Continuous (fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2)) :=
    hf.smooth.continuous_fderiv (by simp)
  have h : (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (f p.1) p.2 e) =
      fun p => fderiv ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2) p ((0 : ℝ), e) := by
    funext p
    obtain ⟨s, y⟩ := p
    have := (hasFDerivAt_section hf s y).fderiv
    simp only
    rw [this]
    simp
  rw [h]
  exact hF.clm_apply continuous_const

theorem continuous_XF (hf : IsPlaneEversion κ₀ ε f) :
    Continuous (fun p : ℝ × (ℝ × ℝ) => XF f p.1 p.2) :=
  continuous_cross.comp
    ((continuous_fderiv_section hf (1, 0)).prodMk (continuous_fderiv_section hf (0, 1)))

theorem XF_ne (hf : IsPlaneEversion κ₀ ε f) (s : ℝ) (y : ℝ × ℝ) : XF f s y ≠ wp :=
  cross_ne_of_injective (hf.immersion s y)

theorem f_start (hf : IsPlaneEversion κ₀ ε f) {s : ℝ} (hs : s ≤ 0) : f s = planeG := by
  funext y
  rw [hf.fixed s y (Or.inl hs), bsP_of_le (by linarith)]

theorem f_finish (hf : IsPlaneEversion κ₀ ε f) {s : ℝ} (hs : 1 ≤ s) : f s = -planeG := by
  funext y
  rw [hf.fixed s y (Or.inr (Or.inl hs)), bsP_of_ge (by linarith)]
  rfl

theorem XF_start (hf : IsPlaneEversion κ₀ ε f) {s : ℝ} (hs : s ≤ 0) (y : ℝ × ℝ) :
    XF f s y = hC (tau y) • n0 y := by
  simp only [XF, f_start hf hs, fderiv_planeG, planeD_e1, planeD_e2, cross_D1_D2]

theorem XF_finish (hf : IsPlaneEversion κ₀ ε f) {s : ℝ} (hs : 1 ≤ s) (y : ℝ × ℝ) :
    XF f s y = hC (tau y) • n0 y := by
  have hd : DifferentiableAt ℝ planeG y := contDiff_planeG.differentiable (by simp) y
  have e : fderiv ℝ (-planeG) y = -fderiv ℝ planeG y := fderiv_neg
  simp only [XF, f_finish hf hs, e, neg_apply, cross_neg_neg', fderiv_planeG,
    planeD_e1, planeD_e2, cross_D1_D2]

/-- **C3 の帰結の証明**。 -/
theorem family_facts (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1) (hf : IsPlaneEversion κ₀ ε f) :
    FamilyFacts κ₀ ε f where
  start := fun s hs => f_start hf hs
  finish := fun s hs => f_finish hf hs
  horn := fun s y hy => hf.fixed s y (Or.inr (Or.inr hy))
  ball := fun y => by
    have h2 := nsq_le_of_dist (hf.close (1 / 2) y)
    have e : bsP κ₀ (1 / 2) y = κ₀ • Lam (π / 2) (planeG y) := by
      simp only [bsP, kapS, phiS, sig_half, Kf_half]
      congr 2
      ring
    rw [e, nsq_smul] at h2
    have h3 := nsq_Lam_le (π / 2) (planeG y)
    have h4 := nsq_planeG_le_half y
    have h5 : κ₀ ^ 2 * nsq (Lam (π / 2) (planeG y)) ≤ κ₀ ^ 2 * (1 / 2) :=
      mul_le_mul_of_nonneg_left (h3.trans h4) (sq_nonneg _)
    linarith
  decay := fun s y hy => by
    rw [hf.fixed s y (Or.inr (Or.inr hy))]
    simp only [bsP]
    rw [nsq_smul]
    have hk1 := kapS_le h1 s
    have hk0 := kapS_pos h0 h1 s
    have hk2 : kapS κ₀ s ^ 2 ≤ 1 := by nlinarith
    have h3 := nsq_Lam_le (phiS s) (planeG y)
    have h4 := nsq_planeG_le (y := y) (by linarith)
    have h5 := nsq_nonneg (Lam (phiS s) (planeG y))
    nlinarith
  normal_cont := continuous_XF hf
  normal_ne := XF_ne hf
  normal_field :=
    { cont := continuous_XF hf
      ne := fun p => XF_ne hf p.1 p.2
      perp := fun p ξ => by
        have e : ξ = ξ.1 • ((1 : ℝ), (0 : ℝ)) + ξ.2 • ((0 : ℝ), (1 : ℝ)) := by
          ext <;> simp
        rw [e, map_add, map_smul, map_smul]
        simp only [XF, dot, cross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul]
        ring }
  frame_law := fun s₁ s₂ y hs₁ hs₂ => by
    simp only [Everse]
    rw [XF_start hf hs₁, XF_finish hf hs₂, f_finish hf hs₂, f_start hf hs₁]
    rfl
  reversal := fun n hn s₁ s₂ y₁ y₂ hs₁ hs₂ hy₁ hy₂ => by
    obtain ⟨c, -, hsm, hs⟩ := rigid_normal (α := ℝ × (ℝ × ℝ)) (continuous_XF hf)
      (fun p => XF_ne hf p.1 p.2) hn.cont hn.ne (S := univ) dense_univ (fun p _ => by
        simp only [XF]
        exact cross_of_perp (hn.perp p _) (hn.perp p _))
    have hh := (side_mul_of_rigid (α := ℝ × (ℝ × ℝ)) (n := n) (N₀ := fun p => XF f p.1 p.2)
      (c := c) hsm hs (q₁ := f s₁ y₁) (q₂ := f s₂ y₂) (p₁ := (s₁, y₁)) (p₂ := (s₂, y₂))).1
    refine hh (mul_neg_of_pos_of_neg ?_ ?_)
    · simp only [XF_start hf hs₁, f_start hf hs₁]
      exact side_planeG_pos hy₁
    · simp only [XF_finish hf hs₂, f_finish hf hs₂, Pi.neg_apply, side_neg_pos]
      have := side_planeG_pos hy₂
      linarith

end Family

/-! ### 複素数の式 -/

/-- 𝔾(z, v) = (Re z, |z|² z eⁱᵛ)/(1 + |z|⁴)。実軸で G に一致する。 -/
def GG (z : ℂ) (v : ℝ) : V3 :=
  (z.re / (1 + Complex.normSq z ^ 2),
   Complex.normSq z * (z.re * cos v - z.im * sin v) / (1 + Complex.normSq z ^ 2),
   Complex.normSq z * (z.re * sin v + z.im * cos v) / (1 + Complex.normSq z ^ 2))

theorem GG_real (w v : ℝ) : GG (w : ℂ) v = G w v := by
  have e : Complex.normSq (w : ℂ) = w * w := Complex.normSq_ofReal w
  simp only [GG, G, D, e, Complex.ofReal_re, Complex.ofReal_im]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring_nf

/-- ρ e^{iφ} -/
def zOf (ρ φ : ℝ) : ℂ := ⟨ρ * cos φ, ρ * sin φ⟩

theorem zOf_eq (ρ φ : ℝ) : zOf ρ φ = (ρ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp [zOf, Complex.exp_ofReal_mul_I_re]
  · simp [zOf, Complex.exp_ofReal_mul_I_im]

theorem normSq_zOf (ρ φ : ℝ) : Complex.normSq (zOf ρ φ) = ρ ^ 2 := by
  have h := sin_sq_add_cos_sq φ
  simp only [zOf, Complex.normSq_mk]
  linear_combination ρ ^ 2 * h

theorem GG_polar (ρ φ v : ℝ) : GG (zOf ρ φ) v = Lam φ (G ρ v) := by
  have e : (1 : ℝ) + (ρ ^ 2) ^ 2 = D ρ := by simp only [D]; ring
  have hre : (zOf ρ φ).re = ρ * cos φ := rfl
  have him : (zOf ρ φ).im = ρ * sin φ := rfl
  simp only [GG, normSq_zOf, hre, him, e, Lam, G]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> ring

theorem zOf_smul (r ρ φ : ℝ) : (r : ℂ) * zOf ρ φ = zOf (r * ρ) φ := by
  apply Complex.ext <;> simp [zOf, mul_assoc]

theorem zOf_ne {ρ : ℝ} (hρ : 0 < ρ) (φ : ℝ) : zOf ρ φ ≠ 0 := by
  intro h
  have := normSq_zOf ρ φ
  rw [h, map_zero] at this
  have h2 := pow_pos hρ 2
  linarith

/-! ### 比較の値 -/

theorem nsq_kLam (κ φ ρ v : ℝ) :
    nsq (κ • Lam φ (G ρ v)) = κ ^ 2 * ((cos φ) ^ 2 * ρ ^ 2 + ρ ^ 6) / D ρ ^ 2 := by
  have hD := D_ne ρ
  have h1 := sin_sq_add_cos_sq φ
  have h2 := sin_sq_add_cos_sq v
  have e : nsq (Lam φ (G ρ v)) = ((cos φ) ^ 2 * ρ ^ 2 + ρ ^ 6) / D ρ ^ 2 := by
    simp only [nsq, dot, Lam, G]
    field_simp
    linear_combination (ρ ^ 6 * (sin v) ^ 2 + ρ ^ 6 * (cos v) ^ 2) * h1 + ρ ^ 6 * h2
  rw [nsq_smul, e]
  ring

theorem xhat_kLam {κ ρ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (φ v : ℝ) :
    xhat (κ • Lam φ (G ρ v)) =
      cos φ * ρ * (1 + ρ ^ 4) / (κ * ((cos φ) ^ 2 * ρ ^ 2 + ρ ^ 6)) := by
  have hD := D_ne ρ
  have hden : 0 < (cos φ) ^ 2 * ρ ^ 2 + ρ ^ 6 := by positivity
  simp only [xhat, nsq_kLam]
  simp only [Lam, G, Prod.smul_fst, smul_eq_mul]
  have e : D ρ = 1 + ρ ^ 4 := rfl
  field_simp
  rw [e]

/-- 前後の比較の核：|z|² = W, x² = X ≤ W, 0 < r のとき、分子は正。 -/
theorem order_numerator_pos {r X W : ℝ} (hr0 : 0 < r) (hX : 0 ≤ X) (hXW : X ≤ W) (hW : 0 < W) :
    0 < X * (1 - (r + r ^ 2 + r ^ 3) * W ^ 2) + W ^ 3 * (1 + r + r ^ 2 + r ^ 3 + r ^ 4)
      + r ^ 4 * W ^ 5 := by
  by_cases h : 0 ≤ 1 - (r + r ^ 2 + r ^ 3) * W ^ 2
  · have h1 : 0 ≤ X * (1 - (r + r ^ 2 + r ^ 3) * W ^ 2) := mul_nonneg hX h
    have h2 : 0 < W ^ 3 * (1 + r + r ^ 2 + r ^ 3 + r ^ 4) := by positivity
    have h3 : 0 < r ^ 4 * W ^ 5 := by positivity
    linarith
  · push Not at h
    have h1 : W * (1 - (r + r ^ 2 + r ^ 3) * W ^ 2) ≤ X * (1 - (r + r ^ 2 + r ^ 3) * W ^ 2) :=
      mul_le_mul_of_nonpos_right hXW h.le
    have e : W * (1 - (r + r ^ 2 + r ^ 3) * W ^ 2) + W ^ 3 * (1 + r + r ^ 2 + r ^ 3 + r ^ 4)
        + r ^ 4 * W ^ 5 = W + (1 + r ^ 4) * W ^ 3 + r ^ 4 * W ^ 5 := by ring
    have h2 : 0 < W + (1 + r ^ 4) * W ^ 3 + r ^ 4 * W ^ 5 := by positivity
    linarith

/-- 比較の値の差の符号は cos φ の符号に等しい。 -/
theorem xhat_diff {κ ρ r : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hr0 : 0 < r) (hr1 : r < 1)
    (φ v₁ v₂ : ℝ) :
    ∃ m : ℝ, 0 < m ∧ xhat (κ • Lam φ (G (r * ρ) v₁)) - xhat (κ • Lam φ (G ρ v₂)) = cos φ * m := by
  have hc1 : (cos φ) ^ 2 ≤ 1 := by nlinarith [sin_sq_add_cos_sq φ, sq_nonneg (sin φ)]
  set c := cos φ with hc
  set W := ρ ^ 2 with hW
  set X := c ^ 2 * ρ ^ 2 with hX
  have hWp : 0 < W := by positivity
  have hX0 : 0 ≤ X := by positivity
  have hXW : X ≤ W := by
    rw [hX, hW]
    nlinarith [pow_pos hρ 2]
  have hQ := order_numerator_pos hr0 hX0 hXW hWp
  set Q := X * (1 - (r + r ^ 2 + r ^ 3) * W ^ 2) + W ^ 3 * (1 + r + r ^ 2 + r ^ 3 + r ^ 4)
      + r ^ 4 * W ^ 5 with hQdef
  have hd1 : 0 < c ^ 2 * ρ ^ 2 + ρ ^ 6 := by positivity
  have hd2 : 0 < c ^ 2 * ρ ^ 2 + r ^ 4 * ρ ^ 6 := by positivity
  refine ⟨ρ * (1 - r) * Q / (κ * r * (c ^ 2 * ρ ^ 2 + r ^ 4 * ρ ^ 6) * (c ^ 2 * ρ ^ 2 + ρ ^ 6)),
    ?_, ?_⟩
  · have : 0 < 1 - r := by linarith
    positivity
  · rw [xhat_kLam hκ (mul_pos hr0 hρ), xhat_kLam hκ hρ, ← hc]
    have e1 : c ^ 2 * (r * ρ) ^ 2 + (r * ρ) ^ 6 = r ^ 2 * (c ^ 2 * ρ ^ 2 + r ^ 4 * ρ ^ 6) := by ring
    rw [e1, hQdef, hX, hW]
    field_simp
    ring

/-! ### 走者 -/

theorem bb_lt {p p' : ℝ} (h0 : 0 < p) (hlt : p < p') (h1 : p' ≤ 1) : bb p < bb p' := by
  have hp' : 0 < p' := h0.trans hlt
  have hm : 0 < p * p' := mul_pos h0 hp'
  have hm1 : p * p' ≤ 1 := by nlinarith
  have hm3 : (p * p') ^ 3 ≤ p * p' := by
    have : (p * p') ^ 2 ≤ 1 := pow_le_one₀ hm.le hm1
    nlinarith
  have key : 0 < p' ^ 2 + p' * p + p ^ 2 - p ^ 3 * p' ^ 3 := by
    have e : p ^ 3 * p' ^ 3 = (p * p') ^ 3 := by ring
    rw [e]
    nlinarith [pow_pos h0 2, pow_pos hp' 2]
  simp only [bb]
  rw [div_lt_div_iff₀ (D_pos p) (D_pos p')]
  simp only [D]
  have e : p' ^ 3 * (1 + p ^ 4) - p ^ 3 * (1 + p' ^ 4) =
      (p' - p) * (p' ^ 2 + p' * p + p ^ 2 - p ^ 3 * p' ^ 3) := by ring
  have := mul_pos (sub_pos.mpr hlt) key
  linarith

/-- ζ 成分の大きさ。 -/
def zetaSq (q : V3) : ℝ := q.2.1 ^ 2 + q.2.2 ^ 2

theorem zetaSq_kLam (κ φ ρ v : ℝ) : zetaSq (κ • Lam φ (G ρ v)) = κ ^ 2 * bb ρ ^ 2 := by
  have h1 := sin_sq_add_cos_sq φ
  have h2 := sin_sq_add_cos_sq v
  rw [G_eq_aa_bb]
  simp only [zetaSq, Lam, Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
  linear_combination κ ^ 2 * bb ρ ^ 2 * ((sin v) ^ 2 + (cos v) ^ 2) * h1 + κ ^ 2 * bb ρ ^ 2 * h2

namespace Race

variable (R : Race) (η : ℝ)

/-- 面の時刻 s(t)：g = η で 0、g = −η で 1。 -/
def sT (t : ℝ) : ℝ := 1 / 2 - R.g t / (2 * η)

/-- 半径の助変数 ρ(t) -/
def rhoT (t : ℝ) : ℝ := rho η (R.g t)

/-- アキレスの捻転の角度 -/
def thT (t : ℝ) : ℝ := thetaSm R.r η (R.g t)

/-- 亀の平面の座標：y = (1/(rρ), 0) -/
def yTt (t : ℝ) : ℝ × ℝ := (1 / (R.r * R.rhoT η t), 0)

/-- アキレスの平面の座標：y = e^{iθ}/ρ -/
def yAt (t : ℝ) : ℝ × ℝ := (cos (R.thT η t) / R.rhoT η t, sin (R.thT η t) / R.rhoT η t)

/-- 複素数の助変数 z(t) = ρ e^{iφ} -/
def zT (t : ℝ) : ℂ := zOf (R.rhoT η t) (phiS (R.sT η t))

end Race

/-! ### 定理 C2 -/

/-- **定理 C2**：動く面の上の走者の結論の連言。 -/
structure FlexPassage (R : Race) (η κ₀ : ℝ) (f : ℝ → ℝ × ℝ → V3) (s : ℝ → ℝ)
    (yT yA : ℝ → ℝ × ℝ) (θ : ℝ → ℝ) (z : ℝ → ℂ) : Prop where
  /-- 導線は滑らかである。 -/
  smooth_T : ContDiff ℝ ∞ (fun t => f (s t) (yT t))
  smooth_A : ContDiff ℝ ∞ (fun t => f (s t) (yA t))
  /-- 窓の外では面は g、−g で、走者は理想形と同じ点を通る。 -/
  window_start : ∀ t, η ≤ R.g t → s t ≤ 0
  window_end : ∀ t, R.g t ≤ -η → 1 ≤ s t
  on_horn : ∀ t ∈ Icc 0 (2 * R.tstar), 1 ≤ tau (yT t) ∧ 1 ≤ tau (yA t)
  agree_T : ∀ t ∈ Icc 0 (2 * R.tstar), η ≤ |R.g t| → f (s t) (yT t) = R.idealT t
  agree_A : ∀ t ∈ Icc 0 (2 * R.tstar), η ≤ |R.g t| → f (s t) (yA t) = R.idealA t
  /-- ゼノンの段階。 -/
  step_before : ∀ k : ℕ, η ≤ R.r ^ (k + 1) →
    f (s (R.tn (k + 1))) (yA (R.tn (k + 1))) = f (s (R.tn k)) (yT (R.tn k))
  step_after : ∀ k : ℕ, η ≤ R.r ^ (k + 1) →
    f (s (R.tn' k)) (yT (R.tn' k)) = f (s (R.tn' (k + 1))) (yA (R.tn' (k + 1)))
  /-- 複素迂回：走者は 𝔾 の上にある。z は 0 を避け、閉じた上半平面にある。 -/
  complex_T : ∀ t ∈ Icc 0 (2 * R.tstar),
    f (s t) (yT t) = kapS κ₀ (s t) • GG ((R.r : ℂ) * z t) 0
  complex_A : ∀ t ∈ Icc 0 (2 * R.tstar), f (s t) (yA t) = kapS κ₀ (s t) • GG (z t) (θ t)
  z_real : ∀ t, η ≤ |R.g t| → z t = (R.g t : ℂ)
  z_ne : ∀ t, z t ≠ 0
  z_diff_ne : ∀ t, z t - (R.r : ℂ) * z t ≠ 0
  z_im_nonneg : ∀ t, 0 ≤ (z t).im
  z_im_star : 0 < (z R.tstar).im
  z_re_before : ∀ t, t < R.tstar → 0 < (z t).re
  z_re_after : ∀ t, R.tstar < t → (z t).re < 0
  z_re_star : (z R.tstar).re = 0
  /-- 非衝突。 -/
  no_collision : ∀ t ∈ Icc 0 (2 * R.tstar), f (s t) (yT t) ≠ f (s t) (yA t)
  min_dist : ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar), d ≤ nsq (f (s t) (yT t) - f (s t) (yA t))
  /-- 前後：比較の値は符号を変え、t∗ でだけ一致する。その時刻に二人は同じ点にいない。 -/
  compare_before : ∀ t ∈ Icc 0 (2 * R.tstar), t < R.tstar →
    xhat (f (s t) (yA t)) < xhat (f (s t) (yT t))
  compare_after : ∀ t ∈ Icc 0 (2 * R.tstar), R.tstar < t →
    xhat (f (s t) (yT t)) < xhat (f (s t) (yA t))
  compare_star : xhat (f (s R.tstar) (yT R.tstar)) = xhat (f (s R.tstar) (yA R.tstar)) ∧
    f (s R.tstar) (yT R.tstar) ≠ f (s R.tstar) (yA R.tstar)
  /-- 表裏：亀は +X、アキレスは −X に立つ。 -/
  side_T_start : ∀ t ∈ Icc 0 (2 * R.tstar), η ≤ R.g t →
    Front (f (s t) (yT t)) (XF f (s t) (yT t))
  side_T_end : ∀ t ∈ Icc 0 (2 * R.tstar), R.g t ≤ -η →
    Back (f (s t) (yT t)) (XF f (s t) (yT t))
  side_A_start : ∀ t ∈ Icc 0 (2 * R.tstar), η ≤ R.g t →
    Back (f (s t) (yA t)) (-XF f (s t) (yA t))
  side_A_end : ∀ t ∈ Icc 0 (2 * R.tstar), R.g t ≤ -η →
    Front (f (s t) (yA t)) (-XF f (s t) (yA t))

/-! ### 定理 C2 の証明 -/

section FlexProof

variable (R : Race) {η κ₀ ε : ℝ} {f : ℝ → ℝ × ℝ → V3}

theorem sT_le_zero (hη : 0 < η) {t : ℝ} (h : η ≤ R.g t) : R.sT η t ≤ 0 := by
  simp only [Race.sT]
  have : 1 / 2 ≤ R.g t / (2 * η) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  linarith

theorem one_le_sT (hη : 0 < η) {t : ℝ} (h : R.g t ≤ -η) : 1 ≤ R.sT η t := by
  simp only [Race.sT]
  have : R.g t / (2 * η) ≤ -(1 / 2) := by
    rw [div_le_iff₀ (by positivity)]; linarith
  linarith

theorem sT_lt_half (hη : 0 < η) {t : ℝ} (h : t < R.tstar) : R.sT η t < 1 / 2 := by
  simp only [Race.sT]
  have := div_pos (R.g_pos_of_lt h) (by positivity : 0 < 2 * η)
  linarith

theorem sT_gt_half (hη : 0 < η) {t : ℝ} (h : R.tstar < t) : 1 / 2 < R.sT η t := by
  simp only [Race.sT]
  have := div_neg_of_neg_of_pos (R.g_neg_of_gt h) (by positivity : 0 < 2 * η)
  linarith

theorem sT_star : R.sT η R.tstar = 1 / 2 := by
  simp [Race.sT, R.g_tstar]

theorem cos_phiS_pos {s : ℝ} (h : s < 1 / 2) : 0 < cos (phiS s) := by
  have h1 : sig s < 1 / 2 := s0_lt_half (by linarith)
  have h0 := sig_nonneg s
  have hπ := Real.pi_pos
  apply Real.cos_pos_of_mem_Ioo
  simp only [phiS, mem_Ioo]
  constructor <;> nlinarith

theorem cos_phiS_neg {s : ℝ} (h : 1 / 2 < s) : cos (phiS s) < 0 := by
  have h1 : 1 / 2 < sig s := s0_gt_half (by linarith)
  have h0 := sig_le_one s
  have hπ := Real.pi_pos
  apply Real.cos_neg_of_pi_div_two_lt_of_lt
  · simp only [phiS]; nlinarith
  · simp only [phiS]; nlinarith

theorem phiS_half : phiS (1 / 2) = π / 2 := by
  simp only [phiS, sig_half]; ring

theorem sin_phiS_nonneg (s : ℝ) : 0 ≤ sin (phiS s) := by
  have h0 := sig_nonneg s
  have h1 := sig_le_one s
  have hπ := Real.pi_pos
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · simp only [phiS]; positivity
  · simp only [phiS]; nlinarith

theorem phiS_of_le {s : ℝ} (h : s ≤ 0) : phiS s = 0 := by
  simp [phiS, sig_of_le (by linarith : s ≤ 1 / 4)]

theorem phiS_of_ge {s : ℝ} (h : 1 ≤ s) : phiS s = π := by
  simp [phiS, sig_of_ge (by linarith : 3 / 4 ≤ s)]

theorem kapS_of_le (κ₀ : ℝ) {s : ℝ} (h : s ≤ 0) : kapS κ₀ s = 1 := by
  simp [kapS, sig_of_le (by linarith : s ≤ 1 / 4), Kf_zero]

theorem kapS_of_ge (κ₀ : ℝ) {s : ℝ} (h : 1 ≤ s) : kapS κ₀ s = 1 := by
  simp [kapS, sig_of_ge (by linarith : 3 / 4 ≤ s), Kf_one]

theorem rhoT_pos (hη : 0 < η) (t : ℝ) : 0 < R.rhoT η t := rho_pos hη.ne' _

theorem rhoT_le_one (hη : 0 < η) (hη1 : η < 1) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    R.rhoT η t ≤ 1 := by
  have hle := R.abs_g_le ht.1 ht.2
  have hs : R.g t ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hle
  have h1 : R.rhoT η t ^ 2 ≤ 1 := by
    simp only [Race.rhoT]
    rw [rho_sq hη.ne', ← hh_one hη.ne' (by nlinarith)]
    exact (hh_strictMono hη.ne').monotone hs
  have hp := rhoT_pos R hη t
  nlinarith

theorem rhoT_of (hη : 0 < η) {t : ℝ} (h : η ≤ |R.g t|) : R.rhoT η t = |R.g t| := by
  simp only [Race.rhoT]
  apply rho_of hη.ne'
  have : η ^ 2 ≤ R.g t ^ 2 := by
    rw [← sq_abs (R.g t)]
    exact pow_le_pow_left₀ hη.le h 2
  nlinarith [pow_pos hη 2]

theorem thT_of (hη : 0 < η) {t : ℝ} (h : η ≤ |R.g t|) : R.thT η t = theta R.r (R.g t) := by
  simp only [Race.thT]
  apply thetaSm_of hη.ne'
  have : η ^ 2 ≤ R.g t ^ 2 := by
    rw [← sq_abs (R.g t)]
    exact pow_le_pow_left₀ hη.le h 2
  nlinarith [pow_pos hη 2]

theorem yTt_polar (t : ℝ) :
    R.yTt η t = (cos 0 / (R.r * R.rhoT η t), sin 0 / (R.r * R.rhoT η t)) := by
  simp [Race.yTt]

theorem tau_yT_ge (hη : 0 < η) (hη1 : η < 1) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    1 ≤ tau (R.yTt η t) := by
  have hp := rhoT_pos R hη t
  have hle := rhoT_le_one R hη hη1 ht
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hrp : 0 < R.r * R.rhoT η t := mul_pos hr0 hp
  rw [yTt_polar, tau_polar hrp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul hr1.le hle hp.le zero_le_one]

theorem tau_yA_ge (hη : 0 < η) (hη1 : η < 1) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    1 ≤ tau (R.yAt η t) := by
  have hp := rhoT_pos R hη t
  have hle := rhoT_le_one R hη hη1 ht
  simp only [Race.yAt]
  rw [tau_polar hp]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem planeG_yT (hη : 0 < η) (hη1 : η < 1) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    planeG (R.yTt η t) = G (R.r * R.rhoT η t) 0 := by
  have hp := rhoT_pos R hη t
  have hle := rhoT_le_one R hη hη1 ht
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hrp : 0 < R.r * R.rhoT η t := mul_pos hr0 hp
  have hle2 : R.r * R.rhoT η t ≤ 1 := by nlinarith
  rw [yTt_polar, planeG_polar hrp (by nlinarith)]

theorem planeG_yA (hη : 0 < η) (hη1 : η < 1) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    planeG (R.yAt η t) = G (R.rhoT η t) (R.thT η t) := by
  have hp := rhoT_pos R hη t
  have hle := rhoT_le_one R hη hη1 ht
  simp only [Race.yAt]
  rw [planeG_polar hp (by nlinarith)]

theorem flexT_eq (hη : 0 < η) (hη1 : η < 1) (hf : IsPlaneEversion κ₀ ε f) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar)) :
    f (R.sT η t) (R.yTt η t) =
      kapS κ₀ (R.sT η t) • Lam (phiS (R.sT η t)) (G (R.r * R.rhoT η t) 0) := by
  rw [hf.fixed _ _ (Or.inr (Or.inr (tau_yT_ge R hη hη1 ht)))]
  simp only [bsP, planeG_yT R hη hη1 ht]

theorem flexA_eq (hη : 0 < η) (hη1 : η < 1) (hf : IsPlaneEversion κ₀ ε f) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar)) :
    f (R.sT η t) (R.yAt η t) =
      kapS κ₀ (R.sT η t) • Lam (phiS (R.sT η t)) (G (R.rhoT η t) (R.thT η t)) := by
  rw [hf.fixed _ _ (Or.inr (Or.inr (tau_yA_ge R hη hη1 ht)))]
  simp only [bsP, planeG_yA R hη hη1 ht]

theorem flex_agree_T (hη : 0 < η) (hη1 : η < 1) (hf : IsPlaneEversion κ₀ ε f) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar)) (h : η ≤ |R.g t|) :
    f (R.sT η t) (R.yTt η t) = R.idealT t := by
  rw [flexT_eq R hη hη1 hf ht, rhoT_of R hη h]
  simp only [Race.idealT]
  rcases le_abs.mp h with h1 | h1
  · have hs := sT_le_zero R hη h1
    have hg : 0 < R.g t := by linarith
    rw [phiS_of_le hs, kapS_of_le κ₀ hs, Lam_zero, one_smul, abs_of_pos hg]
  · have hg' : R.g t ≤ -η := by linarith
    have hs := one_le_sT R hη hg'
    have hg : R.g t < 0 := by linarith
    rw [phiS_of_ge hs, kapS_of_ge κ₀ hs, Lam_pi, one_smul, abs_of_neg hg, ← G_odd]
    congr 1
    ring

theorem flex_agree_A (hη : 0 < η) (hη1 : η < 1) (hf : IsPlaneEversion κ₀ ε f) {t : ℝ}
    (ht : t ∈ Icc 0 (2 * R.tstar)) (h : η ≤ |R.g t|) :
    f (R.sT η t) (R.yAt η t) = R.idealA t := by
  rw [flexA_eq R hη hη1 hf ht, rhoT_of R hη h, thT_of R hη h]
  simp only [Race.idealA]
  rcases le_abs.mp h with h1 | h1
  · have hs := sT_le_zero R hη h1
    have hg : 0 < R.g t := by linarith
    rw [phiS_of_le hs, kapS_of_le κ₀ hs, Lam_zero, one_smul, abs_of_pos hg]
  · have hg' : R.g t ≤ -η := by linarith
    have hs := one_le_sT R hη hg'
    have hg : R.g t < 0 := by linarith
    rw [phiS_of_ge hs, kapS_of_ge κ₀ hs, Lam_pi, one_smul, abs_of_neg hg, ← G_odd, neg_neg]

theorem bb_pos {p : ℝ} (h : 0 < p) : 0 < bb p := by
  rw [bb_eq]
  exact mul_pos (pow_pos h 2) (aa_pos h)

theorem flex_no_collision (hη : 0 < η) (hη1 : η < 1) (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1)
    (hf : IsPlaneEversion κ₀ ε f) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    f (R.sT η t) (R.yTt η t) ≠ f (R.sT η t) (R.yAt η t) := by
  intro he
  rw [flexT_eq R hη hη1 hf ht, flexA_eq R hη hη1 hf ht] at he
  have h2 := congrArg zetaSq he
  rw [zetaSq_kLam, zetaSq_kLam] at h2
  have hp := rhoT_pos R hη t
  have hle := rhoT_le_one R hη hη1 ht
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hrp : 0 < R.r * R.rhoT η t := mul_pos hr0 hp
  have hb := bb_lt hrp (by nlinarith) hle
  have hb0 := bb_pos hrp
  have hk := kapS_pos h0 h1 (R.sT η t)
  have hsq : bb (R.r * R.rhoT η t) ^ 2 < bb (R.rhoT η t) ^ 2 :=
    pow_lt_pow_left₀ hb hb0.le (by norm_num)
  have hk2 : 0 < kapS κ₀ (R.sT η t) ^ 2 := by positivity
  nlinarith

theorem contDiff_sT : ContDiff ℝ ∞ (R.sT η) := by
  unfold Race.sT
  exact contDiff_const.sub (R.contDiff_g.div_const _)

theorem contDiff_rhoT (hη : 0 < η) : ContDiff ℝ ∞ (R.rhoT η) := by
  unfold Race.rhoT
  exact (contDiff_rho hη.ne').comp R.contDiff_g

theorem contDiff_yT (hη : 0 < η) : ContDiff ℝ ∞ (R.yTt η) := by
  have h1 : ContDiff ℝ ∞ (fun t => 1 / (R.r * R.rhoT η t)) :=
    contDiff_const.div (contDiff_const.mul (contDiff_rhoT R hη))
      fun t => (mul_pos R.r_pos (rhoT_pos R hη t)).ne'
  exact h1.prodMk contDiff_const

theorem contDiff_yA (hη : 0 < η) : ContDiff ℝ ∞ (R.yAt η) := by
  have h0 : ContDiff ℝ ∞ (R.thT η) := by
    unfold Race.thT
    exact (contDiff_thetaSm R.r hη.ne').comp R.contDiff_g
  have h1 : ContDiff ℝ ∞ (fun t => cos (R.thT η t) / R.rhoT η t) :=
    (Real.contDiff_cos.comp h0).div (contDiff_rhoT R hη) fun t => (rhoT_pos R hη t).ne'
  have h2 : ContDiff ℝ ∞ (fun t => sin (R.thT η t) / R.rhoT η t) :=
    (Real.contDiff_sin.comp h0).div (contDiff_rhoT R hη) fun t => (rhoT_pos R hη t).ne'
  exact h1.prodMk h2

theorem flex_smooth_T (hη : 0 < η) (hf : IsPlaneEversion κ₀ ε f) :
    ContDiff ℝ ∞ (fun t => f (R.sT η t) (R.yTt η t)) := by
  have hp : ContDiff ℝ ∞ (fun t => ((R.sT η t, R.yTt η t) : ℝ × (ℝ × ℝ))) :=
    (contDiff_sT R).prodMk (contDiff_yT R hη)
  have h2 := hf.smooth.comp hp
  exact h2

theorem flex_smooth_A (hη : 0 < η) (hf : IsPlaneEversion κ₀ ε f) :
    ContDiff ℝ ∞ (fun t => f (R.sT η t) (R.yAt η t)) := by
  have hp : ContDiff ℝ ∞ (fun t => ((R.sT η t, R.yAt η t) : ℝ × (ℝ × ℝ))) :=
    (contDiff_sT R).prodMk (contDiff_yA R hη)
  have h2 := hf.smooth.comp hp
  exact h2

theorem flex_min (hη : 0 < η) (hη1 : η < 1) (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1)
    (hf : IsPlaneEversion κ₀ ε f) :
    ∃ d > 0, ∀ t ∈ Icc 0 (2 * R.tstar),
      d ≤ nsq (f (R.sT η t) (R.yTt η t) - f (R.sT η t) (R.yAt η t)) := by
  have hT := (flex_smooth_T R hη hf).continuous
  have hA := (flex_smooth_A R hη hf).continuous
  have hcont : Continuous fun t =>
      nsq (f (R.sT η t) (R.yTt η t) - f (R.sT η t) (R.yAt η t)) := by
    unfold nsq
    exact continuous_dot.comp ((hT.sub hA).prodMk (hT.sub hA))
  have hne' : (Icc 0 (2 * R.tstar)).Nonempty := ⟨0, le_rfl, by have := R.tstar_pos; positivity⟩
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne' hcont.continuousOn
  exact ⟨_, nsq_pos_of_ne (sub_ne_zero.mpr (flex_no_collision R hη hη1 h0 h1 hf ht₀)),
    fun t ht => hmin ht⟩

theorem flex_compare (hη : 0 < η) (hη1 : η < 1) (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1)
    (hf : IsPlaneEversion κ₀ ε f) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    ∃ m : ℝ, 0 < m ∧ xhat (f (R.sT η t) (R.yTt η t)) - xhat (f (R.sT η t) (R.yAt η t)) =
      cos (phiS (R.sT η t)) * m := by
  rw [flexT_eq R hη hη1 hf ht, flexA_eq R hη hη1 hf ht]
  exact xhat_diff (kapS_pos h0 h1 _) (rhoT_pos R hη t) R.r_pos R.r_lt_one _ _ _

/-- **定理 C2**。 -/
theorem flex_passage (hη : 0 < η) (hη1 : η < 1) (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1)
    (hf : IsPlaneEversion κ₀ ε f) :
    FlexPassage R η κ₀ f (R.sT η) (R.yTt η) (R.yAt η) (R.thT η) (R.zT η) where
  smooth_T := flex_smooth_T R hη hf
  smooth_A := flex_smooth_A R hη hf
  window_start := fun t h => sT_le_zero R hη h
  window_end := fun t h => one_le_sT R hη h
  on_horn := fun t ht => ⟨tau_yT_ge R hη hη1 ht, tau_yA_ge R hη hη1 ht⟩
  agree_T := fun t ht h => flex_agree_T R hη hη1 hf ht h
  agree_A := fun t ht h => flex_agree_A R hη hη1 hf ht h
  step_before := fun k hk => by
    have hr0 := R.r_pos
    have hr1 := R.r_lt_one
    have hts := R.tstar_pos
    have hp0 : ∀ n : ℕ, 0 < R.r ^ n := fun n => pow_pos hr0 n
    have hp1 : ∀ n : ℕ, R.r ^ n ≤ 1 := fun n => pow_le_one₀ hr0.le hr1.le
    have hm : ∀ n : ℕ, R.tn n ∈ Icc 0 (2 * R.tstar) := fun n => by
      have h3 := hp0 n
      have h4 := hp1 n
      simp only [Race.tn, mem_Icc]
      constructor <;> nlinarith
    have hg1 : η ≤ |R.g (R.tn (k + 1))| := by
      rw [R.g_tn, abs_of_pos (hp0 _)]; exact hk
    have hg2 : η ≤ |R.g (R.tn k)| := by
      rw [R.g_tn, abs_of_pos (hp0 _)]
      refine hk.trans ?_
      rw [pow_succ]
      nlinarith [hp0 k]
    rw [flex_agree_A R hη hη1 hf (hm _) hg1, flex_agree_T R hη hη1 hf (hm _) hg2]
    exact ((ideal_passage R).meet_before k).2
  step_after := fun k hk => by
    have hr0 := R.r_pos
    have hr1 := R.r_lt_one
    have hts := R.tstar_pos
    have hp0 : ∀ n : ℕ, 0 < R.r ^ n := fun n => pow_pos hr0 n
    have hp1 : ∀ n : ℕ, R.r ^ n ≤ 1 := fun n => pow_le_one₀ hr0.le hr1.le
    have hm : ∀ n : ℕ, R.tn' n ∈ Icc 0 (2 * R.tstar) := fun n => by
      have h3 := hp0 n
      have h4 := hp1 n
      simp only [Race.tn', mem_Icc]
      constructor <;> nlinarith
    have hg1 : η ≤ |R.g (R.tn' (k + 1))| := by
      rw [R.g_tn', abs_neg, abs_of_pos (hp0 _)]; exact hk
    have hg2 : η ≤ |R.g (R.tn' k)| := by
      rw [R.g_tn', abs_neg, abs_of_pos (hp0 _)]
      refine hk.trans ?_
      rw [pow_succ]
      nlinarith [hp0 k]
    rw [flex_agree_T R hη hη1 hf (hm _) hg2, flex_agree_A R hη hη1 hf (hm _) hg1]
    exact ((ideal_passage R).meet_after k).2
  complex_T := fun t ht => by
    rw [flexT_eq R hη hη1 hf ht]
    simp only [Race.zT]
    rw [zOf_smul, GG_polar]
  complex_A := fun t ht => by
    rw [flexA_eq R hη hη1 hf ht]
    simp only [Race.zT]
    rw [GG_polar]
  z_real := fun t h => by
    simp only [Race.zT, rhoT_of R hη h]
    rcases le_abs.mp h with h1' | h1'
    · have hs := sT_le_zero R hη h1'
      have hg : 0 < R.g t := by linarith
      rw [phiS_of_le hs, abs_of_pos hg]
      apply Complex.ext <;> simp [zOf]
    · have hg' : R.g t ≤ -η := by linarith
      have hs := one_le_sT R hη hg'
      have hg : R.g t < 0 := by linarith
      rw [phiS_of_ge hs, abs_of_neg hg]
      apply Complex.ext <;> simp [zOf]
  z_ne := fun t => zOf_ne (rhoT_pos R hη t) _
  z_diff_ne := fun t => by
    have e : R.zT η t - (R.r : ℂ) * R.zT η t = ((1 - R.r : ℝ) : ℂ) * R.zT η t := by
      push_cast; ring
    rw [e]
    refine mul_ne_zero ?_ (zOf_ne (rhoT_pos R hη t) _)
    have : (1 - R.r) ≠ 0 := by
      have := R.r_lt_one
      linarith
    exact_mod_cast this
  z_im_nonneg := fun t =>
    mul_nonneg (rhoT_pos R hη t).le (sin_phiS_nonneg _)
  z_im_star := by
    have e : (R.zT η R.tstar).im = R.rhoT η R.tstar * sin (phiS (R.sT η R.tstar)) := rfl
    rw [e, sT_star, phiS_half, sin_pi_div_two, mul_one]
    exact rhoT_pos R hη _
  z_re_before := fun t ht =>
    mul_pos (rhoT_pos R hη t) (cos_phiS_pos (sT_lt_half R hη ht))
  z_re_after := fun t ht =>
    mul_neg_of_pos_of_neg (rhoT_pos R hη t) (cos_phiS_neg (sT_gt_half R hη ht))
  z_re_star := by
    have e : (R.zT η R.tstar).re = R.rhoT η R.tstar * cos (phiS (R.sT η R.tstar)) := rfl
    rw [e, sT_star, phiS_half, cos_pi_div_two, mul_zero]
  no_collision := fun t ht => flex_no_collision R hη hη1 h0 h1 hf ht
  min_dist := flex_min R hη hη1 h0 h1 hf
  compare_before := fun t ht h => by
    obtain ⟨m, hm, e⟩ := flex_compare R hη hη1 h0 h1 hf ht
    have := mul_pos (cos_phiS_pos (sT_lt_half R hη h)) hm
    linarith
  compare_after := fun t ht h => by
    obtain ⟨m, hm, e⟩ := flex_compare R hη hη1 h0 h1 hf ht
    have := mul_neg_of_neg_of_pos (cos_phiS_neg (sT_gt_half R hη h)) hm
    linarith
  compare_star := by
    have hts := R.tstar_pos
    have hmem : R.tstar ∈ Icc 0 (2 * R.tstar) := ⟨hts.le, by linarith⟩
    refine ⟨?_, flex_no_collision R hη hη1 h0 h1 hf hmem⟩
    obtain ⟨m, hm, e⟩ := flex_compare R hη hη1 h0 h1 hf hmem
    rw [sT_star, phiS_half, cos_pi_div_two, zero_mul] at e
    rw [sT_star] at *
    linarith
  side_T_start := fun t ht h => by
    have hs := sT_le_zero R hη h
    simp only [Front, XF_start hf hs, f_start hf hs]
    exact side_planeG_pos (tau_yT_ge R hη hη1 ht)
  side_T_end := fun t ht h => by
    have hs := one_le_sT R hη h
    simp only [Back, XF_finish hf hs, f_finish hf hs, Pi.neg_apply, side_neg_pos]
    have := side_planeG_pos (tau_yT_ge R hη hη1 ht)
    linarith
  side_A_start := fun t ht h => by
    have hs := sT_le_zero R hη h
    simp only [Back, XF_start hf hs, f_start hf hs, side_neg]
    have := side_planeG_pos (tau_yA_ge R hη hη1 ht)
    linarith
  side_A_end := fun t ht h => by
    have hs := one_le_sT R hη h
    simp only [Front, XF_finish hf hs, f_finish hf hs, Pi.neg_apply, side_neg_pos, side_neg]
    have := side_planeG_pos (tau_yA_ge R hη hη1 ht)
    linarith

end FlexProof

/-! ### 理想形への収束 -/

theorem nsq_G_le_sq (p v : ℝ) : nsq (G p v) ≤ p ^ 2 := by
  rw [nsq_G]
  have hD := D_pos p
  rw [div_le_iff₀ hD]
  simp only [D]
  nlinarith [sq_nonneg p, pow_nonneg (sq_nonneg p) 2, mul_nonneg (sq_nonneg p) (sq_nonneg (p ^ 2))]

theorem rho_zero_sq {η : ℝ} (hη : 0 < η) : rho η 0 ^ 2 ≤ η ^ 2 := by
  rw [rho_sq hη.ne']
  have e : hh η ((0 : ℝ) ^ 2) = rsq η := by
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this, hh_zero hη.ne']
  rw [e]
  have h1 : rsq η ≤ η ^ 2 / 8 := rsq_le
  nlinarith [pow_pos hη 2]

/-- **C から A へ（亀）**：窓を狭めると、動く面の上の亀は各時刻で理想形の亀に収束する。 -/
theorem flex_tendsto_T (R : Race) {κ₀ ε : ℝ} {f : ℝ → ℝ × ℝ → V3} (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1)
    (hf : IsPlaneEversion κ₀ ε f) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    Tendsto (fun η => f (R.sT η t) (R.yTt η t)) (𝓝[>] 0) (𝓝 (R.idealT t)) := by
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  by_cases hts : t = R.tstar
  · have e : R.idealT t = wp := by
      subst hts
      simp [Race.idealT, R.g_tstar, G_zero]
    rw [e]
    apply tendsto_wp_of_nsq
    have hsq : Tendsto (fun η : ℝ => η ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun η : ℝ => η ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) :=
        (continuous_id.pow 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
    refine squeeze_zero' (Eventually.of_forall fun η => nsq_nonneg _) ?_ hsq
    filter_upwards [hmem] with η hη
    rw [flexT_eq R hη.1 hη.2 hf ht, nsq_smul]
    have hk1 := kapS_le h1 (R.sT η t)
    have hk2 := kapS_pos h0 h1 (R.sT η t)
    have hk : kapS κ₀ (R.sT η t) ^ 2 ≤ 1 := by nlinarith
    have hρ : R.rhoT η t ^ 2 ≤ η ^ 2 := by
      subst hts
      simp only [Race.rhoT, R.g_tstar]
      exact rho_zero_sq hη.1
    have hρp := rhoT_pos R hη.1 t
    have h3 : nsq (Lam (phiS (R.sT η t)) (G (R.r * R.rhoT η t) 0)) ≤ η ^ 2 := by
      refine (nsq_Lam_le _ _).trans ((nsq_G_le_sq _ _).trans ?_)
      have e2 : (R.r * R.rhoT η t) ^ 2 = R.r ^ 2 * R.rhoT η t ^ 2 := by ring
      rw [e2]
      have hr2 : R.r ^ 2 ≤ 1 := by nlinarith
      nlinarith [pow_pos hρp 2]
    have h5 := nsq_nonneg (Lam (phiS (R.sT η t)) (G (R.r * R.rhoT η t) 0))
    nlinarith
  · have hpos : 0 < min 1 |R.g t| := lt_min one_pos (abs_pos.mpr (R.g_ne_zero hts))
    have hmem : Ioo (0 : ℝ) (min 1 |R.g t|) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hpos
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hmem] with η hη
    have h2 := lt_of_lt_of_le hη.2 (min_le_left _ _)
    have h3 := lt_of_lt_of_le hη.2 (min_le_right _ _)
    exact (flex_agree_T R hη.1 h2 hf ht h3.le).symm

/-- **C から A へ（アキレス）**。 -/
theorem flex_tendsto_A (R : Race) {κ₀ ε : ℝ} {f : ℝ → ℝ × ℝ → V3} (h0 : 0 < κ₀) (h1 : κ₀ ≤ 1)
    (hf : IsPlaneEversion κ₀ ε f) {t : ℝ} (ht : t ∈ Icc 0 (2 * R.tstar)) :
    Tendsto (fun η => f (R.sT η t) (R.yAt η t)) (𝓝[>] 0) (𝓝 (R.idealA t)) := by
  by_cases hts : t = R.tstar
  · have e : R.idealA t = wp := by
      subst hts
      simp [Race.idealA, R.g_tstar, G_zero]
    rw [e]
    apply tendsto_wp_of_nsq
    have hsq : Tendsto (fun η : ℝ => η ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun η : ℝ => η ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) :=
        (continuous_id.pow 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
    refine squeeze_zero' (Eventually.of_forall fun η => nsq_nonneg _) ?_ hsq
    filter_upwards [hmem] with η hη
    rw [flexA_eq R hη.1 hη.2 hf ht, nsq_smul]
    have hk1 := kapS_le h1 (R.sT η t)
    have hk2 := kapS_pos h0 h1 (R.sT η t)
    have hk : kapS κ₀ (R.sT η t) ^ 2 ≤ 1 := by nlinarith
    have hρ : R.rhoT η t ^ 2 ≤ η ^ 2 := by
      subst hts
      simp only [Race.rhoT, R.g_tstar]
      exact rho_zero_sq hη.1
    have h3 : nsq (Lam (phiS (R.sT η t)) (G (R.rhoT η t) (R.thT η t))) ≤ η ^ 2 :=
      (nsq_Lam_le _ _).trans ((nsq_G_le_sq _ _).trans hρ)
    have h5 := nsq_nonneg (Lam (phiS (R.sT η t)) (G (R.rhoT η t) (R.thT η t)))
    nlinarith
  · have hpos : 0 < min 1 |R.g t| := lt_min one_pos (abs_pos.mpr (R.g_ne_zero hts))
    have hmem : Ioo (0 : ℝ) (min 1 |R.g t|) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hpos
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hmem] with η hη
    have h2 := lt_of_lt_of_le hη.2 (min_le_left _ _)
    have h3 := lt_of_lt_of_le hη.2 (min_le_right _ _)
    exact (flex_agree_A R hη.1 h2 hf ht h3.le).symm

end Zeno.Model
