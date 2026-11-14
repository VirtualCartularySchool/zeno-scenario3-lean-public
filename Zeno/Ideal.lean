/-
# Zeno.Ideal : 定理 A（理想形）

競走の追いつき点 P を射影変換で理想点へ送り、枠つき平面 (G, N) の上に走者を置く。
亀は直線 v = 0、アキレスはきりもみ v = θ(w)（原資料 L62）。無限捻転はそのまま扱う。
t∗ で両者は ℘ に一致する。この一致を隠さない。定理 B、C がこれを取り除く。
-/
import Zeno.Horn
import Zeno.Side

noncomputable section

namespace Zeno.Model

open Real Set Filter Topology OnePoint

/-! ### ホーンと比較の座標 -/

/-- 符号つきのホーン H(X, v) = (X, eⁱᵛ/X)。X > 0 が右、X < 0 が左。 -/
def H (X v : ℝ) : V3 := (X, cos v / X, sin v / X)

/-- 反転チャートの像は、助変数 w = 1/X で G である。 -/
theorem inv3_G_eq_H {w : ℝ} (hw : w ≠ 0) (v : ℝ) : inv3 (G w v) = H (1 / w) v := by
  rw [inv3_G hw]
  simp only [H]
  field_simp

/-- ホーンの軸の座標 x̂(q) = q₁/|q|²。反転チャートの第 1 成分である。 -/
def xhat (q : V3) : ℝ := q.1 / nsq q

theorem xhat_G {w : ℝ} (hw : w ≠ 0) (v : ℝ) : xhat (G w v) = 1 / w := by
  have h := inv3_G hw v
  exact congrArg Prod.fst h

/-- |G|² = w²/D は |w| ≤ 1 で |w| について狭義単調。 -/
theorem nsq_G_lt {w₁ w₂ : ℝ} (h : |w₁| < |w₂|) (h1 : |w₂| ≤ 1) (v₁ v₂ : ℝ) :
    nsq (G w₁ v₁) < nsq (G w₂ v₂) := by
  rw [nsq_G, nsq_G]
  have hD1 := D_pos w₁
  have hD2 := D_pos w₂
  rw [div_lt_div_iff₀ hD1 hD2]
  have hu : w₁ ^ 2 < w₂ ^ 2 := by
    rw [← sq_abs w₁, ← sq_abs w₂]
    exact pow_lt_pow_left₀ h (abs_nonneg _) (by norm_num)
  have hu2 : w₂ ^ 2 ≤ 1 := by
    rw [← sq_abs w₂]
    exact pow_le_one₀ (abs_nonneg _) h1
  have hu0 : 0 ≤ w₁ ^ 2 := sq_nonneg _
  simp only [D]
  nlinarith [mul_nonneg hu0 (sub_nonneg.2 hu2), mul_pos (sub_pos.2 hu) (sub_pos.2 (lt_of_lt_of_le hu hu2))]

/-! ### 形成写像 -/

namespace Race

variable (R : Race)

/-- 追いつき点 P = vₐ t∗。 -/
def P : ℝ := R.va * R.tstar

/-- 形成写像 w(x) = (P − x)/P。直線の一次関数である。 -/
def wmap (x : ℝ) : ℝ := (R.P - x) / R.P

/-- 形成写像 X(x) = P/(P − x)。直線の射影変換で、P を ∞ へ送る。 -/
def Xmap (x : ℝ) : OnePoint ℝ := invOP (R.wmap x)

theorem P_pos : 0 < R.P := mul_pos R.va_pos R.tstar_pos

theorem T_tstar : R.T R.tstar = R.P := by
  have h := R.gap_pos.ne'
  simp only [T, P, tstar]
  field_simp
  ring

theorem wmap_A (t : ℝ) : R.wmap (R.A t) = R.g t := by
  have h := R.P_pos.ne'
  have h2 := R.tstar_pos.ne'
  have h3 := R.va_pos.ne'
  rw [R.g_eq]
  simp only [wmap, A, P]
  field_simp

theorem wmap_T (t : ℝ) : R.wmap (R.T t) = R.r * R.g t := by
  have hP := R.T_tstar
  have h := R.P_pos.ne'
  have h2 := R.tstar_pos.ne'
  have h3 := R.va_pos.ne'
  have e : R.P - R.T t = R.vt * (R.tstar - t) := by
    rw [← hP]; simp only [T]; ring
  rw [R.g_eq]
  simp only [wmap]
  rw [e]
  simp only [P, r]
  field_simp

theorem wmap_P : R.wmap R.P = 0 := by
  simp [wmap]

/-- ゼノンの段階 P(1 − rᵏ) は w = rᵏ へ移る。 -/
theorem wmap_step (k : ℕ) : R.wmap (R.P * (1 - R.r ^ k)) = R.r ^ k := by
  have h := R.P_pos.ne'
  simp only [wmap]
  field_simp
  ring

theorem Xmap_P : R.Xmap R.P = ∞ := by
  simp only [Xmap, wmap_P, invOP_zero]

theorem continuous_wmap : Continuous R.wmap := by
  unfold wmap; fun_prop

/-- X は直線から `OnePoint ℝ` への連続写像で、P でだけ ∞ を取る。 -/
theorem continuous_Xmap : Continuous R.Xmap := continuous_invOP.comp R.continuous_wmap

theorem Xmap_eq_infty_iff (x : ℝ) : R.Xmap x = ∞ ↔ x = R.P := by
  have h := R.P_pos.ne'
  simp only [Xmap, invOP_eq_infty_iff, wmap]
  rw [div_eq_zero_iff]
  constructor
  · rintro (h1 | h1)
    · linarith
    · exact absurd h1 h
  · rintro rfl; left; ring

/-- 右の後半の段階：t′ₖ = t∗(1 + rᵏ)。 -/
def tn' (k : ℕ) : ℝ := R.tstar * (1 + R.r ^ k)

theorem g_tn' (k : ℕ) : R.g (R.tn' k) = -R.r ^ k := by
  have h := R.tstar_pos.ne'
  rw [g_eq]
  simp only [tn']
  field_simp
  ring

theorem continuous_g : Continuous R.g := by
  unfold g T A; fun_prop

theorem abs_g_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 2 * R.tstar) : |R.g t| ≤ 1 := by
  have hts := R.tstar_pos
  rw [g_eq, abs_le]
  have h2 : 0 ≤ t / R.tstar := by positivity
  have h3 : t / R.tstar ≤ 2 := by
    rw [div_le_iff₀ hts]; linarith
  constructor <;> linarith

theorem g_ne_zero {t : ℝ} (h : t ≠ R.tstar) : R.g t ≠ 0 := by
  have hts := R.tstar_pos
  rw [g_eq]
  intro h0
  apply h
  have : t / R.tstar = 1 := by linarith
  field_simp at this
  linarith

/-- g は減少する。 -/
theorem g_lt_g {s t : ℝ} (h : s < t) : R.g t < R.g s := by
  rw [g_eq, g_eq]
  have : s / R.tstar < t / R.tstar := div_lt_div_of_pos_right h R.tstar_pos
  linarith

theorem g_pos_of_lt {t : ℝ} (h : t < R.tstar) : 0 < R.g t := by
  have := R.g_lt_g h
  rwa [R.g_tstar] at this

theorem g_neg_of_gt {t : ℝ} (h : R.tstar < t) : R.g t < 0 := by
  have := R.g_lt_g h
  rwa [R.g_tstar] at this

theorem g_nonneg_of_le {t : ℝ} (h : t ≤ R.tstar) : 0 ≤ R.g t := by
  rcases eq_or_lt_of_le h with e | e
  · rw [e, g_tstar]
  · exact (R.g_pos_of_lt e).le

theorem g_nonpos_of_ge {t : ℝ} (h : R.tstar ≤ t) : R.g t ≤ 0 := by
  rcases eq_or_lt_of_le h with e | e
  · rw [← e, g_tstar]
  · exact (R.g_neg_of_gt e).le

theorem abs_g_lt_before {s t : ℝ} (hst : s < t) (ht : t ≤ R.tstar) : |R.g t| < |R.g s| := by
  have h1 := R.g_nonneg_of_le ht
  have h2 := R.g_lt_g hst
  rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)]
  exact h2

theorem abs_g_lt_after {s t : ℝ} (hs : R.tstar ≤ s) (hst : s < t) : |R.g s| < |R.g t| := by
  have h1 := R.g_nonpos_of_ge hs
  have h2 := R.g_lt_g hst
  rw [abs_of_nonpos h1, abs_of_nonpos (by linarith)]
  linarith

theorem abs_r_g_lt {t : ℝ} (ht : t ≠ R.tstar) : |R.r * R.g t| < |R.g t| := by
  have hg := abs_pos.mpr (R.g_ne_zero ht)
  rw [abs_mul, abs_of_pos R.r_pos]
  nlinarith [R.r_lt_one]

theorem abs_r_g_le (t : ℝ) : |R.r * R.g t| ≤ |R.g t| := by
  rw [abs_mul, abs_of_pos R.r_pos]
  nlinarith [R.r_lt_one, R.r_pos, abs_nonneg (R.g t)]

/-- 出発：g(0) = 1。 -/
theorem g_start : R.g 0 = 1 := by
  rw [g_eq]; simp

/-- 到着：g(2t∗) = −1。 -/
theorem g_end : R.g (2 * R.tstar) = -1 := by
  have h := R.tstar_pos.ne'
  rw [g_eq]
  field_simp
  ring

/-! ### 走者 -/

/-- 亀：直線 v = 0。 -/
def idealT (t : ℝ) : V3 := G (R.r * R.g t) 0

/-- アキレス：きりもみ v = θ(w)。 -/
def idealA (t : ℝ) : V3 := G (R.g t) (theta R.r (R.g t))

end Race

/-! ### 平面 α の余向き -/

/-- 平面 α の余向き：連続で消えない法線場。w = 0 では G の法線が定まらないので、条件は w ≠ 0 に置く。 -/
structure IsCoorientation (n : ℝ × ℝ → V3) : Prop where
  cont : Continuous n
  ne : ∀ p, n p ≠ wp
  perp : ∀ p, p.1 ≠ 0 → dot (n p) (Tv p.1 p.2) = 0 ∧ dot (n p) (Tw p.1 p.2) = 0

theorem continuous_N : Continuous fun p : ℝ × ℝ => N p.1 p.2 := by
  unfold N; fun_prop

theorem N_isCoorientation : IsCoorientation fun p => N p.1 p.2 where
  cont := continuous_N
  ne := fun p => N_ne_zero p.1 p.2
  perp := fun _ _ => ⟨dot_N_Tv _ _, dot_N_Tw _ _⟩

theorem dense_w_ne_zero : Dense {p : ℝ × ℝ | p.1 ≠ 0} := by
  have h : {p : ℝ × ℝ | p.1 ≠ 0} = ({0}ᶜ : Set ℝ) ×ˢ (univ : Set ℝ) := by
    ext q; simp
  rw [h]
  exact (dense_compl_singleton (0 : ℝ)).prod dense_univ

theorem cross_Tv_Tw_smul (w v : ℝ) : cross (Tv w v) (Tw w v) = (w ^ 3 / D w ^ 3) • N w v := by
  rw [cross_Tv_Tw]
  rfl

/-- **余向きの剛性（平面 α）**：連続な余向きは N の定符号の倍である。 -/
theorem coorientation_rigid {n : ℝ × ℝ → V3} (hn : IsCoorientation n) :
    ∃ c : ℝ × ℝ → ℝ, Continuous c ∧ (∀ p, n p = c p • N p.1 p.2) ∧
      ((∀ p, 0 < c p) ∨ (∀ p, c p < 0)) := by
  refine rigid_normal continuous_N (fun p => N_ne_zero p.1 p.2) hn.cont hn.ne dense_w_ne_zero ?_
  intro p hp
  obtain ⟨h1, h2⟩ := hn.perp p hp
  have h := cross_of_perp h1 h2
  rw [cross_Tv_Tw_smul, cross_smul_right] at h
  have hc : p.1 ^ 3 / D p.1 ^ 3 ≠ 0 := div_ne_zero (pow_ne_zero 3 hp) (pow_ne_zero 3 (D_ne _))
  have h' := congrArg (fun z : V3 => (p.1 ^ 3 / D p.1 ^ 3)⁻¹ • z) h
  simp only [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
  rw [h']
  simp [wp]

theorem side_G_N (w v : ℝ) : side (G w v) (N w v) = 2 * w ^ 5 / D w := dot_gradPhi_N w v

theorem side_G_N_pos {w : ℝ} (hw : 0 < w) (v : ℝ) : 0 < side (G w v) (N w v) := by
  rw [side_G_N]
  have := D_pos w
  positivity

theorem side_G_N_neg {w : ℝ} (hw : w < 0) (v : ℝ) : side (G w v) (N w v) < 0 := by
  rw [side_G_N]
  have hD := D_pos w
  have h5 : w ^ 5 < 0 := Odd.pow_neg (by decide) hw
  exact div_neg_of_neg_of_pos (by linarith) hD

/-- **表裏の反転（ラベルによらない形）**：どの連続な余向きをとっても、右岸と左岸で Φ のラベルが逆になる。 -/
theorem ideal_reversal {n : ℝ × ℝ → V3} (hn : IsCoorientation n) {w₁ w₂ : ℝ} (h₁ : 0 < w₁)
    (h₂ : w₂ < 0) (v₁ v₂ : ℝ) :
    side (G w₁ v₁) (n (w₁, v₁)) * side (G w₂ v₂) (n (w₂, v₂)) < 0 := by
  obtain ⟨c, -, hsm, hs⟩ := coorientation_rigid hn
  have h := (side_mul_of_rigid (α := ℝ × ℝ) (n := n) (N₀ := fun p => N p.1 p.2) (c := c) hsm hs
    (q₁ := G w₁ v₁) (q₂ := G w₂ v₂) (p₁ := (w₁, v₁)) (p₂ := (w₂, v₂))).1
  exact h (mul_neg_of_pos_of_neg (side_G_N_pos h₁ v₁) (side_G_N_neg h₂ v₂))

/-! ### 定理 A -/

/-- **定理 A**：理想形の結論の連言。走者や面のラベルは定義に入っていない。 -/
structure IdealPassage (R : Race) : Prop where
  /-- 直線の上の競走：ゼノンの段階、その極限、順序。 -/
  line_zeno : ∀ n : ℕ, R.A (R.tn (n + 1)) = R.T (R.tn n)
  line_limit : Tendsto R.tn atTop (𝓝 R.tstar)
  line_order : ∀ t, (0 < R.g t ↔ R.A t < R.T t) ∧ (R.g t < 0 ↔ R.T t < R.A t)
  /-- A1：形成写像と反転。 -/
  formation_A : ∀ t, R.wmap (R.A t) = R.g t
  formation_T : ∀ t, R.wmap (R.T t) = R.r * R.g t
  formation_P : R.wmap R.P = 0 ∧ R.Xmap R.P = ∞ ∧ Continuous R.Xmap ∧ ∀ x, R.Xmap x = ∞ ↔ x = R.P
  formation_step : ∀ k : ℕ, R.wmap (R.P * (1 - R.r ^ k)) = R.r ^ k
  collapse : ∀ v, G 0 v = wp
  periodic : ∀ w v, G w (v + 2 * π) = G w v ∧ N w (v + 2 * π) = N w v
  tangents : ∀ w v, HasDerivAt (fun w => G w v) (Tw w v) w ∧ HasDerivAt (fun v => G w v) (Tv w v) v
  orientation : ∀ w v, cross (Tv w v) (Tw w v) = (w ^ 3 / D w ^ 3) • N w v
  chart : ∀ w v, w ≠ 0 → inv3 (G w v) = H (1 / w) v
  horn_pair : ∀ u v, u ≠ 0 → inv3 (G (1 / u) v) = FR u v ∧ inv3 (G (-(1 / u)) v) = FL u (v + π)
  symmetric : ∀ w v, G (-w) v = -G w v
  mirror_sym : ∀ w v, G (-w) (v + π) = mirror (G w v) ∧ N (-w) (v + π) = -mirror (N w v)
  /-- 基準 Φ は両岸で同じ周囲の関数で、ホーンの方程式 x²ρ² = 1 の反転である。 -/
  surface_level : ∀ w v, Phi (G w v) = 0
  criterion : ∀ q, nsq q ≠ 0 →
    Phi q = nsq q ^ 4 * ((inv3 q).1 ^ 2 * ((inv3 q).2.1 ^ 2 + (inv3 q).2.2 ^ 2) - 1)
  /-- A2：無限捻転。導線は α の上で無限遠へ去り、像は ℘ へ収束し、法線に極限はない。 -/
  twist_step : ∀ w, w ≠ 0 → theta R.r (R.r * w) = theta R.r w + 2 * π
  twist_count : ∀ k : ℕ, theta R.r (R.r ^ k) = k * (2 * π)
  twist_escape : Tendsto (theta R.r) (𝓝[≠] 0) atTop
  twist_angle : ¬ ∃ a : Real.Angle, Tendsto (fun w => ((theta R.r w : ℝ) : Real.Angle)) (𝓝[>] 0) (𝓝 a)
  twist_image : Tendsto (fun w => G w (theta R.r w)) (𝓝 0) (𝓝 wp)
  twist_normal : ¬ ∃ n₀ : V3, Tendsto (fun w => N w (theta R.r w)) (𝓝[>] 0) (𝓝 n₀)
  /-- A3：異時刻の交差。t∗ の前はアキレスが亀の過去の位置に、後は亀がアキレスの過去の位置に着く。 -/
  meet_before : ∀ k : ℕ, R.tn k < R.tn (k + 1) ∧ R.idealA (R.tn (k + 1)) = R.idealT (R.tn k)
  meet_after : ∀ k : ℕ, R.tn' (k + 1) < R.tn' k ∧ R.idealT (R.tn' k) = R.idealA (R.tn' (k + 1))
  meet_discrete : meetings R.r = range (fun n : ℕ => R.r ^ n) ∧ (meetings R.r).Infinite ∧
    ∀ w₀ : ℝ, 0 < w₀ → (meetings R.r ∩ Ici w₀).Finite
  /-- 段の番号の無限遠は w = 0、すなわち ℘ に当たる（仮定 1）。 -/
  step_compact : Continuous (stepPoint R.r) ∧ Function.Injective (stepPoint R.r) ∧
    stepPoint R.r ∞ = 0
  /-- A4：表裏。亀は +N、アキレスは −N に立つ。ラベルは Φ で計算する。 -/
  coorientation : IsCoorientation (fun p => N p.1 p.2)
  rigid : ∀ n, IsCoorientation n → ∀ w₁ w₂ v₁ v₂, 0 < w₁ → w₂ < 0 →
    side (G w₁ v₁) (n (w₁, v₁)) * side (G w₂ v₂) (n (w₂, v₂)) < 0
  frame_law : ∀ w v, (G (-w) v, N (-w) v) = Everse (G w v, N w v)
  side_T_before : ∀ t, t < R.tstar → Front (R.idealT t) (N (R.r * R.g t) 0)
  side_T_after : ∀ t, R.tstar < t → Back (R.idealT t) (N (R.r * R.g t) 0)
  side_A_before : ∀ t, t < R.tstar →
    Back (R.idealA t) (-N (R.g t) (theta R.r (R.g t)))
  side_A_after : ∀ t, R.tstar < t →
    Front (R.idealA t) (-N (R.g t) (theta R.r (R.g t)))
  /-- A5：前後。ホーンの軸の座標の差は 0 にならず、t∗ で ∞ を通る。 -/
  order_xhat : ∀ t, t ≠ R.tstar →
    xhat (R.idealT t) - xhat (R.idealA t) = (1 - R.r) / (R.r * R.g t)
  order_before : ∀ t, t < R.tstar → xhat (R.idealA t) < xhat (R.idealT t)
  order_after : ∀ t, R.tstar < t → xhat (R.idealT t) < xhat (R.idealA t)
  door : Continuous (fun t => invOP (R.g t)) ∧ Continuous (fun t => invOP (R.r * R.g t)) ∧
    (∀ t, invOP (R.g t) = ∞ ↔ t = R.tstar) ∧ (∀ t, invOP (R.r * R.g t) = ∞ ↔ t = R.tstar) ∧
    (∀ t, t ≠ R.tstar → invOP (R.g t) = ((xhat (R.idealA t) : ℝ) : OnePoint ℝ) ∧
      invOP (R.r * R.g t) = ((xhat (R.idealT t) : ℝ) : OnePoint ℝ))
  /-- 実数値のままでは両岸の行き先が違い、`OnePoint ℝ` では同じ ∞ に閉じる（C.f. 中間値の定理）。 -/
  door_limits : Tendsto (fun w : ℝ => w⁻¹) (𝓝[>] 0) atTop ∧ Tendsto (fun w : ℝ => w⁻¹) (𝓝[<] 0) atBot
  door_forced : ∀ a b : ℝ, a ≤ b → ∀ γ : ℝ → OnePoint ℝ, ContinuousOn γ (Icc a b) → ∀ xa xb : ℝ,
    γ a = (xa : OnePoint ℝ) → 0 < xa → γ b = (xb : OnePoint ℝ) → xb < 0 →
    ∃ t ∈ Icc a b, γ t = ((0 : ℝ) : OnePoint ℝ) ∨ γ t = ∞
  door_not_zero : ∀ w, invOP w ≠ ((0 : ℝ) : OnePoint ℝ)
  /-- A5：追従の向き。t∗ までは亀がアキレスの過去の位置に来ることはなく、t∗ 以後はその逆。 -/
  follow_before : ∀ s t, 0 ≤ s → s < t → t ≤ R.tstar → R.idealT t ≠ R.idealA s
  follow_after : ∀ s t, R.tstar ≤ s → s < t → t ≤ 2 * R.tstar → R.idealA t ≠ R.idealT s
  /-- A6：同時刻の位置。t∗ 以外では亀の方が ℘ に近い。t∗ では両者とも ℘ にいる（隠さない）。 -/
  nearer : ∀ t ∈ Icc 0 (2 * R.tstar), t ≠ R.tstar → nsq (R.idealT t) < nsq (R.idealA t)
  coincide : R.idealT R.tstar = wp ∧ R.idealA R.tstar = wp
  /-- A7：ガブリエルのホーン：体積は有限、面積は無限。 -/
  horn_volume : ∀ x, 1 ≤ x → hornV x ≤ π
  horn_area : Tendsto hornA atTop atTop
  /-- A7：ホーンの辞書。比較モデルでは崩れる。 -/
  dictionary_time : ∀ t, 0 ≤ t → t < R.tstar → hornV (1 / R.g t) / π = t / R.tstar
  dictionary_area : Tendsto (fun n : ℕ => hornA (1 / R.g (R.tn n))) atTop atTop
  dictionary_thin : Tendsto thinV atTop atTop
  dictionary_fat : ∀ x, 1 ≤ x → fatA x ≤ 2 * π * √5

/-! ### 定理 A の証明 -/

theorem theta_mul {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {w : ℝ} (hw : w ≠ 0) :
    theta r (r * w) = theta r w + 2 * π := by
  have hl := log_r_ne hr0 hr1
  simp only [theta, abs_mul, abs_of_pos hr0]
  rw [Real.log_mul hr0.ne' (abs_ne_zero.mpr hw)]
  field_simp
  ring

theorem tendsto_theta {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : Tendsto (theta r) (𝓝[≠] 0) atTop := by
  have hlog : log r < 0 := Real.log_neg hr0 hr1
  have h1 : Tendsto (fun w => log |w|) (𝓝[≠] 0) atBot := by
    simpa only [Real.log_abs] using Real.tendsto_log_nhdsNE_zero
  have hc : 2 * π / log r < 0 := div_neg_of_pos_of_neg (by positivity) hlog
  have h2 : Tendsto (fun w => (2 * π / log r) * log |w|) (𝓝[≠] 0) atTop :=
    h1.const_mul_atBot_of_neg hc
  refine h2.congr fun w => ?_
  simp only [theta]
  ring

theorem G_theta_pow {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {w : ℝ} {k : ℕ} (hw : |w| = r ^ k) :
    G w (theta r w) = G w 0 := by
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, abs_zero] at hw
    exact (pow_pos hr0 k).ne hw
  exact (meeting_iff hr0 hr1 hw0).2 ⟨k, by rw [hw, zpow_natCast]⟩

/-- **定理 A**。 -/
theorem ideal_passage (R : Race) : IdealPassage R := by
  have hr0 := R.r_pos
  have hr1 := R.r_lt_one
  have hts := R.tstar_pos
  refine
    { line_zeno := R.A_succ_eq_T
      line_limit := R.tendsto_tn
      line_order := fun t => ⟨R.g_pos_iff t, R.g_neg_iff t⟩
      formation_A := R.wmap_A
      formation_T := R.wmap_T
      formation_P := ⟨R.wmap_P, R.Xmap_P, R.continuous_Xmap, R.Xmap_eq_infty_iff⟩
      formation_step := R.wmap_step
      collapse := G_zero
      periodic := fun w v => ⟨G_periodic w v, N_periodic w v⟩
      tangents := fun w v => ⟨hasDerivAt_G_w w v, hasDerivAt_G_v w v⟩
      orientation := cross_Tv_Tw_smul
      chart := fun w v hw => inv3_G_eq_H hw v
      horn_pair := fun u v hu => ⟨inv3_G_right hu v, inv3_G_left hu v⟩
      symmetric := G_odd
      mirror_sym := fun w v => ⟨G_mirror w v, N_mirror w v⟩
      surface_level := Phi_G
      criterion := fun q hq => Phi_eq_horn hq
      twist_step := fun w hw => theta_mul hr0 hr1 hw
      twist_count := theta_pow hr0 hr1
      twist_escape := tendsto_theta hr0 hr1
      twist_angle := no_angle_limit hr0 hr1
      twist_image := tendsto_G_wp _
      twist_normal := normal_no_limit hr0 hr1
      meet_before := ?_
      meet_after := ?_
      meet_discrete := ⟨meetings_eq hr0 hr1, meetings_infinite hr0 hr1,
        fun w₀ h => meetings_finite_off_wp hr0 hr1 h⟩
      step_compact := ⟨continuous_stepPoint hr0 hr1, injective_stepPoint hr0 hr1, rfl⟩
      coorientation := N_isCoorientation
      rigid := fun n hn w₁ w₂ v₁ v₂ h₁ h₂ => ideal_reversal hn h₁ h₂ v₁ v₂
      frame_law := fun w v => by
        simp only [Everse, G_odd, N_even]
      side_T_before := ?_
      side_T_after := ?_
      side_A_before := ?_
      side_A_after := ?_
      order_xhat := ?_
      order_before := ?_
      order_after := ?_
      door := ?_
      door_limits := inv_right_left
      door_forced := fun a b hab γ hγ xa xb h0 hxa h1 hxb => two_doors hab hγ h0 hxa h1 hxb
      door_not_zero := invOP_ne_zero
      follow_before := ?_
      follow_after := ?_
      nearer := ?_
      coincide := ?_
      horn_volume := fun x hx => hornV_le hx
      horn_area := tendsto_hornA
      dictionary_time := fun t h0 h1 => R.dict_time h0 h1
      dictionary_area := R.tendsto_steps_area
      dictionary_thin := tendsto_thinV
      dictionary_fat := fun x hx => fatA_le hx }
  · intro k
    constructor
    · simp only [Race.tn, pow_succ]
      have hp := pow_pos hr0 k
      have : R.r ^ k * R.r < R.r ^ k := by nlinarith
      nlinarith
    · simp only [Race.idealA, Race.idealT, R.g_tn]
      rw [G_theta_pow hr0 hr1 (k := k + 1) (abs_of_pos (pow_pos hr0 _)), pow_succ']
  · intro k
    constructor
    · simp only [Race.tn', pow_succ]
      have hp := pow_pos hr0 k
      have : R.r ^ k * R.r < R.r ^ k := by nlinarith
      nlinarith
    · simp only [Race.idealA, Race.idealT, R.g_tn']
      rw [G_theta_pow hr0 hr1 (k := k + 1) (by rw [abs_neg, abs_of_pos (pow_pos hr0 _)])]
      congr 1
      rw [pow_succ']
      ring
  · intro t ht
    exact side_G_N_pos (mul_pos hr0 (R.g_pos_of_lt ht)) 0
  · intro t ht
    exact side_G_N_neg (mul_neg_of_pos_of_neg hr0 (R.g_neg_of_gt ht)) 0
  · intro t ht
    simp only [Back, Race.idealA, side_neg]
    have := side_G_N_pos (R.g_pos_of_lt ht) (theta R.r (R.g t))
    linarith
  · intro t ht
    simp only [Front, Race.idealA, side_neg]
    have := side_G_N_neg (R.g_neg_of_gt ht) (theta R.r (R.g t))
    linarith
  · intro t ht
    have hg := R.g_ne_zero ht
    simp only [Race.idealA, Race.idealT]
    rw [xhat_G (mul_ne_zero hr0.ne' hg), xhat_G hg]
    field_simp
  · intro t ht
    have hg := R.g_pos_of_lt ht
    simp only [Race.idealA, Race.idealT]
    rw [xhat_G (mul_ne_zero hr0.ne' hg.ne'), xhat_G hg.ne']
    exact one_div_lt_one_div_of_lt (mul_pos hr0 hg) (by nlinarith)
  · intro t ht
    have hg := R.g_neg_of_gt ht
    simp only [Race.idealA, Race.idealT]
    rw [xhat_G (mul_ne_zero hr0.ne' hg.ne), xhat_G hg.ne]
    have hinv : 1 / R.g t < 0 := one_div_neg.mpr hg
    have hr : 1 < 1 / R.r := by rw [lt_div_iff₀ hr0]; linarith
    have e : 1 / (R.r * R.g t) = 1 / R.r * (1 / R.g t) := by field_simp
    rw [e]; nlinarith
  · refine ⟨continuous_invOP.comp R.continuous_g,
      continuous_invOP.comp (continuous_const.mul R.continuous_g), ?_, ?_, ?_⟩
    · intro t
      rw [invOP_eq_infty_iff, R.g_eq_zero_iff]
    · intro t
      rw [invOP_eq_infty_iff, mul_eq_zero, R.g_eq_zero_iff]
      simp [hr0.ne']
    · intro t ht
      have hg := R.g_ne_zero ht
      simp only [Race.idealA, Race.idealT]
      rw [xhat_G hg, xhat_G (mul_ne_zero hr0.ne' hg), invOP_of_ne hg,
        invOP_of_ne (mul_ne_zero hr0.ne' hg)]
      simp only [one_div, and_self]
  · intro s t hs hst ht he
    have hlt : |R.r * R.g t| < |R.g s| := (R.abs_r_g_le t).trans_lt (R.abs_g_lt_before hst ht)
    have := nsq_G_lt hlt (R.abs_g_le hs (by linarith)) 0 (theta R.r (R.g s))
    simp only [Race.idealA, Race.idealT] at he
    rw [he] at this
    exact lt_irrefl _ this
  · intro s t hs hst ht he
    have hlt : |R.r * R.g s| < |R.g t| := (R.abs_r_g_le s).trans_lt (R.abs_g_lt_after hs hst)
    have := nsq_G_lt hlt (R.abs_g_le (by linarith) ht) 0 (theta R.r (R.g t))
    simp only [Race.idealA, Race.idealT] at he
    rw [← he] at this
    exact lt_irrefl _ this
  · intro t ht htne
    have hg := R.g_ne_zero htne
    have hle := R.abs_g_le ht.1 ht.2
    simp only [Race.idealA, Race.idealT]
    refine nsq_G_lt ?_ hle _ _
    rw [abs_mul, abs_of_pos hr0]
    have := abs_pos.mpr hg
    nlinarith
  · simp only [Race.idealA, Race.idealT, R.g_tstar, mul_zero, G_zero, and_self]

end Zeno.Model
