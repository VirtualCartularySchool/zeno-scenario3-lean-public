/-
# ZenoSmale.KleinQuotient : 商曲面 M = ℝ²/Γ（位相空間として）と、M の上の M2

`KleinCover` の群 Γ = {γ_{k,m}} による ℝ² の商を、Lean の型 `KleinM` として作る（商位相）。

- `KleinM` はコンパクトなハウスドルフ空間であり、射影 `toM` は連続な開写像で、半径 2 の開球の上で
  単射である。したがって M は局所的に ℝ² と同相な閉じた位相曲面である。
- Γ 不変な写像は M の上の写像に降下し、連続性は保たれる（`descend`、`continuous_descend`）。
  源曲面 Ŝ と族の各段 F_s は M から ℝ³ への連続写像 `ShatM`、`FM` になる。
- **M の上の M2**：Ω で符号を変える連続で消えない法線 X について、M の上に、各点で X に平行な
  連続で消えない法線場はない（`no_normal_on_M`）。
- 終点が始点の Ω⁻¹ による像である道は、M の上で閉じている（`toM_Omega_inv`）。

M の滑らかな構造（座標は `toM` の局所的な逆、座標変換は Γ の元）と、降下した写像のはめ込み性は
本文で述べる。Mathlib の商多様体は座標つき空間の構造までであり、滑らかさは未整備である。
-/
import ZenoSmale.KleinCover

noncomputable section

namespace Zeno.Smale

open Metric Set Function Filter Topology Real
open scoped ContDiff
open Zeno.Model

/-! ### Γ の元は等長な同相写像である -/

theorem abs_sgn (k : ℤ) : |sgn k| = 1 := by
  rcases sgn_eq k with h | h <;> rw [h] <;> simp

/-- γ_{k,m} は等長である。 -/
theorem dist_gam (k m : ℤ) (p q : ℝ × ℝ) : dist (gam k m p) (gam k m q) = dist p q := by
  rw [Prod.dist_eq, Prod.dist_eq]
  simp only [gam, Real.dist_eq]
  have e1 : p.1 + 4 * (k : ℝ) - (q.1 + 4 * (k : ℝ)) = p.1 - q.1 := by ring
  have e2 : sgn k * p.2 + (m : ℝ) * (2 * π) - (sgn k * q.2 + (m : ℝ) * (2 * π)) =
      sgn k * (p.2 - q.2) := by ring
  rw [e1, e2, abs_mul, abs_sgn, one_mul]

theorem continuous_gam (k m : ℤ) : Continuous (gam k m) := by
  unfold gam
  fun_prop

/-- 軌道の異なる二点は距離 4 以上離れている。 -/
theorem four_le_dist_orbit {k m k' m' : ℤ} (h : k ≠ k' ∨ m ≠ m') (p : ℝ × ℝ) :
    4 ≤ dist (gam k' m' p) (gam k m p) := by
  have e : gam k' m' p = gam (k' + -k) (m' + sgnZ k' * -(sgnZ k * m)) (gam k m p) := by
    rw [← gam_comp, gam_inv]
  rw [e]
  apply four_le_dist_gam
  by_cases hk : k = k'
  · right
    subst hk
    have hm : m ≠ m' := by tauto
    have h2 : sgnZ k * -(sgnZ k * m) = -m := by
      have := sgnZ_mul_self k
      linear_combination (-m) * this
    rw [h2]
    intro h0
    apply hm
    linarith
  · left
    intro h0
    apply hk
    linarith

/-! ### 商 M = ℝ²/Γ -/

/-- Γ の軌道の同値関係。 -/
def gamSetoid : Setoid (ℝ × ℝ) where
  r p q := ∃ k m : ℤ, gam k m p = q
  iseqv :=
    { refl := fun p => ⟨0, 0, gam_zero p⟩
      symm := fun {p q} ⟨k, m, h⟩ => ⟨-k, -(sgnZ k * m), by rw [← h]; exact gam_inv k m p⟩
      trans := fun {p q u} ⟨k, m, h⟩ ⟨k', m', h'⟩ =>
        ⟨k' + k, m' + sgnZ k' * m, by rw [← h', ← h, gam_comp]⟩ }

/-- **商曲面** M = ℝ²/Γ（商位相をもつ位相空間）。 -/
def KleinM : Type := Quotient gamSetoid

instance : TopologicalSpace KleinM := inferInstanceAs (TopologicalSpace (Quotient gamSetoid))

/-- 被覆写像 ℝ² → M。 -/
def toM (p : ℝ × ℝ) : KleinM := Quotient.mk gamSetoid p

theorem continuous_toM : Continuous toM := continuous_quotient_mk'

theorem toM_surjective : Surjective toM := Quotient.mk_surjective

theorem toM_eq_iff {p q : ℝ × ℝ} : toM p = toM q ↔ ∃ k m : ℤ, gam k m p = q :=
  Quotient.eq (r := gamSetoid)

theorem toM_gam (k m : ℤ) (p : ℝ × ℝ) : toM (gam k m p) = toM p :=
  (toM_eq_iff.mpr ⟨k, m, rfl⟩).symm

/-- 終点が始点の Ω⁻¹ による像である道は、M の上で閉じている。 -/
theorem toM_Omega_inv (p : ℝ × ℝ) : toM (p.1 - 4, -p.2) = toM p := by
  have e : gam (-1) 0 p = (p.1 - 4, -p.2) := by
    have hs : sgn (-1) = -1 := by rw [sgn_neg, sgn_one]
    simp only [gam, hs]
    refine Prod.ext ?_ ?_
    · push_cast; ring
    · push_cast; ring
  rw [← e, toM_gam]

theorem preimage_image_toM (U : Set (ℝ × ℝ)) :
    toM ⁻¹' (toM '' U) = ⋃ (k : ℤ) (m : ℤ), gam k m ⁻¹' U := by
  ext x
  simp only [mem_preimage, mem_image, mem_iUnion]
  constructor
  · rintro ⟨u, hu, h⟩
    obtain ⟨k, m, hkm⟩ := toM_eq_iff.mp h.symm
    exact ⟨k, m, hkm ▸ hu⟩
  · rintro ⟨k, m, h⟩
    exact ⟨gam k m x, h, toM_gam k m x⟩

/-- 被覆写像は開写像である。 -/
theorem isOpenMap_toM : IsOpenMap toM := by
  intro U hU
  have hq : IsQuotientMap toM := isQuotientMap_quotient_mk'
  rw [← hq.isOpen_preimage, preimage_image_toM]
  exact isOpen_iUnion fun k => isOpen_iUnion fun m => hU.preimage (continuous_gam k m)

/-- 被覆写像は半径 2 の開球の上で単射である（均等被覆近傍）。 -/
theorem toM_injOn_ball (p : ℝ × ℝ) : InjOn toM (ball p 2) := by
  intro a ha b hb hab
  obtain ⟨k, m, hkm⟩ := toM_eq_iff.mp hab
  by_cases h : k ≠ 0 ∨ m ≠ 0
  · exfalso
    have := gam_ball_disjoint h p ha
    rw [hkm] at this
    exact this hb
  · push Not at h
    rw [h.1, h.2, gam_zero] at hkm
    exact hkm

/-- **M はコンパクトである**（基本領域 [−1, 3] × [0, 2π] の像）。 -/
instance kleinM_compactSpace : CompactSpace KleinM := by
  refine ⟨?_⟩
  have hK : IsCompact (Icc (-1 : ℝ) 3 ×ˢ Icc (0 : ℝ) (2 * π)) := isCompact_Icc.prod isCompact_Icc
  have himg : toM '' (Icc (-1 : ℝ) 3 ×ˢ Icc (0 : ℝ) (2 * π)) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨p, rfl⟩ := toM_surjective x
    obtain ⟨k, m, h1, h2⟩ := exists_gam_mem_fundamental p
    exact ⟨gam k m p, ⟨Ico_subset_Icc_self h1, Ico_subset_Icc_self h2⟩, toM_gam k m p⟩
  rw [← himg]
  exact hK.image continuous_toM

/-- 軌道に入らない点は、軌道から一様に離れている。 -/
theorem exists_orbit_gap {p q : ℝ × ℝ} (hne : ∀ k m : ℤ, gam k m p ≠ q) :
    ∃ δ > 0, ∀ k m : ℤ, δ ≤ dist (gam k m p) q := by
  by_cases h : ∀ k m : ℤ, 1 ≤ dist (gam k m p) q
  · exact ⟨1, one_pos, h⟩
  · push Not at h
    obtain ⟨k₀, m₀, h₀⟩ := h
    have hpos : 0 < dist (gam k₀ m₀ p) q := dist_pos.mpr (hne k₀ m₀)
    refine ⟨dist (gam k₀ m₀ p) q, hpos, fun k m => ?_⟩
    by_cases hkm : k₀ ≠ k ∨ m₀ ≠ m
    · have h4 := four_le_dist_orbit hkm p
      have htri := dist_triangle (gam k m p) q (gam k₀ m₀ p)
      rw [dist_comm q (gam k₀ m₀ p)] at htri
      linarith
    · push Not at hkm
      rw [hkm.1, hkm.2]

/-- **M はハウスドルフ空間である**。 -/
instance kleinM_t2Space : T2Space KleinM := by
  refine ⟨fun x y hxy => ?_⟩
  obtain ⟨p, rfl⟩ := toM_surjective x
  obtain ⟨q, rfl⟩ := toM_surjective y
  have hne : ∀ k m : ℤ, gam k m p ≠ q := fun k m h => hxy (toM_eq_iff.mpr ⟨k, m, h⟩)
  obtain ⟨δ, hδ, hd⟩ := exists_orbit_gap hne
  refine ⟨toM '' ball p (δ / 2), toM '' ball q (δ / 2), isOpenMap_toM _ isOpen_ball,
    isOpenMap_toM _ isOpen_ball, ⟨p, mem_ball_self (half_pos hδ), rfl⟩,
    ⟨q, mem_ball_self (half_pos hδ), rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  obtain ⟨k, m, hkm⟩ := toM_eq_iff.mp hab.symm
  have h1 : dist (gam k m p) (gam k m a) = dist p a := dist_gam k m p a
  have htri := dist_triangle (gam k m p) (gam k m a) q
  rw [h1, hkm] at htri
  have ha' := mem_ball.mp ha
  have hb' := mem_ball.mp hb
  rw [dist_comm] at ha'
  linarith [hd k m]

/-! ### Γ 不変な写像の降下 -/

/-- Γ 不変な写像の M への降下。 -/
def descend {α : Type*} (G : ℝ → ℝ → α)
    (h : ∀ (k m : ℤ) (p : ℝ × ℝ), G (gam k m p).1 (gam k m p).2 = G p.1 p.2) : KleinM → α :=
  Quotient.lift (fun p : ℝ × ℝ => G p.1 p.2) (fun p q hpq => by
    obtain ⟨k, m, hkm⟩ := hpq
    rw [← hkm]
    exact (h k m p).symm)

theorem descend_toM {α : Type*} (G : ℝ → ℝ → α)
    (h : ∀ (k m : ℤ) (p : ℝ × ℝ), G (gam k m p).1 (gam k m p).2 = G p.1 p.2) (p : ℝ × ℝ) :
    descend G h (toM p) = G p.1 p.2 := rfl

theorem continuous_descend {α : Type*} [TopologicalSpace α] {G : ℝ → ℝ → α}
    (h : ∀ (k m : ℤ) (p : ℝ × ℝ), G (gam k m p).1 (gam k m p).2 = G p.1 p.2)
    (hG : Continuous (fun p : ℝ × ℝ => G p.1 p.2)) : Continuous (descend G h) :=
  hG.quotient_lift _

/-- 源曲面から ℝ³ への写像 Ŝ̄ : M → ℝ³。 -/
def ShatM (w₀ : ℝ) : KleinM → V3 := descend (Shat w₀) (Shat_gam w₀)

theorem ShatM_toM (w₀ : ℝ) (p : ℝ × ℝ) : ShatM w₀ (toM p) = Shat w₀ p.1 p.2 := rfl

theorem continuous_ShatM {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) : Continuous (ShatM w₀) :=
  continuous_descend (Shat_gam w₀) (contDiff_Shat h0 h1).continuous

section Family

variable {w₀ ε : ℝ} {F : ℝ → ℝ → ℝ → V3} (E : NeckEversion w₀ ε (Shat w₀) F)

/-- 族の各段の M の上の写像 F̄_s : M → ℝ³。 -/
def FM (E : NeckEversion w₀ ε (Shat w₀) F) (s : ℝ) : KleinM → V3 := descend (F s) (F_gam E s)

theorem FM_toM (s : ℝ) (p : ℝ × ℝ) : FM E s (toM p) = F s p.1 p.2 := rfl

theorem continuous_FM (s : ℝ) : Continuous (FM E s) :=
  continuous_descend (F_gam E s)
    (E.smooth.continuous.comp (continuous_const.prodMk continuous_id))

/-- s ≤ 0 では F̄_s = Ŝ̄。 -/
theorem FM_of_start {s : ℝ} (hs : s ≤ 0) : FM E s = ShatM w₀ := by
  funext x
  obtain ⟨p, rfl⟩ := toM_surjective x
  rw [FM_toM, ShatM_toM]
  exact E.start s p.1 p.2 hs

end Family

/-! ### M の上の M2 -/

/-- **M の上の M2**：Ω で符号を変える連続で消えない法線 X について、M の上に、各点で X に平行な
連続で消えない法線場はない。 -/
theorem no_normal_on_M {X : ℝ → ℝ → V3} (hX : Continuous (fun p : ℝ × ℝ => X p.1 p.2))
    (hne : ∀ w v, X w v ≠ wp) (hglide : ∀ w v, X (w + 4) (-v) = -X w v) :
    ¬ ∃ n : KleinM → V3, Continuous n ∧ (∀ x, n x ≠ wp) ∧
      (∀ p : ℝ × ℝ, cross (n (toM p)) (X p.1 p.2) = wp) := by
  rintro ⟨n, hn, hn0, hpar⟩
  exact no_gam_invariant_normal hX hne hglide
    ⟨n ∘ toM, hn.comp continuous_toM, fun p => hn0 _, hpar,
      fun k m p => by simp only [Function.comp, toM_gam]⟩

/-- 静的な源曲面 Ŝ̄ : M → ℝ³ は一側である。 -/
theorem ShatM_one_sided {w₀ : ℝ} (h0 : 0 < w₀) (h1 : w₀ < 1) :
    ¬ ∃ n : KleinM → V3, Continuous n ∧ (∀ x, n x ≠ wp) ∧
      (∀ p : ℝ × ℝ, cross (n (toM p)) (Xhat w₀ p.1 p.2) = wp) :=
  no_normal_on_M (continuous_Xhat h0 h1) (Xhat_ne h0 h1) (Xhat_glide h0 h1)

/-- 族の各段 F̄_s : M → ℝ³ は一側である。 -/
theorem FM_one_sided {w₀ ε : ℝ} {F : ℝ → ℝ → ℝ → V3} (E : NeckEversion w₀ ε (Shat w₀) F)
    (s : ℝ) : ¬ ∃ n : KleinM → V3, Continuous n ∧ (∀ x, n x ≠ wp) ∧
      (∀ p : ℝ × ℝ, cross (n (toM p)) (XF F s p.1 p.2) = wp) :=
  no_normal_on_M (continuous_XF E s) (XF_ne E s) (XF_glide E s)

/-! ### 走者の閉路は源曲面 M の上で閉じている -/

/-- **亀の閉路（M の上の形）**：`KleinPassage` の閉路は、像の一致ではなく源曲面 M の上で閉じており
（toM (γ(3t∗)) = toM (γ(0))）、それに沿って運んだ側は反転して戻る。 -/
theorem KleinPassage.loop_T_on_M {R : Race} {w₀ c : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3}
    {Vt Va : ℝ → ℝ} (P : KleinPassage R w₀ c n₁ S X Vt Va) :
    ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.r * R.g t, Vt (R.r * R.g t))) ∧
      toM (γ (3 * R.tstar)) = toM (γ 0) ∧
      (∀ n : ℝ → V3, Continuous n → (∀ s, n s ≠ wp) →
        (∀ s, cross (n s) (X (γ s).1 (γ s).2) = wp) →
        ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0)) := by
  obtain ⟨γ, h1, h2, h3, h4⟩ := P.loop_T
  exact ⟨γ, h1, h2, by rw [h3, toM_Omega_inv], h4⟩

/-- **アキレスの閉路（M の上の形）**。 -/
theorem KleinPassage.loop_A_on_M {R : Race} {w₀ c : ℝ} {n₁ : ℕ} {S X : ℝ → ℝ → V3}
    {Vt Va : ℝ → ℝ} (P : KleinPassage R w₀ c n₁ S X Vt Va) :
    ∃ γ : ℝ → ℝ × ℝ, ContDiff ℝ ∞ γ ∧
      (∀ t ∈ Icc 0 (2 * R.tstar), γ t = (R.g t, Va (R.g t))) ∧
      toM (γ (3 * R.tstar)) = toM (γ 0) ∧
      (∀ n : ℝ → V3, Continuous n → (∀ s, n s ≠ wp) →
        (∀ s, cross (n s) (X (γ s).1 (γ s).2) = wp) →
        ∃ κ : ℝ, 0 < κ ∧ n (3 * R.tstar) = -(κ • n 0)) := by
  obtain ⟨γ, h1, h2, h3, h4⟩ := P.loop_A
  exact ⟨γ, h1, h2, by rw [h3, toM_Omega_inv], h4⟩

end Zeno.Smale
