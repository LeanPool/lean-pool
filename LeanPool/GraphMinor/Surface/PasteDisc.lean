/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Gluing
import Mathlib.Analysis.Complex.Basic

/-!
# Pasting a closed disc onto a cuff

`paste_disc : PasteDiscStatement`: pasting a closed disc onto a cuff `C` of a surface gives a
surface.

The space is the quotient of the sum of `S` and the closed disc of `ℂ` that pastes each point `z`
of the unit circle to `b z`, for a homeomorphism `b` from the circle onto `C`. It is compact and
Hausdorff by `t2Space_quotient_of_isClosed`. Points off `C` keep their charts. At a point of `C`,
take
a half plane chart of `S`, and on the disc side use polar coordinates, with the angle read off
this chart. The two half rectangles paste to a rectangle around the point
(`isInteriorPoint_pasted`).
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The closed disc of `ℂ`, as a type. -/
abbrev DiscType : Type := closedBall (0 : ℂ) 1

/-- `a` and `a'` are equal, or pasted: one is `z` on the unit circle and the other is `b z`. -/
def pasteRel (b : ℂ → S) (a a' : S ⊕ DiscType) : Prop :=
  a = a' ∨ (∃ z : DiscType, z.1 ∈ sphere (0 : ℂ) 1 ∧ a = .inl (b z) ∧ a' = .inr z) ∨
    (∃ z : DiscType, z.1 ∈ sphere (0 : ℂ) 1 ∧ a = .inr z ∧ a' = .inl (b z))

/-- The relation `pasteRel` is an equivalence relation, since `b` is injective on the circle. -/
def pasteSetoid {b : ℂ → S} (hb : InjOn b (sphere (0 : ℂ) 1)) : Setoid (S ⊕ DiscType) where
  r := pasteRel b
  iseqv :=
    { refl := fun _ => .inl rfl
      symm := by
        rintro a a' (rfl | ⟨z, hz, rfl, rfl⟩ | ⟨z, hz, rfl, rfl⟩)
        · exact .inl rfl
        · exact .inr (.inr ⟨z, hz, rfl, rfl⟩)
        · exact .inr (.inl ⟨z, hz, rfl, rfl⟩)
      trans := by
        rintro a a' a'' (rfl | ⟨z, hz, rfl, rfl⟩ | ⟨z, hz, rfl, rfl⟩) h'
        · exact h'
        · obtain rfl | ⟨w, hw, h1, rfl⟩ | ⟨w, hw, h1, rfl⟩ := h'
          · exact .inr (.inl ⟨z, hz, rfl, rfl⟩)
          · exact absurd h1 (by simp)
          · have : z = w := Sum.inr.inj h1
            subst this
            exact .inl rfl
        · obtain rfl | ⟨w, hw, h1, rfl⟩ | ⟨w, hw, h1, rfl⟩ := h'
          · exact .inr (.inr ⟨z, hz, rfl, rfl⟩)
          · have : z = w := Subtype.ext (hb hz hw (Sum.inl.inj h1))
            subst this
            exact .inl rfl
          · exact absurd h1 (by simp) }

/-- The space obtained by pasting the closed disc onto `S` along `b`. -/
def Pasted {b : ℂ → S} (hb : InjOn b (sphere (0 : ℂ) 1)) : Type u := Quotient (pasteSetoid hb)

instance {b : ℂ → S} (hb : InjOn b (sphere (0 : ℂ) 1)) : TopologicalSpace (Pasted hb) :=
  inferInstanceAs (TopologicalSpace (Quotient (pasteSetoid hb)))

variable {b : ℂ → S} (hb : InjOn b (sphere (0 : ℂ) 1))

/-- The map from `S` to the pasted space. -/
def Pasted.ι : S → Pasted hb := fun s => Quotient.mk (pasteSetoid hb) (.inl s)

/-- The map from the closed disc to the pasted space. -/
def Pasted.δ : DiscType → Pasted hb := fun z => Quotient.mk (pasteSetoid hb) (.inr z)

omit [TopologicalSpace S] in
theorem Pasted.ι_eq_ι {s s' : S} : Pasted.ι hb s = Pasted.ι hb s' ↔ s = s' := by
  constructor
  · intro h
    obtain h | ⟨z, -, -, h⟩ | ⟨z, -, h, -⟩ := Quotient.exact h
    · exact Sum.inl.inj h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · rintro rfl
    rfl

omit [TopologicalSpace S] in
theorem Pasted.δ_eq_δ {z z' : DiscType} : Pasted.δ hb z = Pasted.δ hb z' ↔ z = z' := by
  constructor
  · intro h
    obtain h | ⟨w, -, h, -⟩ | ⟨w, -, -, h⟩ := Quotient.exact h
    · exact Sum.inr.inj h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
  · rintro rfl
    rfl

omit [TopologicalSpace S] in
theorem Pasted.ι_eq_δ {s : S} {z : DiscType} :
    Pasted.ι hb s = Pasted.δ hb z ↔ z.1 ∈ sphere (0 : ℂ) 1 ∧ s = b z := by
  constructor
  · intro h
    obtain h | ⟨w, hw, h1, h2⟩ | ⟨w, -, h, -⟩ := Quotient.exact h
    · exact absurd h (by simp)
    · have h3 : w = z := (Sum.inr.inj h2).symm
      subst h3
      exact ⟨hw, Sum.inl.inj h1⟩
    · exact absurd h (by simp)
  · rintro ⟨hz, rfl⟩
    exact Quotient.sound (.inr (.inl ⟨z, hz, rfl, rfl⟩))

omit [TopologicalSpace S] in
theorem Pasted.surj (p : Pasted hb) : (∃ s, p = Pasted.ι hb s) ∨ ∃ z, p = Pasted.δ hb z := by
  obtain ⟨a | a, rfl⟩ := Quotient.exists_rep p
  · exact .inl ⟨a, rfl⟩
  · exact .inr ⟨a, rfl⟩

theorem Pasted.continuous_ι : Continuous (Pasted.ι hb) :=
  continuous_quotient_mk'.comp continuous_inl

theorem Pasted.continuous_δ : Continuous (Pasted.δ hb) :=
  continuous_quotient_mk'.comp continuous_inr

theorem Pasted.isOpen_iff {W : Set (Pasted hb)} :
    IsOpen W ↔ IsOpen (Pasted.ι hb ⁻¹' W) ∧ IsOpen (Pasted.δ hb ⁻¹' W) := by
  refine (isQuotientMap_quotient_mk' (s := pasteSetoid hb)).isOpen_preimage.symm.trans ?_
  rw [isOpen_sum_iff]
  rfl

instance [CompactSpace S] : CompactSpace (Pasted hb) :=
  inferInstanceAs (CompactSpace (Quotient (pasteSetoid hb)))

theorem Pasted.t2Space [CompactSpace S] [T2Space S] (hbc : ContinuousOn b (sphere (0 : ℂ) 1)) :
    T2Space (Pasted hb) := by
  have : CompactSpace DiscType := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  refine t2Space_quotient_of_isClosed (pasteSetoid hb) ?_
  let T : Set DiscType := Subtype.val ⁻¹' sphere (0 : ℂ) 1
  have hT : IsCompact T :=
    (isClosed_sphere.preimage continuous_subtype_val).isCompact
  have hbT : ContinuousOn (fun z : DiscType => (Sum.inl (b z) : S ⊕ DiscType)) T :=
    continuous_inl.comp_continuousOn (hbc.comp continuous_subtype_val.continuousOn fun _ h => h)
  have hG : IsCompact ((fun z : DiscType => ((Sum.inl (b z) : S ⊕ DiscType),
      (Sum.inr z : S ⊕ DiscType))) '' T) :=
    hT.image_of_continuousOn (hbT.prodMk continuous_inr.continuousOn)
  have hG' := hG.image continuous_swap
  have hrel : {p : (S ⊕ DiscType) × (S ⊕ DiscType) | (pasteSetoid hb) p.1 p.2} =
      diagonal _ ∪ ((fun z : DiscType => ((Sum.inl (b z) : S ⊕ DiscType),
      (Sum.inr z : S ⊕ DiscType))) '' T ∪
      Prod.swap '' ((fun z : DiscType => ((Sum.inl (b z) : S ⊕ DiscType),
      (Sum.inr z : S ⊕ DiscType))) '' T)) := by
    ext ⟨a, a'⟩
    constructor
    · rintro (h | ⟨z, hz, h1, h2⟩ | ⟨z, hz, h1, h2⟩)
      · exact .inl h
      · exact .inr (.inl ⟨z, hz, Prod.ext h1.symm h2.symm⟩)
      · exact .inr (.inr ⟨_, ⟨z, hz, rfl⟩, Prod.ext h1.symm h2.symm⟩)
    · rintro (h | ⟨z, hz, he⟩ | ⟨_, ⟨z, hz, rfl⟩, he⟩)
      · exact .inl h
      · simp only [Prod.mk.injEq] at he
        exact .inr (.inl ⟨z, hz, he.1.symm, he.2.symm⟩)
      · simp only [Prod.swap_prod_mk, Prod.mk.injEq] at he
        exact .inr (.inr ⟨z, hz, he.1.symm, he.2.symm⟩)
  rw [hrel]
  exact isClosed_diagonal.union (hG.isClosed.union hG'.isClosed)

/-- The map from the disc of `ℂ` to the pasted space, extended by a junk value. -/
noncomputable def Pasted.δ' (s₀ : S) : ℂ → Pasted hb := fun z =>
  open Classical in if h : z ∈ closedBall (0 : ℂ) 1 then Pasted.δ hb ⟨z, h⟩ else Pasted.ι hb s₀

omit [TopologicalSpace S] in
theorem Pasted.δ'_of_mem (s₀ : S) {z : ℂ} (h : z ∈ closedBall (0 : ℂ) 1) :
    Pasted.δ' hb s₀ z = Pasted.δ hb ⟨z, h⟩ := by
  simp [Pasted.δ', h]

theorem Pasted.continuousOn_δ' (s₀ : S) : ContinuousOn (Pasted.δ' hb s₀) (closedBall 0 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (closedBall (0 : ℂ) 1).domRestrict (Pasted.δ' hb s₀) = Pasted.δ hb :=
    funext fun z => Pasted.δ'_of_mem hb s₀ z.2
  rw [this]
  exact Pasted.continuous_δ hb

omit [TopologicalSpace S] in
theorem Pasted.injOn_δ' (s₀ : S) : InjOn (Pasted.δ' hb s₀) (closedBall 0 1) := by
  intro z hz w hw he
  rw [Pasted.δ'_of_mem hb s₀ hz, Pasted.δ'_of_mem hb s₀ hw, Pasted.δ_eq_δ] at he
  exact congrArg Subtype.val he

/-- A point of the open disc is an interior point of the pasted space. -/
theorem Pasted.isInteriorPoint_δ [CompactSpace S] [T2Space S]
    (hbc : ContinuousOn b (sphere (0 : ℂ) 1)) (s₀ : S) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    IsInteriorPoint (Pasted.δ' hb s₀ z) := by
  have := Pasted.t2Space hb hbc
  refine isInteriorPoint_of_injOn (isCompact_closedBall 0 1) (Pasted.continuousOn_δ' hb s₀)
    (Pasted.injOn_δ' hb s₀) ball_subset_closedBall isOpen_ball ?_ hz
  rw [Pasted.isOpen_iff]
  constructor
  · convert isOpen_empty
    rw [eq_empty_iff_forall_notMem]
    rintro s ⟨w, hw, he⟩
    rw [Pasted.δ'_of_mem hb s₀ (ball_subset_closedBall hw), eq_comm, Pasted.ι_eq_δ] at he
    have h1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp he.1
    have h2 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    linarith
  · have : Pasted.δ hb ⁻¹' (Pasted.δ' hb s₀ '' ball 0 1) = Subtype.val ⁻¹' ball (0 : ℂ) 1 := by
      ext w
      constructor
      · rintro ⟨v, hv, he⟩
        rw [Pasted.δ'_of_mem hb s₀ (ball_subset_closedBall hv), Pasted.δ_eq_δ] at he
        change w.1 ∈ ball (0 : ℂ) 1
        rw [← he]
        exact hv
      · intro hw
        exact ⟨w.1, hw, by rw [Pasted.δ'_of_mem hb s₀ w.2]⟩
    rw [this]
    exact isOpen_ball.preimage continuous_subtype_val

/-- The map from `S` to the pasted space is an open embedding off `C`. -/
theorem Pasted.isOpenEmbedding_compl [CompactSpace S] [T2Space S]
    (hbc : ContinuousOn b (sphere (0 : ℂ) 1)) :
    IsOpenEmbedding (fun s : ((b '' sphere (0 : ℂ) 1)ᶜ : Set S) => Pasted.ι hb s.1) := by
  have := Pasted.t2Space hb hbc
  have hCc : IsClosed (b '' sphere (0 : ℂ) 1) :=
    ((isCompact_sphere _ _).image_of_continuousOn hbc).isClosed
  have hemb : IsEmbedding (Pasted.ι hb) :=
    ((Pasted.continuous_ι hb).isClosedEmbedding
      fun _ _ h => (Pasted.ι_eq_ι hb).mp h).isEmbedding
  refine ⟨hemb.comp IsEmbedding.subtypeVal, ?_⟩
  have hsub : range (fun s : ((b '' sphere (0 : ℂ) 1)ᶜ : Set S) => Pasted.ι hb s.1) =
      Pasted.ι hb '' (b '' sphere (0 : ℂ) 1)ᶜ := by
    ext p
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  rw [hsub, Pasted.isOpen_iff]
  constructor
  · rw [preimage_image_eq _ fun _ _ h => (Pasted.ι_eq_ι hb).mp h]
    exact hCc.isOpen_compl
  · convert isOpen_empty
    rw [eq_empty_iff_forall_notMem]
    rintro z ⟨s, hs, he⟩
    obtain ⟨hz, rfl⟩ := (Pasted.ι_eq_δ hb).mp he
    exact hs ⟨z.1, hz, rfl⟩

private theorem horizontalScale_injective {ρ : ℝ} (hρ : ρ ≠ 0) :
    Function.Injective
      (fun z : ℂ => ((ρ * z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) := by
  intro z w h
  apply Complex.ext
  · have hz := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero] at hz
    exact mul_left_cancel₀ hρ hz
  · have hz := congrArg Complex.im h
    simpa using hz

private theorem isOpen_pasted_chart_rectangle
    (hbc : ContinuousOn b (sphere (0 : ℂ) 1)) {b' : S → ℂ}
    (hb'l : LeftInvOn b' b (sphere (0 : ℂ) 1))
    (hCbd : b '' sphere (0 : ℂ) 1 ⊆ bd S) {s : S}
    {U : Set S} {O : Set ℂ} {j : S → ℂ} {k : ℂ → S}
    (hU : IsOpen U) (hj : ContinuousOn j U) (hm : MapsTo j U (O ∩ halfPlane))
    (hk' : MapsTo k (O ∩ halfPlane) U) (hl : LeftInvOn k j U)
    (hr : LeftInvOn j k (O ∩ halfPlane))
    (hre0 : ∀ y ∈ U, y ∈ bd S → (j y).re = 0) {ρ y₀ : ℝ} (hρ : 0 < ρ) :
    let I₀ : Set ℝ := Icc (y₀ - ρ) (y₀ + ρ)
    let line : ℝ → ℂ := fun y => (y : ℂ) * Complex.I
    let u : ℝ → ℂ := fun y => b' (k (line y))
    let Rq : Set ℂ := Icc 0 ρ ×ℂ I₀
    let P : ℂ → ℂ := fun z => ((ρ * z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I
    let A : ℂ → Pasted hb := fun z => Pasted.ι hb (k (P z))
    let E : ℂ → ℂ := fun z => (((1 + z.re / 2 : ℝ) : ℂ)) * u z.im
    let B : ℂ → Pasted hb := fun z => Pasted.δ' hb s (E z)
    ∀ Ψ : ℂ → Pasted hb,
    let Rp : Set ℂ := Icc 0 1 ×ℂ I₀
    let Rn : Set ℂ := Icc (-1) 0 ×ℂ I₀
    let R : Set ℂ := Icc (-1) 1 ×ℂ I₀
    let V : Set ℂ := Ioo (-1) 1 ×ℂ Ioo (y₀ - ρ) (y₀ + ρ)
    Rq ⊆ O ∩ halfPlane → (∀ y ∈ I₀, line y ∈ Rq) →
    (∀ y ∈ I₀, u y ∈ sphere (0 : ℂ) 1 ∧ b (u y) = k (line y)) →
    (∀ z ∈ Rp, P z ∈ Rq) →
    (∀ z, z.im ∈ I₀ → z.re ∈ Icc (-1 : ℝ) 1 → ‖E z‖ = 1 + z.re / 2) →
    (∀ z ∈ Rn, E z ∈ closedBall (0 : ℂ) 1) →
    EqOn Ψ A Rp → EqOn Ψ B Rn →
    (∀ z ∈ R, z.re < 0 → ∀ t, Pasted.ι hb t ≠ B z) →
    IsOpen (Ψ '' V) := by
  intro I₀ line u Rq P A E B Ψ Rp Rn R V hRq hline hu hPR hEnorm hEball hΨp hΨn hne
  have hPre : ∀ z, (P z).re = ρ * z.re := fun z => by simp [P]
  have hPim : ∀ z, (P z).im = z.im := fun z => by simp [P]
  have hVR : V ⊆ R := fun z hz => ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩
  have hmemR : ∀ z ∈ R, 0 ≤ z.re → z ∈ Rp := fun z hz h => ⟨⟨h, hz.1.2⟩, hz.2⟩
  have hmemR' : ∀ z ∈ R, z.re < 0 → z ∈ Rn := fun z hz h => ⟨⟨hz.1.1, h.le⟩, hz.2⟩
  let T : Set ℂ := Ioo (-ρ) ρ ×ℂ Ioo (y₀ - ρ) (y₀ + ρ)
  have hTo : IsOpen T :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  let Ω : Set S := U ∩ j ⁻¹' T
  have hΩ : IsOpen Ω := hj.isOpen_inter_preimage hU hTo
  have hPT : ∀ z ∈ V, 0 ≤ z.re → P z ∈ T := fun z hz h => by
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · rw [hPre]
      exact ⟨by nlinarith, by nlinarith [hz.1.2]⟩
    · rw [hPim]
      exact hz.2
  have hopenι : Pasted.ι hb ⁻¹' (Ψ '' V) = Ω := by
    ext t
    constructor
    · rintro ⟨z, hz, he⟩
      by_cases h : 0 ≤ z.re
      · rw [hΨp (hmemR z (hVR hz) h)] at he
        have h1 : k (P z) = t := (Pasted.ι_eq_ι hb).mp he
        have h2 := hPR z (hmemR z (hVR hz) h)
        rw [← h1]
        refine ⟨hk' (hRq h2), ?_⟩
        change j (k (P z)) ∈ T
        rw [hr (hRq h2)]
        exact hPT z hz h
      · have h1 := hmemR' z (hVR hz) (not_le.mp h)
        rw [hΨn h1] at he
        exact absurd he.symm (hne z (hVR hz) (not_le.mp h) _)
    · rintro ⟨h1, h2⟩
      have h3 : j t ∈ T := h2
      let z : ℂ := (((j t).re / ρ : ℝ) : ℂ) + ((j t).im : ℂ) * Complex.I
      have hzre : z.re = (j t).re / ρ := by simp [z]
      have hzim : z.im = (j t).im := by simp [z]
      have hre0' : 0 ≤ z.re := by
        rw [hzre]
        exact div_nonneg (hm h1).2 hρ.le
      have hzV : z ∈ V := by
        refine Complex.mem_reProdIm.mpr ⟨⟨by linarith, ?_⟩, ?_⟩
        · rw [hzre, div_lt_one hρ]
          exact h3.1.2
        · rw [hzim]
          exact h3.2
      refine ⟨z, hzV, ?_⟩
      rw [hΨp (hmemR z (hVR hzV) hre0')]
      have hPz : P z = j t := by
        apply Complex.ext
        · rw [hPre, hzre]
          field_simp
        · rw [hPim, hzim]
      change Pasted.ι hb (k (P z)) = _
      rw [hPz, hl h1]
  let W₀ : Set ℂ := {w | 1 / 2 < ‖w‖}
  have hW₀ : IsOpen W₀ := isOpen_lt continuous_const continuous_norm
  let dir : ℂ → ℂ := fun w => ((‖w‖⁻¹ : ℝ) : ℂ) * w
  have hdir : ∀ w ∈ W₀, dir w ∈ sphere (0 : ℂ) 1 := fun w hw => by
    have h0 : ‖w‖ ≠ 0 := by
      have : (1 / 2 : ℝ) < ‖w‖ := hw
      linarith
    rw [mem_sphere_zero_iff_norm]
    simp only [dir, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_nonneg, abs_of_nonneg,
      inv_nonneg]
    field_simp
  have hdirc : ContinuousOn dir W₀ := by
    refine ContinuousOn.mul ?_ continuousOn_id
    refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.inv₀ (by fun_prop) ?_)
    intro w hw
    have : (1 / 2 : ℝ) < ‖w‖ := hw
    linarith
  have hgc : ContinuousOn (b ∘ dir) W₀ := hbc.comp hdirc hdir
  have hopenδ : Pasted.δ hb ⁻¹' (Ψ '' V) = Subtype.val ⁻¹' (W₀ ∩ (b ∘ dir) ⁻¹' Ω) := by
    ext w
    constructor
    · rintro ⟨z, hz, he⟩
      by_cases h : 0 ≤ z.re
      · rw [hΨp (hmemR z (hVR hz) h)] at he
        obtain ⟨hw, hw2⟩ := (Pasted.ι_eq_δ hb).mp he
        have hn : ‖w.1‖ = 1 := mem_sphere_zero_iff_norm.mp hw
        have hd : dir w.1 = w.1 := by simp [dir, hn]
        have hw0 : w.1 ∈ W₀ := by
          change (1 / 2 : ℝ) < ‖w.1‖
          rw [hn]
          norm_num
        refine ⟨hw0, ?_⟩
        change b (dir w.1) ∈ Ω
        rw [hd, ← hw2]
        have h2 := hPR z (hmemR z (hVR hz) h)
        refine ⟨hk' (hRq h2), ?_⟩
        change j (k (P z)) ∈ T
        rw [hr (hRq h2)]
        exact hPT z hz h
      · have h1 := hmemR' z (hVR hz) (not_le.mp h)
        rw [hΨn h1] at he
        have he' : Pasted.δ' hb s (E z) = Pasted.δ hb w := he
        rw [Pasted.δ'_of_mem hb s (hEball z h1), Pasted.δ_eq_δ] at he'
        have hEw : E z = w.1 := congrArg Subtype.val he'
        have hn : ‖w.1‖ = 1 + z.re / 2 := by
          rw [← hEw]
          exact hEnorm z h1.2 (hVR hz).1
        have hd : dir w.1 = u z.im := by
          have h3 : (1 + z.re / 2 : ℝ) ≠ 0 := by linarith [(hVR hz).1.1]
          change ((‖w.1‖⁻¹ : ℝ) : ℂ) * w.1 = u z.im
          rw [hn, ← hEw]
          simp only [E]
          rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ h3]
          simp
        have hw0 : w.1 ∈ W₀ := by
          change (1 / 2 : ℝ) < ‖w.1‖
          rw [hn]
          linarith [hz.1.1]
        refine ⟨hw0, ?_⟩
        change b (dir w.1) ∈ Ω
        rw [hd, (hu _ h1.2).2]
        refine ⟨hk' (hRq (hline _ h1.2)), ?_⟩
        change j (k (line z.im)) ∈ T
        rw [hr (hRq (hline _ h1.2))]
        refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
        · simp [line, hρ]
        · simpa [line] using hz.2
    · rintro ⟨hw0, hw1, hw2⟩
      have hw0' : (1 / 2 : ℝ) < ‖w.1‖ := hw0
      have hw1' : b (dir w.1) ∈ U := hw1
      have hbd : b (dir w.1) ∈ bd S := hCbd ⟨_, hdir _ hw0, rfl⟩
      have hre := hre0 _ hw1' hbd
      have hT' : j (b (dir w.1)) ∈ T := hw2
      set y := (j (b (dir w.1))).im with hy
      have hyI : y ∈ Ioo (y₀ - ρ) (y₀ + ρ) := hT'.2
      have hyI' : y ∈ I₀ := Ioo_subset_Icc_self hyI
      have hline' : line y = j (b (dir w.1)) := by
        apply Complex.ext <;> simp [line, hre, hy]
      have hkb : k (line y) = b (dir w.1) := by
        rw [hline', hl hw1']
      have huy : u y = dir w.1 := by
        change b' (k (line y)) = _
        rw [hkb, hb'l (hdir _ hw0)]
      have hnle : ‖w.1‖ ≤ 1 := mem_closedBall_zero_iff.mp w.2
      let z : ℂ := ((2 * (‖w.1‖ - 1) : ℝ) : ℂ) + (y : ℂ) * Complex.I
      have hzre : z.re = 2 * (‖w.1‖ - 1) := by simp [z]
      have hzim : z.im = y := by simp [z]
      have hzV : z ∈ V := by
        refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
        · rw [hzre]
          exact ⟨by linarith, by linarith⟩
        · rw [hzim]
          exact hyI
      refine ⟨z, hzV, ?_⟩
      have hEz : E z = w.1 := by
        have h6 : (1 + z.re / 2 : ℝ) = ‖w.1‖ := by
          rw [hzre]
          ring
        have h7 : (‖w.1‖ : ℝ) ≠ 0 := by linarith
        simp only [E, h6, hzim, huy, dir]
        rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h7]
        simp
      have h8 : z ∈ Rn := ⟨⟨(hVR hzV).1.1, by rw [hzre]; linarith⟩, (hVR hzV).2⟩
      rw [hΨn h8]
      change Pasted.δ' hb s (E z) = _
      rw [Pasted.δ'_of_mem hb s (hEball z h8)]
      congr 1
      exact Subtype.ext hEz
  have hopen : IsOpen (Ψ '' V) := by
    rw [Pasted.isOpen_iff, hopenι, hopenδ]
    refine ⟨hΩ, IsOpen.preimage continuous_subtype_val ?_⟩
    exact hgc.isOpen_inter_preimage hW₀ hΩ
  exact hopen

/-- A point of the cuff is an interior point of the pasted space: the half rectangle of a half plane
chart pastes to a half rectangle of the disc in polar coordinates. -/
theorem Pasted.isInteriorPoint_ι [CompactSpace S] [T2Space S]
    (hbc : ContinuousOn b (sphere (0 : ℂ) 1)) {b' : S → ℂ}
    (hb'c : ContinuousOn b' (b '' sphere (0 : ℂ) 1))
    (hb'l : LeftInvOn b' b (sphere (0 : ℂ) 1))
    (hC : b '' sphere (0 : ℂ) 1 ∈ componentsIn (bd S)) (hman : ∀ x : S, IsManifoldPoint x)
    {s : S} (hs : s ∈ b '' sphere (0 : ℂ) 1) : IsInteriorPoint (Pasted.ι hb s) := by
  have := Pasted.t2Space hb hbc
  set C := b '' sphere (0 : ℂ) 1 with hCdef
  have hCbd : C ⊆ bd S := by
    obtain ⟨c, hc, hce⟩ := hC
    rw [← hce]
    exact connectedComponentIn_subset _ _
  have hCcomp : C = connectedComponentIn (bd S) s := by
    obtain ⟨c, hc, hce⟩ := hC
    rw [← hce] at hs ⊢
    exact connectedComponentIn_eq hs
  obtain ⟨U, O, j, k, hU, hO, hsU, hj, hk, hm, hk', hl, hr⟩ := (hman s).exists_chart
  have hre0 : ∀ y ∈ U, y ∈ bd S → (j y).re = 0 := fun y hy hyb =>
    le_antisymm (not_lt.mp fun h => hyb (isInteriorPoint_of_chart hU hO hj hk hm hk' hl hr hy h))
      (hm hy).2
  have hjs : j s = ((j s).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre0 s hsU (hCbd hs)]
  set y₀ := (j s).im with hy₀
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.mp hO _ (hm hsU).1
  obtain ⟨ρ, hρ, hρρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ < ρ' := ⟨ρ' / 3, by positivity, by linarith⟩
  -- the half rectangle in the chart
  let Rq : Set ℂ := Icc 0 ρ ×ℂ Icc (y₀ - ρ) (y₀ + ρ)
  have hRq : Rq ⊆ O ∩ halfPlane := by
    rintro z ⟨h1, h2⟩
    refine ⟨hball ?_, h1.1⟩
    rw [mem_ball, dist_eq_norm]
    have h3 : (z - j s).re = z.re := by simp [hre0 s hsU (hCbd hs)]
    have h4 : (z - j s).im = z.im - y₀ := by simp [hy₀]
    calc ‖z - j s‖ ≤ |(z - j s).re| + |(z - j s).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ ρ + ρ := by
        rw [h3, h4, abs_of_nonneg h1.1]
        exact add_le_add h1.2 (abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩)
      _ < ρ' := by linarith
  let line : ℝ → ℂ := fun y => (y : ℂ) * Complex.I
  have hline : ∀ y ∈ Icc (y₀ - ρ) (y₀ + ρ), line y ∈ Rq := fun y hy => by
    refine ⟨?_, ?_⟩ <;> simp [line, hρ.le, hy.1, hy.2]
  -- the side of the rectangle lies in the cuff
  have hside : k '' (line '' Icc (y₀ - ρ) (y₀ + ρ)) ⊆ C := by
    rw [hCcomp]
    have hpre : IsPreconnected (k '' (line '' Icc (y₀ - ρ) (y₀ + ρ))) := by
      refine (isPreconnected_Icc.image line (by fun_prop)).image k ?_
      refine hk.mono ?_
      rintro _ ⟨y, hy, rfl⟩
      exact hRq (hline y hy)
    refine hpre.subset_connectedComponentIn ⟨line y₀, ⟨y₀, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩ ?_
    · have : line y₀ = j s := hjs.symm
      rw [this, hl hsU]
    · rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ hint
      refine not_isInteriorPoint_of_chart (O := O) hU hj hm hl.injOn (hk' (hRq
        (hline y hy))) ?_ hint
      rw [hr (hRq (hline y hy))]
      simp [line]
  let I₀ : Set ℝ := Icc (y₀ - ρ) (y₀ + ρ)
  let u : ℝ → ℂ := fun y => b' (k (line y))
  have hkC : ∀ y ∈ I₀, k (line y) ∈ C := fun y hy => hside ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  have hu : ∀ y ∈ I₀, u y ∈ sphere (0 : ℂ) 1 ∧ b (u y) = k (line y) := fun y hy => by
    obtain ⟨z, hz, he⟩ := hkC y hy
    have : u y = z := by
      change b' (k (line y)) = z
      rw [← he, hb'l hz]
    rw [this]
    exact ⟨hz, he⟩
  have hkl : ContinuousOn (fun y => k (line y)) I₀ :=
    hk.comp (by fun_prop) fun y hy => hRq (hline y hy)
  have huc : ContinuousOn u I₀ := hb'c.comp hkl hkC
  have hunorm : ∀ y ∈ I₀, ‖u y‖ = 1 := fun y hy => mem_sphere_zero_iff_norm.mp (hu y hy).1
  let P : ℂ → ℂ := fun z => ((ρ * z.re : ℝ) : ℂ) + (z.im : ℂ) * Complex.I
  have hPre : ∀ z, (P z).re = ρ * z.re := fun z => by simp [P]
  have hPim : ∀ z, (P z).im = z.im := fun z => by simp [P]
  have hPc : Continuous P := by fun_prop
  let A : ℂ → Pasted hb := fun z => Pasted.ι hb (k (P z))
  let E : ℂ → ℂ := fun z => (((1 + z.re / 2 : ℝ) : ℂ)) * u z.im
  let B : ℂ → Pasted hb := fun z => Pasted.δ' hb s (E z)
  let Ψ : ℂ → Pasted hb := fun z => if 0 ≤ z.re then A z else B z
  let Rp : Set ℂ := Icc 0 1 ×ℂ I₀
  let Rn : Set ℂ := Icc (-1) 0 ×ℂ I₀
  let R : Set ℂ := Icc (-1) 1 ×ℂ I₀
  have hRcover : R = Rp ∪ Rn := by
    ext z
    simp only [R, Rp, Rn, mem_union, Complex.mem_reProdIm, mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      rcases le_total 0 z.re with h | h
      · exact .inl ⟨⟨h, h2⟩, h3⟩
      · exact .inr ⟨⟨h1, h⟩, h3⟩
    · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
      · exact ⟨⟨by linarith, h2⟩, h3⟩
      · exact ⟨⟨h1, by linarith⟩, h3⟩
  have hPR : ∀ z ∈ Rp, P z ∈ Rq := fun z hz => by
    obtain ⟨h1, h2⟩ := hz
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · rw [hPre]
      exact ⟨mul_nonneg hρ.le h1.1, by nlinarith [h1.2]⟩
    · rw [hPim]
      exact h2
  have hEnorm : ∀ z, z.im ∈ I₀ → z.re ∈ Icc (-1 : ℝ) 1 → ‖E z‖ = 1 + z.re / 2 := fun z h1 h2 => by
    simp only [E, norm_mul, Complex.norm_real, hunorm _ h1, mul_one, Real.norm_eq_abs]
    exact abs_of_nonneg (by linarith [h2.1])
  have hEball : ∀ z ∈ Rn, E z ∈ closedBall (0 : ℂ) 1 := fun z hz => by
    obtain ⟨h1, h2⟩ := hz
    rw [mem_closedBall_zero_iff, hEnorm z h2 ⟨h1.1, by linarith [h1.2]⟩]
    linarith [h1.2]
  have hAB : ∀ z ∈ Rn, z.re = 0 → A z = B z := fun z hz h0 => by
    have hP : P z = line z.im := by simp [P, h0, line]
    have hE : E z = u z.im := by simp [E, h0]
    change Pasted.ι hb (k (P z)) = Pasted.δ' hb s (E z)
    rw [Pasted.δ'_of_mem hb s (hEball z hz), Pasted.ι_eq_δ, hP]
    have h2 := hu z.im hz.2
    refine ⟨?_, ?_⟩
    · change E z ∈ _
      rw [hE]
      exact h2.1
    · change k (line z.im) = b (E z)
      rw [hE, h2.2]
  have hΨp : EqOn Ψ A Rp := fun z hz => ite_eq_left hz.1.1
  have hΨn : EqOn Ψ B Rn := fun z hz => by
    change (if 0 ≤ z.re then A z else B z) = B z
    split_ifs with h
    · exact hAB z hz (le_antisymm hz.1.2 h)
    · rfl
  have hAc : ContinuousOn A Rp :=
    (Pasted.continuous_ι hb).comp_continuousOn
      (hk.comp hPc.continuousOn fun z hz => hRq (hPR z hz))
  have hEc : ContinuousOn E Rn := by
    refine ContinuousOn.mul (by fun_prop) ?_
    exact huc.comp (by fun_prop) fun z hz => hz.2
  have hBc : ContinuousOn B Rn := (Pasted.continuousOn_δ' hb s).comp hEc hEball
  have hclosedp : IsClosed Rp :=
    (isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Icc.preimage
      Complex.continuous_im)
  have hclosedn : IsClosed Rn :=
    (isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Icc.preimage
      Complex.continuous_im)
  have hΨc : ContinuousOn Ψ R := by
    rw [hRcover]
    exact (hAc.congr hΨp).union_of_isClosed (hBc.congr hΨn) hclosedp hclosedn
  have hRcomp : IsCompact R := isCompact_Icc.reProdIm isCompact_Icc
  have hmemR : ∀ z ∈ R, 0 ≤ z.re → z ∈ Rp := fun z hz h => ⟨⟨h, hz.1.2⟩, hz.2⟩
  have hmemR' : ∀ z ∈ R, z.re < 0 → z ∈ Rn := fun z hz h => ⟨⟨hz.1.1, h.le⟩, hz.2⟩
  have hPeq : Function.Injective P := horizontalScale_injective hρ.ne'
  have hk_inj : ∀ z ∈ Rq, ∀ w ∈ Rq, k z = k w → z = w := fun z hz w hw h => by
    rw [← hr (hRq hz), h, hr (hRq hw)]
  -- a point of the disc side with `re < 0` is not in `S`
  have hne : ∀ z ∈ R, z.re < 0 → ∀ t, Pasted.ι hb t ≠ B z := fun z hz h t he => by
    show False
    have hm := hEball z (hmemR' z hz h)
    have he' : Pasted.ι hb t = Pasted.δ' hb s (E z) := he
    rw [Pasted.δ'_of_mem hb s hm, Pasted.ι_eq_δ] at he'
    have h1 : ‖E z‖ = 1 := mem_sphere_zero_iff_norm.mp he'.1
    rw [hEnorm z hz.2 ⟨hz.1.1, hz.1.2⟩] at h1
    linarith
  have hinj : InjOn Ψ R := by
    intro z hz w hw he
    by_cases h1 : 0 ≤ z.re <;> by_cases h2 : 0 ≤ w.re
    · rw [hΨp (hmemR z hz h1), hΨp (hmemR w hw h2)] at he
      exact hPeq (hk_inj _ (hPR _ (hmemR z hz h1)) _ (hPR _ (hmemR w hw h2))
        ((Pasted.ι_eq_ι hb).mp he))
    · rw [hΨp (hmemR z hz h1), hΨn (hmemR' w hw (not_le.mp h2))] at he
      exact absurd he (hne w hw (not_le.mp h2) _)
    · rw [hΨn (hmemR' z hz (not_le.mp h1)), hΨp (hmemR w hw h2)] at he
      exact absurd he.symm (hne z hz (not_le.mp h1) _)
    · have hz' := hmemR' z hz (not_le.mp h1)
      have hw' := hmemR' w hw (not_le.mp h2)
      rw [hΨn hz', hΨn hw'] at he
      have hEE : E z = E w := Pasted.injOn_δ' hb s (hEball z hz') (hEball w hw') he
      have hn := congrArg norm hEE
      rw [hEnorm z hz.2 hz.1, hEnorm w hw.2 hw.1] at hn
      have hre : z.re = w.re := by linarith
      have huu : u z.im = u w.im := by
        have h3 : ((1 + z.re / 2 : ℝ) : ℂ) ≠ 0 := by
          have : (1 + z.re / 2 : ℝ) ≠ 0 := by linarith [hz.1.1]
          exact_mod_cast this
        have h4 : ((1 + z.re / 2 : ℝ) : ℂ) * u z.im = ((1 + z.re / 2 : ℝ) : ℂ) * u w.im := by
          have : E w = ((1 + z.re / 2 : ℝ) : ℂ) * u w.im := by simp only [E, hre]
          rw [← this]
          exact hEE
        exact mul_left_cancel₀ h3 h4
      have hk2 : k (line z.im) = k (line w.im) := by
        rw [← (hu _ hz.2).2, ← (hu _ hw.2).2, huu]
      have := hk_inj _ (hline _ hz.2) _ (hline _ hw.2) hk2
      have him : z.im = w.im := by
        have h5 := congrArg Complex.im this
        simpa [line] using h5
      exact Complex.ext hre him
  -- the open rectangle and its image
  let V : Set ℂ := Ioo (-1) 1 ×ℂ Ioo (y₀ - ρ) (y₀ + ρ)
  have hVo : IsOpen V :=
    (isOpen_Ioo.preimage Complex.continuous_re).inter (isOpen_Ioo.preimage Complex.continuous_im)
  have hVR : V ⊆ R := fun z hz => ⟨Ioo_subset_Icc_self hz.1, Ioo_subset_Icc_self hz.2⟩
  have hopen : IsOpen (Ψ '' V) :=
    isOpen_pasted_chart_rectangle hb hbc hb'l hCbd hU hj hm hk' hl hr hre0 hρ
      Ψ hRq hline hu hPR hEnorm hEball hΨp hΨn hne
  have hcV : line y₀ ∈ V := by
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩ <;> simp [line, hρ]
  have hval : Ψ (line y₀) = Pasted.ι hb s := by
    have h0 : ∀ z : ℂ, z = line y₀ → 0 ≤ z.re := fun z hz => by simp [hz, line]
    rw [hΨp (hmemR _ (hVR hcV) (h0 _ rfl))]
    change Pasted.ι hb (k (P (line y₀))) = _
    have : P (line y₀) = j s := by
      rw [hjs]
      simp [P, line]
    rw [this, hl hsU]
  rw [← hval]
  exact isInteriorPoint_of_injOn hRcomp hΨc hinj hVR hVo hopen hcV

/-- **Pasting a disc onto a cuff.** The route is that of the module docstring. -/
theorem paste_disc : PasteDiscStatement.{u} := by
  intro S _ C hS hC
  obtain ⟨hcomp, ht2, hman⟩ := hS
  obtain ⟨-, -, hOarc⟩ := cuff_statement.{u} S ⟨hcomp, ht2, hman⟩
  obtain ⟨φ⟩ := hOarc C hC
  obtain ⟨o⟩ := oArc_sphere
  have : Nonempty S := by
    obtain ⟨c, hc, -⟩ := hC
    exact ⟨c⟩
  obtain ⟨b, b', hbc, hb'c, hbm, hb'm, hbl, hbr⟩ := exists_functions_of_homeomorph (o.symm.trans φ)
  have hbi : InjOn b (sphere (0 : ℂ) 1) := hbl.injOn
  have hCeq : b '' sphere (0 : ℂ) 1 = C := by
    refine subset_antisymm (image_subset_iff.mpr hbm) fun c hc => ⟨b' c, hb'm hc, hbr hc⟩
  subst hCeq
  have ht2' := Pasted.t2Space hbi hbc
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hemb : IsClosedEmbedding (Pasted.ι hbi) :=
    (Pasted.continuous_ι hbi).isClosedEmbedding fun _ _ h => (Pasted.ι_eq_ι hbi).mp h
  obtain ⟨d', hd'c, hd'l⟩ := exists_inv_of_compactOn (isCompact_closedBall (0 : ℂ) 1)
    (Pasted.continuousOn_δ' hbi s₀) (Pasted.injOn_δ' hbi s₀)
  obtain ⟨hdisc, hbdΔ⟩ := isClosedDisc_closedBall.1.image (Pasted.continuousOn_δ' hbi s₀) hd'c hd'l
  have hsph : Pasted.δ' hbi s₀ '' sphere (0 : ℂ) 1 = Pasted.ι hbi '' (b '' sphere (0 : ℂ) 1) := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨b z, ⟨z, hz, rfl⟩, ?_⟩
      rw [Pasted.δ'_of_mem hbi s₀ (sphere_subset_closedBall hz)]
      exact (Pasted.ι_eq_δ hbi).mpr ⟨hz, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨z, hz, ?_⟩
      rw [Pasted.δ'_of_mem hbi s₀ (sphere_subset_closedBall hz)]
      exact ((Pasted.ι_eq_δ hbi).mpr ⟨hz, rfl⟩).symm
  rw [isClosedDisc_closedBall.2, hsph] at hbdΔ
  have hint : ∀ s ∈ b '' sphere (0 : ℂ) 1, IsInteriorPoint (Pasted.ι hbi s) := fun s hs =>
    Pasted.isInteriorPoint_ι hbi hbc hb'c hbl hC hman hs
  have hopen := Pasted.isOpenEmbedding_compl hbi hbc
  have hCo : IsOpen (b '' sphere (0 : ℂ) 1)ᶜ :=
    ((isCompact_sphere _ _).image_of_continuousOn hbc).isClosed.isOpen_compl
  have hcover : ∀ p : Pasted hbi, (∃ s, p = Pasted.ι hbi s) ∨ ∃ z ∈ ball (0 : ℂ) 1,
      p = Pasted.δ' hbi s₀ z := fun p => by
    obtain ⟨s, rfl⟩ | ⟨z, rfl⟩ := Pasted.surj hbi p
    · exact .inl ⟨s, rfl⟩
    · by_cases hz : z.1 ∈ sphere (0 : ℂ) 1
      · exact .inl ⟨b z, (Pasted.ι_eq_δ hbi).mpr ⟨hz, rfl⟩ |>.symm⟩
      · refine .inr ⟨z.1, ?_, (Pasted.δ'_of_mem hbi s₀ z.2).symm⟩
        have h1 : ‖z.1‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2
        have h2 : ‖z.1‖ ≠ 1 := fun h => hz (mem_sphere_zero_iff_norm.mpr h)
        exact mem_ball_zero_iff.mpr (lt_of_le_of_ne h1 h2)
  refine ⟨Pasted hbi, inferInstance, Pasted.ι hbi, Pasted.δ' hbi s₀ '' closedBall 0 1, ?_, hemb,
    hdisc, ?_, ?_, hbdΔ, ?_⟩
  · refine ⟨inferInstance, ht2', fun p => ?_⟩
    obtain ⟨s, rfl⟩ | ⟨z, hz, rfl⟩ := hcover p
    · by_cases hs : s ∈ b '' sphere (0 : ℂ) 1
      · exact (hint s hs).isManifoldPoint
      · exact (isManifoldPoint_of_isOpenEmbedding hopen (x := ⟨s, hs⟩)
          ((isManifoldPoint_iff_of_isOpenEmbedding hCo.isOpenEmbedding_subtypeVal).mp (hman s)))
    · exact (Pasted.isInteriorPoint_δ hbi hbc s₀ hz).isManifoldPoint
  · rw [eq_univ_iff_forall]
    intro p
    obtain ⟨s, rfl⟩ | ⟨z, hz, rfl⟩ := hcover p
    · exact .inl ⟨s, rfl⟩
    · exact .inr ⟨z, ball_subset_closedBall hz, rfl⟩
  · ext p
    constructor
    · rintro ⟨⟨s, rfl⟩, z, hz, he⟩
      rw [Pasted.δ'_of_mem hbi s₀ hz, eq_comm, Pasted.ι_eq_δ] at he
      exact ⟨s, ⟨z, he.1, he.2.symm⟩, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      refine ⟨⟨s, rfl⟩, ?_⟩
      have hm : Pasted.ι hbi s ∈ Pasted.δ' hbi s₀ '' sphere (0 : ℂ) 1 := by
        rw [hsph]
        exact mem_image_of_mem _ hs
      obtain ⟨z, hz, he⟩ := hm
      exact ⟨z, sphere_subset_closedBall hz, he⟩
  · ext p
    constructor
    · intro hp
      obtain ⟨s, rfl⟩ | ⟨z, hz, rfl⟩ := hcover p
      · refine ⟨s, ⟨fun hs => ?_, fun hs => hp (hint s hs)⟩, rfl⟩
        have hsC : s ∉ b '' sphere (0 : ℂ) 1 := fun h => hp (hint s h)
        exact hp (isInteriorPoint_of_isOpenEmbedding hopen (x := ⟨s, hsC⟩)
          ((isInteriorPoint_iff_of_isOpenEmbedding hCo.isOpenEmbedding_subtypeVal).mp
            hs))
      · exact absurd (Pasted.isInteriorPoint_δ hbi hbc s₀ hz) hp
    · rintro ⟨s, ⟨hs, hsC⟩, rfl⟩ hint'
      refine hs ?_
      have h1 := (isInteriorPoint_iff_of_isOpenEmbedding hopen (x := ⟨s, hsC⟩)).mp hint'
      exact isInteriorPoint_of_isOpenEmbedding hCo.isOpenEmbedding_subtypeVal h1

end GraphMinor.Surface
