/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Perimeter
public import LeanPool.GraphMinor.GM19.RadialExists

/-!
# Two cappings of a surface are homeomorphic

A homeomorphism between the boundaries of two closed discs extends to the discs. So the identity of
`Σ` extends over
the pasted discs of any two cappings. The paper speaks of "the" surface `Σ̂` (Section 2, page 327),
and this is why.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface

variable {A B : Type} [TopologicalSpace A] [TopologicalSpace B]

/-- A homeomorphism of the boundaries of two closed discs extends to the discs. -/
theorem exists_disc_ext {D₁ : Set A} {D₂ : Set B} (h₁ : IsClosedDisc D₁) (h₂ : IsClosedDisc D₂)
    (e : discBd D₁ ≃ₜ discBd D₂) :
    ∃ G : A → B, ContinuousOn G D₁ ∧ BijOn G D₁ D₂ ∧ ∀ x : discBd D₁, G x.1 = (e x).1 := by
  classical
  obtain ⟨p₁, g₁, c₁⟩ := h₁.exists_isChart
  obtain ⟨p₂, g₂, c₂⟩ := h₂.exists_isChart
  have hs₁ : ∀ {z : ℂ}, z ∈ sphere (0 : ℂ) 1 → g₁ z ∈ discBd D₁ := fun hz ↦ c₁.g_sphere ▸
    mem_image_of_mem g₁ hz
  have hs₂ : ∀ {z : ℂ}, z ∈ sphere (0 : ℂ) 1 → g₂ z ∈ discBd D₂ := fun hz ↦ c₂.g_sphere ▸
    mem_image_of_mem g₂ hz
  have hsb₁ : ∀ {x}, x ∈ discBd D₁ → p₁ x ∈ sphere (0 : ℂ) 1 := fun hx ↦ c₁.bd ▸ mem_image_of_mem
    p₁ hx
  have hsb₂ : ∀ {x}, x ∈ discBd D₂ → p₂ x ∈ sphere (0 : ℂ) 1 := fun hx ↦ c₂.bd ▸ mem_image_of_mem
    p₂ hx
  have hsubb₁ : discBd D₁ ⊆ D₁ := discBd_subset _
  have hsubb₂ : discBd D₂ ⊆ D₂ := discBd_subset _
  let E : ℂ → ℂ := fun z ↦ if hz : z ∈ sphere (0 : ℂ) 1 then p₂ (e ⟨g₁ z, hs₁ hz⟩).1 else 0
  let E' : ℂ → ℂ := fun z ↦ if hz : z ∈ sphere (0 : ℂ) 1 then p₁ (e.symm ⟨g₂ z, hs₂ hz⟩).1 else 0
  have hE : ∀ {z} (hz : z ∈ sphere (0 : ℂ) 1), E z = p₂ (e ⟨g₁ z, hs₁ hz⟩).1
    := fun hz ↦ dite_eq_left hz
  have hE' : ∀ {z} (hz : z ∈ sphere (0 : ℂ) 1), E' z = p₁ (e.symm ⟨g₂ z, hs₂ hz⟩).1
    := fun hz ↦ dite_eq_left hz
  have hEs : ∀ {z}, z ∈ sphere (0 : ℂ) 1 → E z ∈ sphere (0 : ℂ) 1 := fun hz ↦ by
    rw [hE hz]
    exact hsb₂ (e _).2
  have hEs' : ∀ {z}, z ∈ sphere (0 : ℂ) 1 → E' z ∈ sphere (0 : ℂ) 1 := fun hz ↦ by
    rw [hE' hz]
    exact hsb₁ (e.symm _).2
  have hsph : sphere (0 : ℂ) 1 ⊆ closedBall 0 1 := sphere_subset_closedBall
  have hm : BdMatch (sphere (0 : ℂ) 1) (sphere (0 : ℂ) 1) E E' := by
    refine ⟨fun z hz ↦ hEs hz, fun z hz ↦ hEs' hz, fun z hz ↦ ?_, fun z hz ↦ ?_, ?_, ?_⟩
    · rw [hE' (hEs hz)]
      have : (⟨g₂ (E z), hs₂ (hEs hz)⟩ : discBd D₂) = e ⟨g₁ z, hs₁ hz⟩ := by
        apply Subtype.ext
        change g₂ (E z) = _
        rw [hE hz]
        exact c₂.gh (hsubb₂ (e _).2)
      rw [this, e.symm_apply_apply]
      exact c₁.hg (hsph hz)
    · rw [hE (hEs' hz)]
      have : (⟨g₁ (E' z), hs₁ (hEs' hz)⟩ : discBd D₁) = e.symm ⟨g₂ z, hs₂ hz⟩ := by
        apply Subtype.ext
        change g₁ (E' z) = _
        rw [hE' hz]
        exact c₁.gh (hsubb₁ (e.symm _).2)
      rw [this, e.apply_symm_apply]
      exact c₂.hg (hsph hz)
    · rw [continuousOn_iff_continuous_domRestrict]
      have h₃ : Continuous fun z : sphere (0 : ℂ) 1 ↦ (⟨g₁ z.1, hs₁ z.2⟩ : discBd D₁) :=
        ((c₁.gc.mono hsph).comp_continuous continuous_subtype_val fun z ↦ z.2).subtype_mk _
      have h₄ : Continuous fun z : sphere (0 : ℂ) 1 ↦ (e ⟨g₁ z.1, hs₁ z.2⟩).1 :=
        continuous_subtype_val.comp (e.continuous.comp h₃)
      have h₅ : Continuous fun z : sphere (0 : ℂ) 1 ↦ p₂ (e ⟨g₁ z.1, hs₁ z.2⟩).1 :=
        (c₂.hc.mono hsubb₂).comp_continuous h₄ fun z ↦ (e _).2
      exact h₅.congr fun z ↦ (hE z.2).symm
    · rw [continuousOn_iff_continuous_domRestrict]
      have h₃ : Continuous fun z : sphere (0 : ℂ) 1 ↦ (⟨g₂ z.1, hs₂ z.2⟩ : discBd D₂) :=
        ((c₂.gc.mono hsph).comp_continuous continuous_subtype_val fun z ↦ z.2).subtype_mk _
      have h₄ : Continuous fun z : sphere (0 : ℂ) 1 ↦ (e.symm ⟨g₂ z.1, hs₂ z.2⟩).1 :=
        continuous_subtype_val.comp (e.symm.continuous.comp h₃)
      have h₅ : Continuous fun z : sphere (0 : ℂ) 1 ↦ p₁ (e.symm ⟨g₂ z.1, hs₂ z.2⟩).1 :=
        (c₁.hc.mono hsubb₁).comp_continuous h₄ fun z ↦ (e.symm _).2
      exact h₅.congr fun z ↦ (hE' z.2).symm
  obtain ⟨ψ, hψc, hψb, hψe⟩ := exists_extension oArc_sphere oArc_sphere hm
  rw [closedInner_sphere] at hψc hψb
  refine ⟨g₂ ∘ ψ ∘ p₁, c₂.gc.comp (hψc.comp c₁.hc c₁.hm) (hψb.mapsTo.comp c₁.hm), ?_, fun x ↦ ?_⟩
  · refine ⟨fun x hx ↦ c₂.gm (hψb.mapsTo (c₁.hm hx)), fun x hx y hy h ↦ ?_, fun y hy ↦ ?_⟩
    · have h₃ := c₂.hg.injOn (hψb.mapsTo (c₁.hm hx)) (hψb.mapsTo (c₁.hm hy)) h
      have h₄ := hψb.injOn (c₁.hm hx) (c₁.hm hy) h₃
      rw [← c₁.gh hx, ← c₁.gh hy, h₄]
    · obtain ⟨w, hw, hwe⟩ := hψb.surjOn (c₂.hm hy)
      refine ⟨g₁ w, c₁.gm hw, ?_⟩
      simp only [Function.comp_apply, c₁.hg hw, hwe]
      exact c₂.gh hy
  · have hx := x.2
    simp only [Function.comp_apply]
    rw [hψe (hsb₁ hx), hE (hsb₁ hx)]
    have : (⟨g₁ (p₁ x.1), hs₁ (hsb₁ hx)⟩ : discBd D₁) = x := Subtype.ext (c₁.gh (hsubb₁ hx))
    rw [this]
    exact c₂.gh (hsubb₂ (e x).2)

variable {S T₁ T₂ : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace T₁] [TopologicalSpace
  T₂]

omit [T2Space S] in
/-- A capping of a surface is unique up to homeomorphism. We extend the identity of `Σ` over each
pasted disc. -/
theorem IsCappedSurface.nonempty_homeomorph (hS : IsSurface S) (cap₁ : IsCappedSurface S T₁)
    (cap₂ : IsCappedSurface S T₂) : Nonempty (T₁ ≃ₜ T₂) := by
  classical
  have hs₁ := cap₁.isSurface
  have hs₂ := cap₂.isSurface
  have : T2Space T₁ := hs₁.2.1
  have : T2Space T₂ := hs₂.2.1
  have : CompactSpace T₁ := hs₁.1
  have : CompactSpace S := hS.1
  have hc₁ := cap₁.isClosedEmbedding hS
  have hc₂ := cap₂.isClosedEmbedding hS
  have hdisc : ∀ Θ ∈ cuffs S, ∃ G : T₁ → T₂, ContinuousOn G (closure (cap₁.cuffDisc Θ)) ∧
      BijOn G (closure (cap₁.cuffDisc Θ)) (closure (cap₂.cuffDisc Θ)) ∧ ∀ y ∈ Θ, G (cap₁.emb y)
        = cap₂.emb y := by
    intro Θ hΘ
    have hb₁ := cap₁.cuffDisc_bd Θ hΘ
    have hb₂ := cap₂.cuffDisc_bd Θ hΘ
    let e₁ : Θ ≃ₜ discBd (closure (cap₁.cuffDisc Θ)) :=
      (cap₁.isEmbedding.homeomorphImage Θ).trans (Homeomorph.setCongr hb₁.symm)
    let e₂ : Θ ≃ₜ discBd (closure (cap₂.cuffDisc Θ)) :=
      (cap₂.isEmbedding.homeomorphImage Θ).trans (Homeomorph.setCongr hb₂.symm)
    obtain ⟨G, hG, hb, he⟩ := exists_disc_ext (cap₁.cuffDisc_closedDisc Θ hΘ)
      (cap₂.cuffDisc_closedDisc Θ hΘ)
      (e₁.symm.trans e₂)
    refine ⟨G, hG, hb, fun y hy ↦ ?_⟩
    have := he (e₁ ⟨y, hy⟩)
    simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply] at this
    exact this
  have : Nonempty T₂ := cap₂.connected.toNonempty
  choose! G hGc hGb hGe using hdisc
  have hfin : (cuffs S).Finite := (cuff_statement S hS).2.1
  have hd₁ : ∀ x, x ∉ range cap₁.emb → ∃ Θ ∈ cuffs S, x ∈ cap₁.cuffDisc Θ := fun x hx ↦ by
    have : x ∈ (range cap₁.emb)ᶜ := hx
    rw [cap₁.compl_eq] at this
    simpa using this
  have hd₂ : ∀ x, x ∉ range cap₂.emb → ∃ Θ ∈ cuffs S, x ∈ cap₂.cuffDisc Θ := fun x hx ↦ by
    have : x ∈ (range cap₂.emb)ᶜ := hx
    rw [cap₂.compl_eq] at this
    simpa using this
  let H : T₁ → T₂ := fun x ↦ if h : x ∈ range cap₁.emb then cap₂.emb h.choose else
    if h' : ∃ Θ ∈ cuffs S, x ∈ cap₁.cuffDisc Θ then G h'.choose x else Classical.arbitrary T₂
  have hH₁ : ∀ y, H (cap₁.emb y) = cap₂.emb y := fun y ↦ by
    have h : cap₁.emb y ∈ range cap₁.emb := mem_range_self y
    change dite _ _ _ = _
    rw [dite_eq_left h, cap₁.isEmbedding.injective h.choose_spec]
  have hH₂ : ∀ Θ ∈ cuffs S, ∀ x ∈ closure (cap₁.cuffDisc Θ), H x = G Θ x := by
    intro Θ hΘ x hx
    rw [cap₁.closure_cuffDisc hS hΘ] at hx
    rcases hx with hx | ⟨y, hy, rfl⟩
    · have hr := cap₁.notMem_range hΘ hx
      have h' : ∃ Θ ∈ cuffs S, x ∈ cap₁.cuffDisc Θ := ⟨Θ, hΘ, hx⟩
      change dite _ _ _ = _
      rw [dite_eq_right hr, dite_eq_left h']
      have hch := h'.choose_spec
      have he : h'.choose = Θ := by
        by_contra hne
        exact disjoint_left.1 (cap₁.cuffDisc_disjoint _ hch.1 _ hΘ hne) (subset_closure hch.2)
          (subset_closure hx)
      rw [he]
    · rw [hH₁, hGe Θ hΘ y hy]
  have hsub₁ : ∀ {Θ}, Θ ∈ cuffs S → cap₁.emb '' Θ ⊆ closure (cap₁.cuffDisc Θ) := fun {Θ} hΘ ↦ by
    rw [cap₁.closure_cuffDisc hS hΘ]
    exact subset_union_right
  have hrange₂ : ∀ {Θ}, Θ ∈ cuffs S → ∀ y, cap₂.emb y ∈ closure (cap₂.cuffDisc Θ) → y ∈ Θ
    := fun {Θ} hΘ y hy ↦ by
    rw [cap₂.closure_cuffDisc hS hΘ] at hy
    rcases hy with hy | ⟨z, hz, he⟩
    · exact absurd (mem_range_self y) (cap₂.notMem_range hΘ hy)
    · exact cap₂.isEmbedding.injective he ▸ hz
  have hcont : Continuous H := by
    have : Finite (cuffs S) := hfin
    let f : Option (cuffs S) → Set T₁ := fun o ↦ o.elim (range cap₁.emb) fun Θ ↦ closure
      (cap₁.cuffDisc Θ.1)
    refine LocallyFinite.continuous (f := f) (locallyFinite_of_finite f) ?_ ?_ ?_
    · refine eq_univ_of_forall fun x ↦ ?_
      by_cases hx : x ∈ range cap₁.emb
      · exact mem_iUnion.2 ⟨none, hx⟩
      · obtain ⟨Θ, hΘ, h⟩ := hd₁ x hx
        exact mem_iUnion.2 ⟨some ⟨Θ, hΘ⟩, subset_closure h⟩
    · rintro (_ | Θ)
      · exact hc₁.isClosed_range
      · exact isClosed_closure
    · rintro (_ | Θ)
      · change ContinuousOn H (range cap₁.emb)
        rw [continuousOn_iff_continuous_domRestrict]
        have : (range cap₁.emb).domRestrict H = cap₂.emb ∘ cap₁.isEmbedding.toHomeomorph.symm := by
          funext z
          obtain ⟨z, y, rfl⟩ := z
          have h₁ : cap₁.isEmbedding.toHomeomorph.symm ⟨_, mem_range_self y⟩ = y :=
            cap₁.isEmbedding.toHomeomorph.symm_apply_apply y
          change H (cap₁.emb y) = cap₂.emb (cap₁.isEmbedding.toHomeomorph.symm ⟨_, mem_range_self
            y⟩)
          rw [h₁, hH₁]
        rw [this]
        exact cap₂.isEmbedding.continuous.comp (Homeomorph.continuous _)
      · exact (hGc Θ.1 Θ.2).congr (hH₂ Θ.1 Θ.2)
  have hinj : Function.Injective H := by
    have key : ∀ y x, x ∉ range cap₁.emb → H (cap₁.emb y) ≠ H x := fun y x hx he ↦ by
      obtain ⟨Θ, hΘ, h⟩ := hd₁ x hx
      have hxc := subset_closure h
      rw [hH₁, hH₂ Θ hΘ x hxc] at he
      have hm := (hGb Θ hΘ).mapsTo hxc
      rw [← he] at hm
      have hy := hrange₂ hΘ y hm
      have := (hGb Θ hΘ).injOn (hsub₁ hΘ (mem_image_of_mem _ hy)) hxc (by rw [hGe Θ hΘ y hy, he])
      exact hx (this ▸ mem_range_self y)
    intro x x' he
    by_cases hx : x ∈ range cap₁.emb
    · obtain ⟨y, rfl⟩ := hx
      by_cases hx' : x' ∈ range cap₁.emb
      · obtain ⟨y', rfl⟩ := hx'
        rw [hH₁, hH₁] at he
        rw [cap₂.isEmbedding.injective he]
      · exact absurd he (key y x' hx')
    · by_cases hx' : x' ∈ range cap₁.emb
      · obtain ⟨y', rfl⟩ := hx'
        exact absurd he.symm (key y' x hx)
      · obtain ⟨Θ, hΘ, h⟩ := hd₁ x hx
        obtain ⟨Θ', hΘ', h'⟩ := hd₁ x' hx'
        have hc := subset_closure h
        have hc' := subset_closure h'
        rw [hH₂ Θ hΘ x hc, hH₂ Θ' hΘ' x' hc'] at he
        by_cases hne : Θ = Θ'
        · subst hne
          exact (hGb Θ hΘ).injOn hc hc' he
        · have h₁ := (hGb Θ hΘ).mapsTo hc
          rw [he] at h₁
          exact absurd ((hGb Θ' hΘ').mapsTo hc') (disjoint_left.1 (cap₂.cuffDisc_disjoint _ hΘ _
            hΘ' hne) h₁)
  have hsurj : Function.Surjective H := by
    intro y
    by_cases hy : y ∈ range cap₂.emb
    · obtain ⟨z, rfl⟩ := hy
      exact ⟨_, hH₁ z⟩
    · obtain ⟨Θ, hΘ, h⟩ := hd₂ y hy
      obtain ⟨x, hx, rfl⟩ := (hGb Θ hΘ).surjOn (subset_closure h)
      exact ⟨x, hH₂ Θ hΘ x hx⟩
  exact ⟨hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective H ⟨hinj, hsurj⟩)⟩

end GraphMinor.GM19
