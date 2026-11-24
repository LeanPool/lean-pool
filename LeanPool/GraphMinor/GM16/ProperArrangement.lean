/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs

/-!
# Properness of the arrangements used in XVI (7.2)

The observation on page 62 of XVI concerns the construction in XV (7.7).
The societies with more than three boundary vertices come from distinct
pieces whose vertex sets are disjoint by XV (7.6). An intersection of
their arrangement discs would give a common boundary vertex, so their
discs are disjoint. The second lemma expresses the same argument using
the disjoint containing discs in XV (7.5)(i).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14
universe u v w

/-- The properness observation in XVI, page 62: disjoint boundary vertex
sets for the large societies force disjoint arrangement discs. -/
theorem IsSurfaceArrangement.isProper_of_disjoint_boundaries
    {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {𝒮 : Set (Society α β)}
    {disc : Society α β → Set S} {pt : α → S}
    (h : IsSurfaceArrangement 𝒮 disc pt)
    (hDisj : ∀ A ∈ 𝒮, ∀ B ∈ 𝒮, A ≠ B →
      3 < A.Ω.bar.ncard → 3 < B.Ω.bar.ncard → Disjoint A.Ω.bar B.Ω.bar) :
    IsProperArrangement 𝒮 disc pt := by
  refine ⟨h, ?_⟩
  intro A hA B hB hne hlargeA hlargeB
  refine disjoint_left.mpr ?_
  intro x hxA hxB
  obtain ⟨v, hv, _⟩ := h.inter_discs _ hA _ hB hne ⟨hxA, hxB⟩
  exact (disjoint_left.mp (hDisj _ hA _ hB hne hlargeA hlargeB)) hv.1 hv.2

/-- The alternative properness check in XVI, page 62, using XV (7.5)(i):
each containing disc contains at most one large society's disc. -/
theorem IsSurfaceArrangement.isProper_of_disjoint_containers
    {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {𝒮 : Set (Society α β)}
    {disc : Society α β → Set S} {pt : α → S}
    {ι : Type*} {Δ : ι → Set S}
    (h : IsSurfaceArrangement 𝒮 disc pt)
    (hΔ : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (hContain : ∀ A ∈ 𝒮, 3 < A.Ω.bar.ncard → ∃ i, disc A ⊆ Δ i)
    (hOne : ∀ i, ∀ A ∈ 𝒮, ∀ B ∈ 𝒮,
      3 < A.Ω.bar.ncard → 3 < B.Ω.bar.ncard →
      disc A ⊆ Δ i → disc B ⊆ Δ i → A = B) :
    IsProperArrangement 𝒮 disc pt := by
  refine ⟨h, ?_⟩
  intro A hA B hB hne hlargeA hlargeB
  obtain ⟨i, hi⟩ := hContain A hA hlargeA
  obtain ⟨j, hj⟩ := hContain B hB hlargeB
  have hij : i ≠ j := fun heq => hne (hOne i A hA B hB hlargeA hlargeB hi (heq ▸ hj))
  exact (hΔ hij).mono hi hj

end GraphMinor.GM16
