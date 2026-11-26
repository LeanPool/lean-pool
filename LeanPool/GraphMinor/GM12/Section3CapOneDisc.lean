/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3FillOneDisc
public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM12.Section3PuncturedCuffs
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs

/-!
# Capping a prescribed cuff

In the reduction of XII (3.1), page 245, to VII, a cuff of Sigma-star
is capped by putting its deleted disc back. The space with all other
discs removed supplies the cap, with its inclusion into the original
surface unchanged on points.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Filling one deleted disc gives a capped surface in the precise
sense used for surrounding curves in VII. Both inclusions fix points
of the original surface. -/
theorem exists_cap_discComplement_cuff
    {S : Type*} {ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) (i : ι) :
    ∃ j : discComplement Δ → discComplement (fun k : {k // k ≠ i} => Δ k.val),
      GM07.IsCappedCuff ((Subtype.val : discComplement Δ → S) ⁻¹' discBd (Δ i))
        (discComplement (fun k : {k // k ≠ i} => Δ k.val)) j
        (Subtype.val ⁻¹' Δ i) ∧ ∀ x, (j x).val = x.val := by
  let C := discComplement Δ
  let T := discComplement (fun k : {k // k ≠ i} => Δ k.val)
  have hT : T = C ∪ Δ i := discComplement_except_eq_union Δ hΔ hdisj i
  have hCT : C ⊆ T := by rw [hT]; exact subset_union_left
  have hDT : Δ i ⊆ T := by rw [hT]; exact subset_union_right
  let j : C → T := Set.inclusion hCT
  have hdisc := isClosedDisc_subtype_preimage hDT (hΔ i)
  have hbdImage : (Subtype.val : T → S) ⁻¹' discBd (Δ i) =
      j '' ((Subtype.val : C → S) ⁻¹' discBd (Δ i)) := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x.val, disc_boundary_subset_discComplement hS Δ hΔ hdisj i hx⟩, hx, ?_⟩
      rfl
    · rintro ⟨y, hy, rfl⟩
      exact hy
  refine ⟨j, ?_, fun _ => rfl⟩
  constructor
  · change (Subtype.val ⁻¹' discBd (Δ i)) ∈ cuffs C
    rw [discComplement_cuffs_eq hS Δ hΔ hdisj]
    exact mem_range_self i
  · exact discComplement_isSurface hS _ (fun k => hΔ k.val)
      (fun a b hab => hdisj (fun he => hab (Subtype.ext he)))
  · exact IsEmbedding.inclusion hCT
  · exact hdisc.1
  · exact hdisc.2.trans hbdImage
  · ext x
    constructor
    · intro _
      trivial
    · intro _
      have hx : x.val ∈ T := x.property
      rw [hT] at hx
      rcases hx with hxC | hxD
      · exact Or.inl ⟨⟨x.val, hxC⟩, rfl⟩
      · exact Or.inr hxD
  · ext x
    constructor
    · rintro ⟨⟨y, rfl⟩, hxD⟩
      apply mem_image_of_mem j
      exact discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨y.property, hxD⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, discBd_subset (Δ i) hy⟩

end GraphMinor.GM12
