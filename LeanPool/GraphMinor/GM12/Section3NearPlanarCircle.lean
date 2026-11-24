/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CapOneDisc
public import LeanPool.GraphMinor.GM12.Section3CapComparison
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Small circles are near-planar

Condition (i) of XII (3.1), page 245, says that a small normal circle
bounds a disc enclosing at most one deleted disc. If it encloses none,
the bounded disc remains in Sigma-star. If it encloses one, it remains
after that cuff is filled. Cap independence then proves near-planarity
in the exact sense of VII.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A bounded disc whose boundary remains in Sigma-star lies wholly
there if it includes none of the deleted discs. Connectedness of each
deleted disc's interior excludes a partial crossing of that disc. -/
theorem disc_subset_discComplement_of_no_deleted_disc
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {D : Set S} (hD : IsClosedDisc D) (hbd : discBd D ⊆ discComplement Δ)
    (hno : ∀ i, ¬ Δ i ⊆ D) : D ⊆ discComplement Δ := by
  have hout : ∀ i, Disjoint (discInt (Δ i)) D := by
    intro i
    have hdis : Disjoint (discInt (Δ i)) (discBd D) := by
      apply Set.disjoint_left.mpr
      intro x hxI hxB
      exact hxI.2 (discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨hbd hxB, hxI.1⟩)
    rcases hD.side (fun x => (hS.2.2 x).isManifoldPoint)
      (hΔ i).isPreconnected_discInt hdis with hin | hout
    · apply False.elim
      apply hno i
      apply (hΔ i).subset_closure_discInt.trans
      rw [← hD.isClosed.closure_eq]
      exact closure_mono (hin.trans (discInt_subset D))
    · exact hout
  intro x hxD
  by_cases hx : x ∈ ⋃ i, Δ i
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    have hxb : x ∈ discBd (Δ i) := by
      by_contra hn
      exact Set.disjoint_left.mp (hout i) ⟨hxi, hn⟩ hxD
    exact disc_boundary_subset_discComplement hS Δ hΔ hdisj i hxb
  · exact subset_closure hx

/-- The topological conclusion of XII (3.1)(i) makes its circle
near-planar in Sigma-star. At most one cuff needs to be filled. -/
theorem isNearPlanar_of_bounds_disc_including_at_most_one
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {F : Set (discComplement Δ)} {D : Set S} (hD : IsClosedDisc D)
    (hbd : discBd D = (Subtype.val : discComplement Δ → S) '' F)
    (hone : ∀ i j, Δ i ⊆ D → Δ j ⊆ D → i = j) : GM07.IsNearPlanar F := by
  classical
  let C := discComplement Δ
  have hbC : discBd D ⊆ C := by
    rw [hbd]
    rintro x ⟨y, _, rfl⟩
    exact y.property
  by_cases hex : ∃ i, Δ i ⊆ D
  · obtain ⟨i, hi⟩ := hex
    let T := discComplement (fun k : {k // k ≠ i} => Δ k.val)
    have hCT : C ⊆ T := by
      change C ⊆ discComplement (fun k : {k // k ≠ i} => Δ k.val)
      rw [discComplement_except_eq_union Δ hΔ hdisj i]
      exact subset_union_left
    have hDT : D ⊆ T := disc_subset_discComplement_of_no_deleted_disc hS
      (fun k : {k // k ≠ i} => Δ k.val) (fun k => hΔ k.val)
      (fun a b hab => hdisj (fun he => hab (Subtype.ext he))) hD (hbC.trans hCT)
      (fun k hk => k.property (hone k.val i hk hi))
    obtain ⟨j, hj, hjval⟩ := exists_cap_discComplement_cuff hS Δ hΔ hdisj i
    have hplan : IsPlanar (j '' F) := by
      refine ⟨Subtype.val ⁻¹' D, (isClosedDisc_subtype_preimage hDT hD).1, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      change (j x).val ∈ D
      rw [hjval]
      exact discBd_subset D (hbd.symm ▸ mem_image_of_mem Subtype.val hx)
    have hp := isPlanarInCappedCuff_of_one_cap (discComplement_isSurface hS Δ hΔ hdisj) hj hplan
    exact Or.inr ⟨_, hj.cuff, hp⟩
  · have hDC := disc_subset_discComplement_of_no_deleted_disc hS Δ hΔ hdisj hD hbC
      (fun i hi => hex ⟨i, hi⟩)
    left
    refine ⟨Subtype.val ⁻¹' D, (isClosedDisc_subtype_preimage hDC hD).1, ?_⟩
    intro x hx
    exact discBd_subset D (hbd.symm ▸ mem_image_of_mem Subtype.val hx)

end GraphMinor.GM12
