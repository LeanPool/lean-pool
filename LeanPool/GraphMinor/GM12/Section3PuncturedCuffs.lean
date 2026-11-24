/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3BoundaryEquality
import LeanPool.GraphMinor.GM12.Section3ClosedComponents
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# The cuffs of the punctured surface

The surface Sigma-star in XII (3.1), page 245, has one cuff for each
removed disc. Its boundary is the union of those circles, which are
closed, connected and pairwise disjoint. Their preimages under inclusion
are therefore exactly the boundary components. Distinct discs give
distinct cuffs, so their number is the number of prescribed discs.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- The cuffs of Sigma-star are precisely the prescribed disc
boundaries read in that subspace, as used in XII (3.1), page 245. -/
theorem discComplement_cuffs_eq {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) :
    cuffs (discComplement Δ) =
      range (fun i => (Subtype.val : discComplement Δ → S) ⁻¹' discBd (Δ i)) := by
  let Q : ι → Set (discComplement Δ) := fun i => (Subtype.val : discComplement Δ → S) ⁻¹' discBd
    (Δ i)
  have hQO : ∀ i, IsOArc (Q i) := fun i => isOArc_subtype_preimage
    (disc_boundary_subset_discComplement hS Δ hΔ hdisj i) (hΔ i).isOArc_discBd
  have hclosed : ∀ i, IsClosed (Q i) := fun i =>
    (hΔ i).isOArc_discBd.isCompact.isClosed.preimage continuous_subtype_val
  have hconn : ∀ i, IsPreconnected (Q i) := fun i => (hQO i).isPreconnected
  have hne : ∀ i, (Q i).Nonempty := by
    intro i
    obtain ⟨f⟩ := hQO i
    exact ⟨(f 1).val, (f 1).property⟩
  have hpair : Pairwise (fun i j => Disjoint (Q i) (Q j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    exact Set.disjoint_left.mp (hdisj hij) (Surface.discBd_subset _ hxi)
      (Surface.discBd_subset _ hxj)
  change componentsIn (bd (discComplement Δ)) = range Q
  rw [discComplement_boundary_eq hS Δ hΔ, preimage_iUnion]
  exact componentsIn_iUnion_disjoint_closed Q hclosed hconn hne hpair

/-- There is exactly one cuff per prescribed disc in Sigma-star.
This gives the cuff count in the application of VII (7.5) for XII (3.1). -/
theorem discComplement_cuff_count {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) :
    (cuffs (discComplement Δ)).ncard = Nat.card ι := by
  let Q : ι → Set (discComplement Δ) := fun i => (Subtype.val : discComplement Δ → S) ⁻¹' discBd
    (Δ i)
  have hQi : Function.Injective Q := by
    intro i j heq
    by_contra hij
    obtain ⟨f⟩ := (hΔ i).isOArc_discBd
    let z := (f 1).val
    have hz : z ∈ discBd (Δ i) := (f 1).property
    have hzC : z ∈ discComplement Δ := disc_boundary_subset_discComplement hS Δ hΔ hdisj i hz
    let x : discComplement Δ := ⟨z, hzC⟩
    have hxi : x ∈ Q i := hz
    have hxj : x ∈ Q j := heq ▸ hxi
    exact Set.disjoint_left.mp (hdisj hij) (Surface.discBd_subset _ hz)
      (Surface.discBd_subset _ hxj)
  rw [discComplement_cuffs_eq hS Δ hΔ hdisj]
  exact Set.ncard_range_of_injective hQi

/-- Removing a nonempty family of prescribed discs leaves at least
one cuff, as needed for applying the capped planar criterion in XII (3.1). -/
theorem discComplement_cuffs_nonempty
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι] [Nonempty ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) :
    (cuffs (discComplement Δ)).Nonempty := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  refine ⟨Subtype.val ⁻¹' discBd (Δ i), ?_⟩
  rw [discComplement_cuffs_eq hS Δ hΔ hdisj]
  exact mem_range_self i

end GraphMinor.GM12
