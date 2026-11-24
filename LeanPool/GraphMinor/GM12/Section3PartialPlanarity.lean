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

/-!
# Planarity inside a partial fill

For the three-branch case of XII (3.1), page 245, a disc enclosing one
cuff cannot contain the whole schismatic set. Any set contained in
such a disc would be planar after that cuff is filled, hence near-planar.
The constructed cap and cap independence prove this for arbitrary sets.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A set lying in a disc in a partial fill is near-planar in the
original punctured surface. The cap is constructed rather than assumed. -/
theorem isNearPlanar_of_image_subset_disc_in_partial_fill
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) (i : ι)
    {X : Set (discComplement Δ)} {D : Set S} (hD : IsClosedDisc D)
    (hDT : D ⊆ discComplement (fun k : {k // k ≠ i} => Δ k.val))
    (hXD : (Subtype.val : discComplement Δ → S) '' X ⊆ D) :
    GM07.IsNearPlanar X := by
  obtain ⟨j, hj, hjval⟩ := exists_cap_discComplement_cuff hS Δ hΔ hdisj i
  have hp : IsPlanar (j '' X) := by
    refine ⟨Subtype.val ⁻¹' D, (isClosedDisc_subtype_preimage hDT hD).1, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    change (j x).val ∈ D
    rw [hjval]
    exact hXD (mem_image_of_mem Subtype.val hx)
  exact Or.inr ⟨_, hj.cuff,
    isPlanarInCappedCuff_of_one_cap (discComplement_isSurface hS Δ hΔ hdisj) hj hp⟩

end GraphMinor.GM12
