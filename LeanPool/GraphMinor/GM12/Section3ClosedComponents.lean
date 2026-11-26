/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM12.Section2Corners

/-!
# Components of a finite disjoint closed family

The punctured surface in XII (3.1), page 245, has the disc boundaries
as its cuffs. Each is connected and closed, and the finite family is
disjoint. A connected component of the union must stay in one member,
while that whole connected member belongs to the component.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- The connected components of the union of a finite disjoint family
of nonempty closed preconnected sets are exactly its members. -/
theorem componentsIn_iUnion_disjoint_closed {S ι : Type*} [TopologicalSpace S] [Finite ι]
    (Q : ι → Set S) (hclosed : ∀ i, IsClosed (Q i))
    (hconn : ∀ i, IsPreconnected (Q i)) (hne : ∀ i, (Q i).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (Q i) (Q j))) :
    componentsIn (⋃ i, Q i) = range Q := by
  have hcomponent : ∀ i, ∀ x ∈ Q i, connectedComponentIn (⋃ j, Q j) x = Q i := by
    intro i x hx
    have hxU : x ∈ ⋃ j, Q j := mem_iUnion.mpr ⟨i, hx⟩
    apply Subset.antisymm
    · apply preconnected_subset_closed_piece isPreconnected_connectedComponentIn Q hclosed
        (connectedComponentIn_subset _ _) _ ⟨x, mem_connectedComponentIn hxU, hx⟩
      intro j k hjk
      apply Set.disjoint_left.mpr
      intro y _ hy
      exact Set.disjoint_left.mp (hdisj hjk) hy.1 hy.2
    · exact (hconn i).subset_connectedComponentIn hx (subset_iUnion Q i)
  ext E
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact ⟨i, (hcomponent i x hxi).symm⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hne i
    exact ⟨x, mem_iUnion.mpr ⟨i, hx⟩, hcomponent i x hx⟩

end GraphMinor.GM12
