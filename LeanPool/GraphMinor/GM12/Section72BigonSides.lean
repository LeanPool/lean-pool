/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72RadialHubs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Comparing a possible empty bigon with the removed disc

For the radial condition in XII (7.2), page 260, the boundary of a
possible new empty bigon lies in the closed outside of the removed
disc. The open interior of that disc is connected and misses the
bigon's boundary. It is therefore wholly inside the bigon or wholly
outside. In the first case the whole removed disc lies in the bigon.
If the bigon misses the boundary vertex, only the second case occurs,
and the bigon already lay in the original region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- A closed disc whose boundary is outside a second disc either
contains that whole disc or misses its open interior. This is the
side comparison for the radial deletion in XII (7.2), page 260. -/
theorem disc_subset_or_disjoint_interior_of_boundary_outside
    (hS : IsClosedSurface S) {D Q : Set S} (hD : IsClosedDisc D) (hQ : IsClosedDisc Q)
    (hbd : discBd Q ⊆ closure (univ \ D)) :
    D ⊆ Q ∨ Disjoint (discInt D) Q := by
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hdis : Disjoint (discInt D) (discBd Q) := by
    apply disjoint_left.mpr
    intro x hxD hxQ
    have hxint : x ∈ interior D :=
      interior_maximal (discInt_subset D) (hD.isOpen_discInt hman) hxD
    have hxout := hbd hxQ
    rw [← compl_eq_univ_sdiff, closure_compl] at hxout
    exact hxout hxint
  rcases hQ.side hman hD.isPreconnected_discInt hdis with hin | hout
  · exact Or.inl (hD.subset_closure_discInt.trans
      (closure_minimal (hin.trans (discInt_subset Q)) hQ.isClosed))
  · exact Or.inr hout

/-- A possible new bigon that misses the removed boundary vertex
already lies in the old region with its own end vertex restored.
This is the unequal-vertex case of the radial condition in XII (7.2). -/
theorem disc_subset_old_region_of_missing_boundary_vertex
    (hS : IsClosedSurface S) {D Q r : Set S} {v x : S}
    (hD : IsClosedDisc D) (hQ : IsClosedDisc Q) (hvD : v ∈ D) (hvQ : v ∉ Q)
    (hbdQ : discBd Q ⊆ closure (univ \ D)) (hbdD : discBd D ⊆ r ∪ {v})
    (hQY : Q ⊆ (r ∪ (D \ {v})) ∪ {x}) : Q ⊆ r ∪ {x} := by
  have hdis : Disjoint (discInt D) Q := by
    rcases disc_subset_or_disjoint_interior_of_boundary_outside hS hD hQ hbdQ with hin | hout
    · exact (hvQ (hin hvD)).elim
    · exact hout
  intro y hy
  rcases hQY hy with (hyr | ⟨hyD, _⟩) | hyx
  · exact Or.inl hyr
  · have hybd : y ∈ discBd D := by
      by_contra hn
      exact disjoint_left.mp hdis ⟨hyD, hn⟩ hy
    rcases hbdD hybd with hyr | hyv
    · exact Or.inl hyr
    · exact (hvQ (mem_singleton_iff.mp hyv ▸ hy)).elim
  · exact Or.inr hyx

end GraphMinor.GM12
