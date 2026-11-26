/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Section6
public import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# An empty disc with drawing boundary is a face

The open part of such a disc lies in one region by connectedness.
That region cannot cross the disc boundary, because the boundary
belongs to the drawing. It is therefore exactly the disc interior,
and its closure is the whole disc. This identifies the brick faces
in the wall rigidity proof of XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM11

/-- Intrinsic and ambient interiors of a disc agree in a closed surface. -/
theorem discInt_eq_interior_of_closedSurface {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D) : discInt D = interior D := by
  change D \ discBd D = interior D
  rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hD]
  ext x
  constructor
  · rintro ⟨hx,hn⟩
    by_contra hInt
    exact hn ⟨subset_closure hx,hInt⟩
  · intro hx
    exact ⟨interior_subset hx,fun h => h.2 hx⟩

/-- A disc interior avoiding the drawing, with its boundary in the
drawing, is a region and has the given disc as closure. -/
theorem empty_disc_is_region {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {H : Drawing S} {D : Set S} (hD : IsClosedDisc D)
    (hBd : discBd D ⊆ H.U) (hEmpty : Disjoint (interior D) H.U) :
    interior D ∈ H.R ∧ closure (interior D) = D := by
  have hInt := discInt_eq_interior_of_closedSurface hS hD
  have hp : IsPreconnected (interior D) := hInt ▸ hD.isPreconnected_discInt
  obtain ⟨x,hx⟩ := hInt ▸ hD.nonempty_discInt
  obtain ⟨r,hr,hxr⟩ := exists_region_of_notMem ((disjoint_left.mp hEmpty) hx)
  have hSub := subset_region hr hp hEmpty hx hxr
  have hAvoid : Disjoint r (frontier D) := by
    apply disjoint_left.mpr
    intro y hyr hyD
    have hyBd : y ∈ discBd D := GM11.IsClosedDisc.frontier_eq_discBd hS hD ▸ hyD
    exact region_subset hr hyr (hBd hyBd)
  have hRD : r ⊆ D := by
    rcases subset_or_disjoint_of_frontier hD.isCompact.isClosed (region_isPreconnected hr) hAvoid
      with h | h
    · exact h
    · exact ((disjoint_left.mp h) hxr (interior_subset hx)).elim
  have hRInt : r ⊆ interior D := by
    intro y hyr
    rw [← hInt]
    exact ⟨hRD hyr,fun hyBd => region_subset hr hyr (hBd hyBd)⟩
  have hEq : interior D = r := subset_antisymm hSub hRInt
  refine ⟨hEq.symm ▸ hr,subset_antisymm (closure_minimal interior_subset hD.isCompact.isClosed) ?_⟩
  exact hInt ▸ hD.subset_closure_discInt

end GraphMinor.GM16
