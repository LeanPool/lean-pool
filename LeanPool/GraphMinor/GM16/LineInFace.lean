/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Locating a normal circle's lines in faces

After splitting a normal circle at its at most two drawing vertices,
each open line avoids the drawing and is connected. It lies in one
region. Taking its closure puts the whole line in the region closure,
and only its ends can meet that face's boundary. These are the local
face data used in the rigidity check of XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface GM11

/-- A line whose open part avoids a drawing lies in one face closure. -/
theorem exists_face_containing_line {S : Type*} [TopologicalSpace S] [T2Space S]
    {H : Drawing S} {P : Set S} {a b : S} (hP : IsLineWithEnds P a b)
    (hAvoid : Disjoint (P \ {a,b}) H.U) :
    ∃ r ∈ H.R, P \ {a,b} ⊆ r ∧ P ⊆ closure r := by
  have hp := isPathConnected_sdiff_pair hP
  obtain ⟨x,hx⟩ := hp.nonempty
  obtain ⟨r,hr,hxr⟩ := exists_region_of_notMem ((disjoint_left.mp hAvoid) hx)
  have hSub := subset_region hr hp.isConnected.isPreconnected hAvoid hx hxr
  exact ⟨r,hr,hSub,closure_sdiff_pair hP ▸ closure_mono hSub⟩

/-- A line with open part in a region meets the boundary of a disc
closure of that region only at its ends. -/
theorem line_inter_face_boundary_subset {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {H : Drawing S} {r P : Set S} {a b : S}
    (hr : r ∈ H.R) (hDisc : IsClosedDisc (closure r))
    (hSub : P \ {a,b} ⊆ r) : P ∩ discBd (closure r) ⊆ {a,b} := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hrInt : r ⊆ interior (closure r) := interior_maximal subset_closure (region_isOpen hr)
  rintro x ⟨hxP,hxBd⟩
  by_contra hn
  have hxInt := hrInt (hSub ⟨hxP,hn⟩)
  have hxFr : x ∈ frontier (closure r) :=
    (GM11.IsClosedDisc.frontier_eq_discBd hS hDisc).symm ▸ hxBd
  exact hxFr.2 hxInt

/-- The boundary of a disc face closure belongs to the drawing. -/
theorem face_disc_boundary_subset_U {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) {H : Drawing S} {r : Set S}
    (hr : r ∈ H.R) (hDisc : IsClosedDisc (closure r)) : discBd (closure r) ⊆ H.U := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hrInt : r ⊆ interior (closure r) := interior_maximal subset_closure (region_isOpen hr)
  intro x hx
  have hxCl : x ∈ closure r := Surface.discBd_subset _ hx
  rcases closure_region_subset hr hxCl with hxR | hxU
  · have hxFr : x ∈ frontier (closure r) :=
      (GM11.IsClosedDisc.frontier_eq_discBd hS hDisc).symm ▸ hx
    exact (hxFr.2 (hrInt hxR)).elim
  · exact hxU

end GraphMinor.GM16
