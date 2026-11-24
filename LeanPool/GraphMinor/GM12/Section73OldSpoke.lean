/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73EdgeWalkLift
import LeanPool.GraphMinor.GM12.Section73MergedHub
import LeanPool.GraphMinor.GM12.Section73StarDrawing
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# The old spoke behind an edge at the merged hub

In XII (7.3), Claim (1), page 262, each new spoke at the hub
comes from an old spoke joining the same drawing vertex to an old
region hub. That old hub lies in the merged region. The surviving
old spoke avoids the deleted vertex. These data identify the two
or four edges used to close the lifted circuit.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Recover the surviving old spoke and its old region hub from
an edge at the contracted vertex. This gives the middle vertices
of the two replacement paths in XII (7.3), Claim (1), page 262. -/
theorem exists_old_spoke_at_contracted_vertex
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R)
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hJV : J.V = f '' K.V)
    (hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g})
    {e : Set S} {x : S} (hel : J.toGraph.IsLink e v x) :
    ∃ (g : Set S) (u : S), g ∈ K.E ∧ v ∉ closure g ∧ f '' g = e ∧
      u ∈ r' ∧ u ∈ K.V ∧ u ∉ Γ.V ∧
      x ∈ (deleteVertices Γ {v}).V ∧ K.toGraph.IsLink g u x := by
  obtain ⟨g, hg, rfl⟩ := hJE hel.1
  obtain ⟨w, hw, r, hr, u, hur, huK, hcap, _⟩ := spoke_ends ⟨hK.1, hK.2.1⟩ hS hg.1
  have hwv : w ≠ v := fun h => hg.2 (h ▸ (hcap.superset (Or.inl rfl)).1)
  have hwnew : w ∈ (deleteVertices Γ {v}).V := by
    rw [deleteVertices_V]
    exact ⟨hw, fun h => hwv h⟩
  have hwnr : w ∉ r' := fun hwr => region_subset hr' hwr
    ((deleteVertices Γ {v}).V_subset_U hwnew)
  have hfw : f w = w := hfix w hwnr
  have hwu : w ≠ u := fun h => region_subset hr (h ▸ hur) (Γ.V_subset_U hw)
  have hcapimage : closure (f '' g) ∩ J.V = {w, f u} := by
    rw [hJV, closure_image_inter_vertices (isLine_closure hg.1 hwu hcap)
      (radial_edge_inter_star hS ⟨hK.1, hK.2.1⟩ hv hg.1 hg.2).2 f hfibre,
      hcap, image_insert_eq, image_singleton, hfw]
  have hpair : ({w, f u} : Set S) = {v, x} := hcapimage.symm.trans hel.2.2.2
  have hwx : w = x := (hpair.subset (Or.inl rfl)).resolve_left hwv
  have hfv : f u = v := by
    have hvpair : v ∈ ({w, f u} : Set S) := hpair.superset (Or.inl rfl)
    exact ((hvpair.resolve_left hwv.symm)).symm
  have huv : u ≠ v := fun h => region_subset hr (h ▸ hur) (Γ.V_subset_U hv)
  have hur' : u ∈ r' := by
    by_contra hunr
    exact huv ((hfix u hunr).symm.trans hfv)
  refine ⟨g, u, hg.1, hg.2, rfl, hur', huK,
    (fun hu => region_subset hr hur (Γ.V_subset_U hu)), hwx ▸ hwnew, hg.1, huK, ?_, ?_⟩
  · exact hwx ▸ hK.2.1.2.1 hw
  · rw [← hwx, hcap, pair_comm]

end GraphMinor.GM12
