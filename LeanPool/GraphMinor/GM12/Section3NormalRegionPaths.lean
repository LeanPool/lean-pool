/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Topology.Connected.PathConnected
import LeanPool.GraphMinor.GM11.Theorem75
import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# Normal connections through regions

To construct the normal sets used in the minimum for XII (3.1),
page 245, join points through drawing regions and their incident
vertices. A vertex in the closure of a region has an approach path
whose other points lie in that region. Two regions whose closures
meet either coincide or share an incident vertex: an intersection
in an edge extends along that edge to an end. Thus points in these
regions can be joined without crossing edge interiors.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A vertex incident with a region joins any point of that region
through points outside the drawing and drawing vertices. -/
theorem joinedIn_normal_points_of_vertex_region
    {S : Type*} [TopologicalSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S)
    {r : Set S} (hr : r ∈ Γ.R) {x y : S}
    (hx : x ∈ Γ.V) (hxr : x ∈ closure r) (hy : y ∈ r) :
    JoinedIn (Γ.Uᶜ ∪ Γ.V) x y := by
  let : T2Space S := hS.2.1
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨g, hgc, hg0, hgr⟩ := exists_path_into_region hS Γ hx hr hxr
  let p : Path x (g 1) := {
    toFun := g
    continuous_toFun := hgc
    source' := hg0
    target' := rfl }
  have hp : JoinedIn (Γ.Uᶜ ∪ Γ.V) x (g 1) := by
    refine ⟨p, ?_⟩
    intro t
    by_cases ht : t = 0
    · exact Or.inr (by change g t ∈ Γ.V; rwa [ht, hg0])
    · have htr : g t ∈ r := hgr t (lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht))
      exact Or.inl (region_subset hr htr)
  have hrp : IsPathConnected r := isPathConnected_of_isOpen hS
    (region_isOpen hr) (region_isPreconnected hr) (region_nonempty hr)
  have hrN : r ⊆ Γ.Uᶜ ∪ Γ.V := fun _ hz => Or.inl (region_subset hr hz)
  exact hp.trans ((hrp.joinedIn (g 1) (hgr 1 zero_lt_one) y hy).mono hrN)

/-- Points in regions with intersecting closures can be joined
normally, using a common incident vertex when the regions differ. -/
theorem joinedIn_normal_points_of_meeting_region_closures
    {S : Type*} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S)
    {r s : Set S} (hr : r ∈ Γ.R) (hs : s ∈ Γ.R)
    {x y : S} (hx : x ∈ r) (hy : y ∈ s) (hmeet : (closure r ∩ closure s).Nonempty) :
    JoinedIn (Γ.Uᶜ ∪ Γ.V) x y := by
  let : T2Space S := hS.2.1
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨z, hzr, hzs⟩ := hmeet
  by_cases hzU : z ∈ Γ.U
  · have hex : ∃ v ∈ Γ.V, v ∈ closure r ∩ closure s := by
      by_cases hzV : z ∈ Γ.V
      · exact ⟨z, hzV, hzr, hzs⟩
      · obtain ⟨e, he, hze⟩ := Γ.exists_edge_of_mem hzU hzV
        have her := edge_subset_closure_of_incident hS he hr ⟨z, hze, hzr⟩
        have hes := edge_subset_closure_of_incident hS he hs ⟨z, hze, hzs⟩
        obtain ⟨γ, hγ⟩ := exists_edgePar Γ
        refine ⟨γ e 0, ?_, ?_, ?_⟩
        · exact end_mem_V hγ he false
        · exact closure_minimal her isClosed_closure (end_mem_closure hγ he false)
        · exact closure_minimal hes isClosed_closure (end_mem_closure hγ he false)
    obtain ⟨v, hv, hvr, hvs⟩ := hex
    exact (joinedIn_normal_points_of_vertex_region hS Γ hr hv hvr hx).symm.trans
      (joinedIn_normal_points_of_vertex_region hS Γ hs hv hvs hy)
  · obtain ⟨t, ht, hzt⟩ := exists_region_of_notMem hzU
    have heqr : t = r := by
      obtain ⟨w, hwt, hwr⟩ := mem_closure_iff.mp hzr t (region_isOpen ht) hzt
      exact region_eq_of_mem ht hr hwt hwr
    have heqs : t = s := by
      obtain ⟨w, hwt, hws⟩ := mem_closure_iff.mp hzs t (region_isOpen ht) hzt
      exact region_eq_of_mem ht hs hwt hws
    have hrs : r = s := heqr.symm.trans heqs
    have hrp : IsPathConnected r := isPathConnected_of_isOpen hS
      (region_isOpen hr) (region_isPreconnected hr) (region_nonempty hr)
    have hrN : r ⊆ Γ.Uᶜ ∪ Γ.V := fun _ hz => Or.inl (region_subset hr hz)
    exact (hrp.joinedIn x hx y (hrs.symm ▸ hy)).mono hrN

end GraphMinor.GM12
