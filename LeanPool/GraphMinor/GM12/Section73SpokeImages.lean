/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73MergedHub
public import LeanPool.GraphMinor.GM12.Section73ImageIncidence
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# Vertices and spokes under the radial-star collapse

For the lifted walks in XII (7.3), page 261, the new radial vertices
are the old vertices outside the merged region together with its new
hub at the deleted vertex. Every old hub inside the merged region
has a spoke to that vertex. Spokes whose hubs lie outside it stay
pointwise fixed. These facts identify the old paths corresponding
to the new spokes.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The new radial vertices are precisely the retained old vertices
and the new hub at the deleted vertex. This identifies the walk
vertices in XII (7.3), page 261. -/
theorem image_radial_vertices_eq
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    {f : S → S} (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) :
    f '' K.V = (K.V \ r') ∪ {v} := by
  apply Subset.antisymm
  · rintro y ⟨x, hxK, hxy⟩
    by_cases hxr : x ∈ r'
    · exact Or.inr (hxy.symm.trans (hcollapse x
        (radial_vertices_in_deleted_region hS hK hE hv hr' hvr' ⟨hxK, hxr⟩)))
    · have hxy' : x = y := (hfix x hxr).symm.trans hxy
      exact Or.inl (hxy' ▸ ⟨hxK, hxr⟩)
  · rintro y (hy | hyv)
    · exact ⟨y, hy.1, hfix y hy.2⟩
    · have hyv' : y = v := hyv
      rw [hyv']
      exact ⟨v, hK.2.1.2.1 hv, hcollapse v (Or.inl rfl)⟩

/-- Every old hub in the merged region has a spoke to the deleted
vertex. This supplies the first edge of the two-edge paths in XII
(7.3), page 261. -/
theorem exists_spoke_to_hub_in_deleted_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    {u : S} (huK : u ∈ K.V) (hun : u ∉ Γ.V) (hur' : u ∈ r') :
    ∃ e ∈ K.E, K.toGraph.IsLink e v u := by
  obtain ⟨r, hr, hur⟩ := hK.2.1.2.2.2.1 u ⟨huK, hun⟩
  have hvcl := deleted_vertex_mem_closure_of_region_meeting hS hv hr hr' hvr' ⟨u, hur, hur'⟩
  obtain ⟨e, he, hcap⟩ := exists_spoke_at ⟨hK.1, hK.2.1⟩ hK.2.2 hS hE hr hur huK hv hvcl
  exact ⟨e, he, he, hK.2.1.2.1 hv, huK, hcap⟩

/-- A spoke whose old hub is outside the merged region stays
outside that region. This is the unchanged-edge case of the walk
replacement in XII (7.3), page 261. -/
theorem spoke_closure_disjoint_deleted_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K)
    {v : S} {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R)
    {g r : Set S} {w u : S} (hg : g ∈ K.E) (hvg : v ∉ closure g)
    (hw : w ∈ Γ.V) (hr : r ∈ Γ.R) (hur : u ∈ r)
    (hcap : closure g ∩ K.V = {w, u}) (hun : u ∉ r') :
    Disjoint (closure g) r' := by
  have hdelete := deleteVertices_isSubdrawing Γ {v}
  obtain ⟨t, ht, hrt⟩ := exists_region_superset hdelete hr
  have htr : t ≠ r' := fun h => hun (h ▸ hrt hur)
  have hrdis : Disjoint r r' := disjoint_left.mpr fun x hxr hxr' =>
    htr (region_eq_of_mem ht hr' (hrt hxr) hxr')
  have hwV : w ∈ (deleteVertices Γ {v}).V := by
    rw [deleteVertices_V]
    exact ⟨hw, fun hwv => hvg (hwv ▸ (hcap.superset (Or.inl rfl)).1)⟩
  have hwn : w ∉ r' := fun hwr' => region_subset hr' hwr' ((deleteVertices Γ {v}).V_subset_U hwV)
  apply disjoint_left.mpr
  intro x hxg hxr'
  rcases closure_spoke_subset_region_vertex hS hK.1 hK.2 hg hr hur hcap hxg with hxr | hxw
  · exact disjoint_left.mp hrdis hxr hxr'
  · exact hwn (hxw ▸ hxr')

end GraphMinor.GM12
