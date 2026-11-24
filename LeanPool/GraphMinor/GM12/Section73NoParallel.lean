/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73DiscPreprocess
import LeanPool.GraphMinor.GM12.Section72Regions
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.GM11.RadialBasics

/-!
# Parallel radial spokes after the selected-disc reduction

The claim in XII (7.3), page 261, that vertex deletion being two-cell
rules out parallel radial spokes needs the selected-disc reduction:
a loop at the deleted vertex is a counterexample without it. Once
no selected one-vertex disc contains an old edge, two parallel spokes
would bound a selected disc containing only their old region and
boundary vertex. This contradicts the radial condition.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- A normal closed disc containing no old edge and only its boundary
vertex from the old vertex set lies in the boundary region with that
vertex restored. -/
theorem disc_subset_region_vertex_of_no_edges (hS : IsClosedSurface S)
    {Γ : Drawing S} {D F r : Set S} {v : S}
    (hD : IsClosedDisc D) (hbd : discBd D = F) (hvF : v ∈ F)
    (hn : (PaintingOrDrawing.drawing Γ).IsNormal F) (hVD : Γ.V ∩ D = {v})
    (hr : r ∈ Γ.R) (hFr : F \ {v} ⊆ r)
    (hno : ∀ e ∈ Γ.E, ¬ e ⊆ D) : D ⊆ r ∪ {v} := by
  have hfront : frontier D = F := (IsClosedDisc.frontier_eq_discBd hS hD).trans hbd
  have hΓD : Γ.U ∩ D ⊆ {v} := by
    rintro x ⟨hxΓ, hxD⟩
    by_cases hxV : x ∈ Γ.V
    · exact hVD.subset ⟨hxV, hxD⟩
    · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxΓ hxV
      have hdis : Disjoint e (frontier D) := by
        apply disjoint_left.mpr
        intro y hye hyF
        exact (he.2.1 hye).2 (hn ⟨hfront ▸ hyF, (he.2.1 hye).1⟩)
      exact (hno e he (subset_of_disjoint_frontier he.2.2.1.isConnected.isPreconnected
        hD.isClosed hdis hxe hxD)).elim
  have hdis : Disjoint (D \ {v}) Γ.U := disjoint_left.mpr fun x hxD hxΓ =>
    hxD.2 (hΓD ⟨hxΓ, hxD.1⟩)
  have hF : IsOArc F := hbd ▸ hD.isOArc_discBd
  obtain ⟨u, hu⟩ := ((infinite_of_isOArc hF).sdiff (finite_singleton v)).nonempty
  have huD : u ∈ D \ {v} := ⟨Surface.discBd_subset D (hbd.symm ▸ hu.1), hu.2⟩
  have hsubset : D \ {v} ⊆ r := subset_region hr
    (disc_sdiff_boundary_point_isPreconnected hD (hbd.symm ▸ hvF)) hdis huD (hFr hu)
  intro x hxD
  by_cases hxv : x = v
  · exact Or.inr hxv
  · exact Or.inl (hsubset ⟨hxD, hxv⟩)

omit [T2Space S] in
/-- The closure of a radial spoke lies in its region with its old
end restored. -/
theorem closure_spoke_subset_region_vertex (hS : IsClosedSurface S)
    {Γ K : Drawing S} (htwo : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {g r : Set S} {v u : S} (hg : g ∈ K.E) (hr : r ∈ Γ.R) (hur : u ∈ r)
    (hcap : closure g ∩ K.V = {v, u}) : closure g ⊆ r ∪ {v} := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hucl : u ∈ closure g := (hcap.superset (Or.inr rfl)).1
  obtain ⟨y, hyr, hyg⟩ := mem_closure_iff.mp hucl r (region_isOpen hr) hur
  have hgr : g ⊆ r := subset_region hr hg.2.2.1.isConnected.isPreconnected
    (spoke_disjoint ⟨htwo, hK⟩ hg) hyg hyr
  intro x hx
  by_cases hxV : x ∈ K.V
  · rcases hcap.subset ⟨hx, hxV⟩ with hxv | hxu
    · exact Or.inr hxv
    · exact Or.inl (hxu ▸ hur)
  · exact Or.inl (hgr ((K.closure_diff_V hg).subset ⟨hx, hxV⟩))

/-- Corrected parallel-spoke claim for XII (7.3), page 261: after
selected one-vertex insides containing old edges have been removed,
no two radial spokes at the vertex have the same other end. -/
theorem no_parallel_spokes_of_no_selected_edge_inside [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsRespectfulDrawingTangle Γ θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K) {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell)
    (hno : ∀ D F : Set S, IsClosedDisc D → IsOArc F → subBd D = F →
      (PaintingOrDrawing.drawing Γ).IsNormal F → F ∩ Γ.V = {v} →
      ((PaintingOrDrawing.drawing Γ).inter D, (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      ∀ e ∈ Γ.E, ¬ e ⊆ D)
    {g h r : Set S} {u : S} (hg : g ∈ K.E) (hh : h ∈ K.E) (hgh : g ≠ h)
    (hr : r ∈ Γ.R) (hur : u ∈ r) (huK : u ∈ K.V)
    (hcapg : closure g ∩ K.V = {v, u}) (hcaph : closure h ∩ K.V = {v, u}) : False := by
  let F := closure g ∪ closure h
  have hvu : v ≠ u := fun h => region_subset hr (h ▸ hur) (Γ.V_subset_U hv)
  have hLg := isLine_closure hg hvu hcapg
  have hLh := isLine_closure hh hvu hcaph
  have hF : IsOArc F := isOArc_union hLg hLh fun x hx =>
    hcapg.subset ⟨hx.1, closure_inter_subset_V hg hh hgh hx⟩
  have hFZ : F ⊆ r ∪ {v} := union_subset
    (closure_spoke_subset_region_vertex hS hT.1 hK hg hr hur hcapg)
    (closure_spoke_subset_region_vertex hS hT.1 hK hh hr hur hcaph)
  have hvF : v ∈ F := Or.inl (hcapg.superset (Or.inl rfl)).1
  have hn : (PaintingOrDrawing.drawing Γ).IsNormal F := by
    rintro x ⟨hxF, hxΓ⟩
    rcases hFZ hxF with hxr | hxv
    · exact (region_subset hr hxr hxΓ).elim
    · exact hxv ▸ hv
  have hFV : F ∩ Γ.V = {v} := by
    apply Subset.antisymm
    · rintro x ⟨hxF, hxV⟩
      exact (hFZ hxF).resolve_left (fun hxr => region_subset hr hxr (Γ.V_subset_U hxV))
    · rintro x hx
      have hxv := mem_singleton_iff.mp hx
      subst x
      exact ⟨hvF, hv⟩
  have hFsmall : (F ∩ Γ.V).ncard < θ := by
    rw [hFV, ncard_singleton]
    omega
  obtain ⟨D, hD, hbd, hm⟩ := hT.2.2.2 F hF hn hFsmall
  have hVD := vertices_in_selected_vertex_disc hS hT.2.1 htwo hD hbd hn hFV hm
  have hDb : discBd D = F := (IsClosedDisc.frontier_eq_discBd hS hD).symm.trans
    ((subBd_eq_frontier D).symm.trans hbd)
  have hDr : D ⊆ r ∪ {v} := disc_subset_region_vertex_of_no_edges hS hD hDb hvF hn hVD hr
    (fun x hx => (hFZ hx.1).resolve_right hx.2) (hno D F hD hF hbd hn hFV hm)
  exact hK.2.2.2.2.2 g hg h hh hgh v hv r hr u ⟨hur, huK⟩ hcapg hcaph ⟨D, hD, hDr, hbd⟩

end GraphMinor.GM12
