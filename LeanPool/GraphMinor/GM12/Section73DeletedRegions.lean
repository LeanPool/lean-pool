/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73Tangle
public import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.Surface.PlaneSeparation

/-!
# Regions meeting a deleted vertex

In XII (7.3), page 261, the radial hubs that merge into the new
region are the hubs of old regions incident with the deleted vertex.
If an old region meets the new region containing the vertex, a
connected set crosses its frontier. A frontier point missing from
the deleted drawing is either the deleted vertex or belongs to a
deleted incident edge. In both cases the vertex lies in the closure
of the old region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A point of the original drawing omitted by vertex deletion is
the deleted vertex or belongs to an edge incident with it. This is
used to locate the merged regions in XII (7.3), page 261. -/
theorem mem_deleted_vertex_or_incident_edge
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {v x : S}
    (hx : x ∈ Γ.U) (hxnot : x ∉ (deleteVertices Γ {v}).U) :
    x = v ∨ ∃ e ∈ Γ.E, x ∈ e ∧ v ∈ closure e := by
  by_cases hxV : x ∈ Γ.V
  · left
    by_contra hxv
    apply hxnot
    apply (deleteVertices Γ {v}).V_subset_U
    rw [deleteVertices_V]
    exact ⟨hxV, hxv⟩
  · right
    rw [Γ.U_eq] at hx
    rcases hx with hxV' | hx
    · exact False.elim (hxV hxV')
    obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
    have hxe' : x ∈ e := (Γ.closure_diff_V he).subset ⟨hxe, hxV⟩
    refine ⟨e, he, hxe', ?_⟩
    by_contra hve
    have he' : e ∈ (deleteVertices Γ {v}).E := by
      rw [deleteVertices_E]
      exact ⟨he, disjoint_left.mpr fun y hy hyv => hve (hyv ▸ hy.1)⟩
    exact hxnot ((deleteVertices Γ {v}).closure_subset_U he' hxe)

/-- Every old region that meets the new region of the deleted
vertex is incident with that vertex. This identifies the hubs merged
by the radial-star contraction in XII (7.3), page 261. -/
theorem deleted_vertex_mem_closure_of_region_meeting
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {v : S} (hv : v ∈ Γ.V)
    {r r' : Set S} (hr : r ∈ Γ.R) (hr' : r' ∈ (deleteVertices Γ {v}).R)
    (hvr' : v ∈ r') (hmeet : (r ∩ r').Nonempty) : v ∈ closure r := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨x, hxr, hxr'⟩ := hmeet
  have hvr : v ∉ r := fun h => region_subset hr h (Γ.V_subset_U hv)
  obtain ⟨y, hyr', hyfr⟩ := inter_frontier_nonempty_of_isPreconnected
    (region_isPreconnected hr') ⟨x, hxr', hxr⟩ ⟨v, hvr', hvr⟩
  have hycl : y ∈ closure r := hyfr.1
  have hyU : y ∈ Γ.U := by
    rcases closure_region_subset hr hycl with hyr | hyU
    · exact False.elim (hyfr.2 ((region_isOpen hr).interior_eq.symm ▸ hyr))
    · exact hyU
  rcases mem_deleted_vertex_or_incident_edge hyU (region_subset hr' hyr') with rfl | ⟨e, he, hye,
    hve⟩
  · exact hycl
  · have hesub : e ⊆ closure r := edge_subset_closure_of_incident hS he hr ⟨y, hye, hycl⟩
    exact closure_minimal hesub isClosed_closure hve

/-- An old region not incident with the deleted vertex remains a
region. This is the unchanged-region part of XII (7.3), page 261. -/
theorem region_deleteVertices_of_not_incident
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {v : S}
    {r : Set S} (hr : r ∈ Γ.R) (hvnot : v ∉ closure r) :
    r ∈ (deleteVertices Γ {v}).R := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hclosure : closure r ⊆ r ∪ (deleteVertices Γ {v}).U := by
    intro y hycl
    rcases closure_region_subset hr hycl with hyr | hyU
    · exact Or.inl hyr
    · by_cases hynew : y ∈ (deleteVertices Γ {v}).U
      · exact Or.inr hynew
      · exfalso
        rcases mem_deleted_vertex_or_incident_edge hyU hynew with rfl | ⟨e, he, hye, hve⟩
        · exact hvnot hycl
        · exact hvnot (closure_minimal
            (edge_subset_closure_of_incident hS he hr ⟨y, hye, hycl⟩) isClosed_closure hve)
  obtain ⟨r', hr', hsub⟩ := exists_region_superset (deleteVertices_isSubdrawing Γ {v}) hr
  have hcov : r' ⊆ r ∪ (closure r)ᶜ := by
    intro y hyr'
    by_cases hycl : y ∈ closure r
    · rcases hclosure hycl with hyr | hyU
      · exact Or.inl hyr
      · exact False.elim (region_subset hr' hyr' hyU)
    · exact Or.inr hycl
  obtain ⟨x, hxr⟩ := region_nonempty hr
  have hback : r' ⊆ r := (region_isPreconnected hr').subset_left_of_subset_union
    (region_isOpen hr) isClosed_closure.isOpen_compl
    (disjoint_left.mpr fun _ hy hyn => hyn (subset_closure hy)) hcov ⟨x, hsub hxr, hxr⟩
  exact (subset_antisymm hsub hback) ▸ hr'

/-- A region after deletion that does not contain the deleted
vertex was already a region before deletion. This gives the other
region hubs in XII (7.3), page 261. -/
theorem deleted_region_of_not_mem_vertex
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {v : S} (hv : v ∈ Γ.V)
    {s : Set S} (hs : s ∈ (deleteVertices Γ {v}).R) (hvs : v ∉ s) : s ∈ Γ.R := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨x, hxs, hxΓ⟩ := exists_notMem_U (Γ := Γ) hS (region_isOpen hs) (region_nonempty hs)
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem hxΓ
  have hvnot : v ∉ closure r := by
    intro hvcl
    have hpre : IsPreconnected (insert v r) := (region_isPreconnected hr).subset_closure
      (subset_insert v r) (by
        intro y hy
        rcases hy with rfl | hyr
        · exact hvcl
        · exact subset_closure hyr)
    have hdelete := deleteVertices_isSubdrawing Γ {v}
    have hvnotU : v ∉ (deleteVertices Γ {v}).U := by
      intro hvU
      have hvV := (isSubdrawing_U_inter_V hdelete).subset ⟨hvU, hv⟩
      exact ((deleteVertices_V Γ {v}).subset hvV).2 rfl
    have hdis : Disjoint (insert v r) (deleteVertices Γ {v}).U := by
      apply disjoint_left.mpr
      rintro y (rfl | hyr) hyU
      · exact hvnotU hyU
      · exact region_subset hr hyr (hdelete.U_subset hyU)
    have hsub := subset_region hs hpre hdis (Or.inr hxr) hxs
    exact hvs (hsub (Or.inl rfl))
  have hrnew := region_deleteVertices_of_not_incident hS hr hvnot
  have heq : r = s := region_eq_of_mem hrnew hs hxr hxs
  exact heq ▸ hr

end GraphMinor.GM12
