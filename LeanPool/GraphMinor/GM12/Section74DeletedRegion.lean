/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73DeletedRegions
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM07.Section3

/-!
# The region of a deleted vertex in XII (7.4)

In the base case of XII (7.4), pages 262--263, the drawing after
vertex deletion is two-cell. All removed edges belong to the
region containing that vertex: each edge together with the
vertex is connected and misses the remaining drawing. Every old
atom contained in this region is the deleted vertex, an incident
edge, or an incident region. The metric's incidence bounds put their
old distance to the deleted vertex at most two. This proves assertions (i) and
(iv) in this base case.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14 GM10

/-- An incident edge, with the deleted vertex restored, lies in
the region containing that vertex after deletion. -/
theorem incident_edge_subset_deleted_vertex_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {v : S} (hv : v ∈ Γ.V)
    {r : Set S} (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r)
    {e : Set S} (he : e ∈ Γ.E) (hve : v ∈ closure e) : e ⊆ r := by
  have hpre : IsPreconnected (insert v e) :=
    he.2.2.1.isConnected.isPreconnected.subset_closure (subset_insert v e)
      (insert_subset hve subset_closure)
  have hdis : Disjoint (insert v e) (deleteVertices Γ {v}).U := by
    apply disjoint_left.mpr
    intro x hx hxU
    rcases hx with rfl | hxe
    · exact region_subset hr hvr hxU
    · have heNew : e ∉ (deleteVertices Γ {v}).E := by
        intro h
        have hdis := (deleteVertices_E Γ {v}).subset h
        exact disjoint_left.mp hdis.2 ⟨hve, hv⟩ rfl
      have hxV : x ∉ Γ.V := (he.2.1 hxe).2
      have hxV' : x ∉ (deleteVertices Γ {v}).V :=
        fun h => hxV ((deleteVertices_isSubdrawing Γ {v}).1 h)
      obtain ⟨f, hf, hxf⟩ := (deleteVertices Γ {v}).exists_edge_of_mem hxU hxV'
      have hef : e = f := Γ.edge_eq_of_mem he ((deleteVertices_isSubdrawing Γ {v}).2 hf) hxe hxf
      exact heNew (hef.symm ▸ hf)
  exact (subset_insert v e).trans (subset_region hr hpre hdis (mem_insert v e) hvr)

/-- Assertion (i) of XII (7.4) in its two-cell-deletion base case.
The containment itself needs no two-cell hypothesis. -/
theorem drawing_subset_delete_union_vertex_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ : Drawing S} {v : S} (hv : v ∈ Γ.V)
    {r : Set S} (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r) :
    Γ.U ⊆ (deleteVertices Γ {v}).U ∪ r := by
  intro x hx
  by_cases hxNew : x ∈ (deleteVertices Γ {v}).U
  · exact Or.inl hxNew
  · right
    rcases mem_deleted_vertex_or_incident_edge hx hxNew with rfl | ⟨e, he, hxe, hve⟩
    · exact hvr
    · exact incident_edge_subset_deleted_vertex_region hv hr hvr he hve hxe

/-- Assertion (iv) of XII (7.4), pages 262--263, when the deleted
drawing is two-cell. Old atoms within its merged region have
old distance at most two from the deleted vertex. -/
theorem atom_in_deleted_vertex_region_distance_le_two
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {v : S} (hv : v ∈ Γ.V) {r : Set S}
    (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r)
    {a : Set S} (ha : a ∈ Γ.A) (har : a ⊆ r) : d a {v} ≤ 2 := by
  have h91 := gm15_theorem_9_1 Γ θ T d hS inferInstance hd
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  rcases ha with (⟨u, hu, rfl⟩ | he) | hs
  · have huv : u = v := by
      by_contra hne
      have huNew : u ∈ (deleteVertices Γ {v}).V := (deleteVertices_V Γ {v}).symm ▸ ⟨hu, hne⟩
      exact region_subset hr (har (mem_singleton u)) ((deleteVertices Γ {v}).V_subset_U huNew)
    subst u
    rw [h91.2.1 {v} hvA]
    exact Nat.zero_le _
  · obtain ⟨x, hxe⟩ := he.1
    have hxnot : x ∉ (deleteVertices Γ {v}).U := region_subset hr (har hxe)
    rcases mem_deleted_vertex_or_incident_edge (he.2.1 hxe).1 hxnot with hxv | ⟨f, hf, hxf, hvf⟩
    · exact ((he.2.1 hxe).2 (hxv.symm ▸ hv)).elim
    · have hef : a = f := Γ.edge_eq_of_mem he hf hxe hxf
      have hve : v ∈ closure a := hef.symm ▸ hvf
      rw [h91.2.2.2.1 a (Or.inl (Or.inr he)) {v} hvA]
      exact h91.2.2.2.2.2.2 v hv a he hve
  · have hE : Γ.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hd.1.2.1 hθ
    obtain ⟨x, hxa⟩ := region_nonempty hs
    have hnear := deleted_vertex_mem_closure_of_region_meeting hS hv hs hr hvr ⟨x, hxa, har hxa⟩
    rw [h91.2.2.2.1 a (Or.inr hs) {v} hvA]
    exact (h91.2.2.2.2.2.1 hE v hv a hs hnear).trans (by decide)

end GraphMinor.GM12
