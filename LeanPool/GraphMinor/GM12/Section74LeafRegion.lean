/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section74DeletedRegion
import LeanPool.GraphMinor.GM12.Section74DiscRegion
import LeanPool.GraphMinor.GM11.LeafNbhd
import LeanPool.GraphMinor.GM11.Regions

/-!
# The merged region at a leaf

In the last gluing step for the base case of XII (7.4), pages
262--263, the vertex has one incident edge. The leaf-neighbourhood
lemma shows that just one old region reaches the vertex. Deleting
the leaf therefore enlarges exactly that region by the open edge
and the leaf endpoint. This identifies the set for the final
open-disc assertion.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Only one region of a drawing can reach a leaf vertex. -/
theorem regions_eq_of_leaf_vertex
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {e : Set S} (he : e ∈ Γ.E)
    {u v : S} (huv : u ≠ v) (hcap : closure e ∩ Γ.V = {u, v})
    (hL : IsLineWithEnds (closure e) u v)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f)
    {r s : Set S} (hr : r ∈ Γ.R) (hs : s ∈ Γ.R)
    (hvr : v ∈ closure r) (hvs : v ∈ closure s) : r = s := by
  obtain ⟨Z, hZ, hvZ, hjoin⟩ := exists_leaf_nbhd hS Γ he huv hcap hL hleaf isOpen_univ (mem_univ v)
  obtain ⟨a, haZ, har⟩ := mem_closure_iff.mp hvr Z hZ hvZ
  obtain ⟨b, hbZ, hbs⟩ := mem_closure_iff.mp hvs Z hZ hvZ
  obtain ⟨A, hA, hdis, haA, hbA, _⟩ := hjoin a haZ (region_subset hr har) b hbZ
    (region_subset hs hbs)
  have hbR : b ∈ r := subset_region hr hA hdis haA har hbA
  exact region_eq_of_mem hr hs hbR hbs

/-- Deleting a leaf enlarges its incident region by precisely
the open edge and the leaf endpoint. -/
theorem deleted_leaf_region_eq
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {e : Set S} (he : e ∈ Γ.E)
    {u v : S} (huv : u ≠ v) (hcap : closure e ∩ Γ.V = {u, v})
    (hL : IsLineWithEnds (closure e) u v)
    (hleaf : ∀ f ∈ Γ.E, f ≠ e → v ∉ closure f)
    {r r' : Set S} (hr : r ∈ Γ.R) (hvr : v ∈ closure r)
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r') :
    r' = r ∪ e ∪ {v} := by
  have hvCap : v ∈ closure e ∩ Γ.V := hcap.symm ▸ (Or.inr rfl : v ∈ ({u, v} : Set S))
  have hv : v ∈ Γ.V := hvCap.2
  have hrr' := region_subset_of_closure_mem_subdrawing_region hS
    (deleteVertices_isSubdrawing Γ {v}) hr hr' hvr hvr'
  apply Subset.antisymm
  · intro x hxr'
    by_cases hxU : x ∈ Γ.U
    · rcases mem_deleted_vertex_or_incident_edge hxU (region_subset hr' hxr') with rfl | ⟨f, hf,
        hxf, hvf⟩
      · exact Or.inr rfl
      · have hfe : f = e := by
          by_contra hne
          exact hleaf f hf hne hvf
        exact Or.inl (Or.inr (hfe ▸ hxf))
    · obtain ⟨s, hs, hxs⟩ := exists_region_of_notMem hxU
      have hvs := deleted_vertex_mem_closure_of_region_meeting hS hv hs hr' hvr' ⟨x, hxs, hxr'⟩
      have hsr : s = r := regions_eq_of_leaf_vertex hS he huv hcap hL hleaf hs hr hvs hvr
      exact Or.inl (Or.inl (hsr ▸ hxs))
  · intro x hx
    rcases hx with (hxr | hxe) | rfl
    · exact hrr' hxr
    · exact incident_edge_subset_deleted_vertex_region hv hr' hvr' he hvCap.1 hxe
    · exact hvr'

end GraphMinor.GM12
