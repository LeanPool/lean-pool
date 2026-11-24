/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section76
import LeanPool.GraphMinor.GM11.GlueFaces
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM11.Section7

/-!
# Gluing disc regions while deleting an edge

The cellularity assertion in the base case of XII (7.4), pages
262--263, requires gluing the old disc regions around the vertex.
Here an edge between two distinct disc regions is removed. Their
union with the open edge is a disc by the proved gluing theorem.
Its boundary remains in the drawing after edge deletion, so this
union is precisely the new region. Every other new region misses
the removed edge and was already an old region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A nonempty open connected set missing a drawing and with
its remaining closure in the drawing is a whole region. -/
theorem mem_regions_of_open_connected_closure_subset
    {S : Type*} [TopologicalSpace S] {K : Drawing S} {A : Set S}
    (hA : IsOpen A) (hc : IsConnected A) (hdis : Disjoint A K.U)
    (hcl : closure A ⊆ A ∪ K.U) : A ∈ K.R := by
  obtain ⟨x, hx⟩ := hc.1
  obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp hdis hx)
  have hAr : A ⊆ r := subset_region hr hc.2 hdis hx hxr
  have hcov : r ⊆ A ∪ (closure A)ᶜ := by
    intro y hyr
    by_cases hycl : y ∈ closure A
    · exact Or.inl ((hcl hycl).resolve_right (region_subset hr hyr))
    · exact Or.inr hycl
  have hrA : r ⊆ A := (region_isPreconnected hr).subset_left_of_subset_union hA
    isClosed_closure.isOpen_compl
    (disjoint_left.mpr fun y hya hyc => hyc (subset_closure hya)) hcov ⟨x, hxr, hx⟩
  exact (Subset.antisymm hrA hAr) ▸ hr

/-- Removing an edge between two distinct open-disc regions
merges them into exactly their union with that edge. -/
theorem merged_region_deleteEdge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S} {e p q : Set S}
    (he : e ∈ K.E) (hp : p ∈ K.R) (hq : q ∈ K.R) (hpq : p ≠ q)
    (hdp : IsOpenDisc p) (hdq : IsOpenDisc q)
    (hep : e ⊆ closure p) (heq : e ⊆ closure q) :
    p ∪ q ∪ e ∈ (K.deleteEdge e).R ∧ IsOpenDisc (p ∪ q ∪ e) := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hdisc := theorem_glue_regions hS he hp hq hpq hdp hdq hep heq
  refine ⟨mem_regions_of_open_connected_closure_subset hdisc.1
    hdisc.isPathConnected.isConnected ?_ ?_, hdisc⟩
  · apply disjoint_left.mpr
    intro x hx hxU
    rw [deleteEdge_U K he] at hxU
    rcases hx with (hxp | hxq) | hxe
    · exact region_subset hp hxp hxU.1
    · exact region_subset hq hxq hxU.1
    · exact hxU.2 hxe
  · intro x hx
    rw [closure_union, closure_union] at hx
    have hxOld : x ∈ (p ∪ q ∪ e) ∪ K.U := by
      rcases hx with (hxp | hxq) | hxe
      · rcases closure_region_subset hp hxp with h | h
        · exact Or.inl (Or.inl (Or.inl h))
        · exact Or.inr h
      · rcases closure_region_subset hq hxq with h | h
        · exact Or.inl (Or.inl (Or.inr h))
        · exact Or.inr h
      · exact Or.inr (K.closure_subset_U he hxe)
    rcases hxOld with hxA | hxK
    · exact Or.inl hxA
    · by_cases hxe : x ∈ e
      · exact Or.inl (Or.inr hxe)
      · exact Or.inr ((deleteEdge_U K he).symm ▸ ⟨hxK, hxe⟩)

/-- Deleting an edge between two distinct regions preserves a
 two-cell drawing. The merged region is a disc by gluing, and
 every other region was already an old disc region. -/
theorem isTwoCell_deleteEdge_of_distinct_regions
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {K : Drawing S}
    (hK : (PaintingOrDrawing.drawing K).IsTwoCell) {e p q : Set S}
    (he : e ∈ K.E) (hp : p ∈ K.R) (hq : q ∈ K.R) (hpq : p ≠ q)
    (hep : e ⊆ closure p) (heq : e ⊆ closure q) :
    (PaintingOrDrawing.drawing (K.deleteEdge e)).IsTwoCell := by
  obtain ⟨hmerge, hdmerge⟩ := merged_region_deleteEdge hS he hp hq hpq (hK.2 p hp)
    (hK.2 q hq) hep heq
  refine ⟨inferInstance, ?_⟩
  intro r hr
  by_cases hmeet : (r ∩ e).Nonempty
  · obtain ⟨x, hxr, hxe⟩ := hmeet
    have hreq : r = p ∪ q ∪ e := region_eq_of_mem hr hmerge hxr (Or.inr hxe)
    exact hreq.symm ▸ hdmerge
  · obtain ⟨x, hxr⟩ := region_nonempty hr
    have hxK : x ∉ K.U := by
      intro hx
      have hxn := region_subset hr hxr
      rw [deleteEdge_U K he] at hxn
      exact hxn ⟨hx, fun hxe => hmeet ⟨x, hxr, hxe⟩⟩
    obtain ⟨s, hs, hxs⟩ := exists_region_of_notMem hxK
    have hrs : r ⊆ s := subset_region hs (region_isPreconnected hr)
      (disjoint_left.mpr fun y hyr hyK => by
        have hyN := region_subset hr hyr
        rw [deleteEdge_U K he] at hyN
        exact hyN ⟨hyK, fun hye => hmeet ⟨y, hyr, hye⟩⟩) hxr hxs
    have hsr : s ⊆ r := subset_region hr (region_isPreconnected hs)
      (disjoint_left.mpr fun y hys hyN => region_subset hs hys
        ((deleteEdge_isSubdrawing K e).U_subset hyN)) hxs hxr
    exact (Subset.antisymm hrs hsr).symm ▸ hK.2 s hs

end GraphMinor.GM12
