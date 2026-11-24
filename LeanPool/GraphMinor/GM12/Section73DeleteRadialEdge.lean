/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Section4c
import LeanPool.GraphMinor.GM11.GlueFaces
import LeanPool.GraphMinor.GM11.Walks

/-!
# Deleting an edge between distinct radial regions

The cleanup in XII (7.3), page 261, removes one boundary edge of an
empty parallel-edge region. Deleting an edge between two distinct
regions merges just those regions. Their union with the edge is an
open disc, so the drawing remains two-cell. Other regions stay
unchanged because an edge is incident with at most two regions.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Edge deletion retains every vertex, including isolated ones.
This keeps the radial hubs fixed during the cleanup in XII (7.3). -/
theorem deleteEdge_vertices_eq
    {S : Type*} [TopologicalSpace S] [T2Space S] (H : Drawing S) (e : Set S) :
    (H.deleteEdge e).V = H.V := by
  apply Subset.antisymm (deleteEdge_isSubdrawing H e).1
  intro x hx
  exact Or.inl ⟨hx, hx⟩

/-- Deleting a radial edge preserves the intersection with the
original drawing because all its vertices are retained. This is
condition (i) during the cleanup of XII (7.3), page 261. -/
theorem drawing_inter_deleteEdge_eq
    {S : Type*} [TopologicalSpace S] [T2Space S] {Γ H : Drawing S}
    (hcap : Γ.U ∩ H.U = Γ.V) (hV : Γ.V ⊆ H.V) (e : Set S) :
    Γ.U ∩ (H.deleteEdge e).U = Γ.V := by
  apply Subset.antisymm
  · rintro x ⟨hxΓ, hxH⟩
    exact hcap.subset ⟨hxΓ, (deleteEdge_isSubdrawing H e).U_subset hxH⟩
  · intro x hxΓ
    refine ⟨Γ.V_subset_U hxΓ, (H.deleteEdge e).V_subset_U ?_⟩
    rw [deleteEdge_vertices_eq]
    exact hV hxΓ

/-- Deleting an edge between two distinct disc regions changes
only those two regions, replacing them by their union with the edge.
This is the region calculation for the cleanup in XII (7.3), page 261. -/
theorem region_deleteEdge_cases
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H : Drawing S} {e p q : Set S}
    (he : e ∈ H.E) (hp : p ∈ H.R) (hq : q ∈ H.R) (hpq : p ≠ q)
    (hdp : IsOpenDisc p) (hdq : IsOpenDisc q)
    (hep : e ⊆ closure p) (heq : e ⊆ closure q)
    {r : Set S} (hr : r ∈ (H.deleteEdge e).R) :
    r = p ∪ q ∪ e ∨ (r ∈ H.R ∧ r ≠ p ∧ r ≠ q) := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let A : Set S := p ∪ q ∪ e
  let B : Set S := ⋃ t ∈ {t ∈ H.R | t ≠ p ∧ t ≠ q}, t
  have hA : IsOpenDisc A := theorem_glue_regions hS he hp hq hpq hdp hdq hep heq
  have hB : IsOpen B := isOpen_biUnion fun t ht => region_isOpen ht.1
  have hother : ∀ t ∈ H.R, t ≠ p → t ≠ q → t ∈ (H.deleteEdge e).R := by
    intro t ht htp htq
    apply region_deleteEdge_of_not_incident he ht
    apply disjoint_left.mpr
    intro x hxe hxcl
    have het := edge_subset_closure_of_incident hS he ht ⟨x, hxe, hxcl⟩
    rcases region_incident_two hS he hp hq ht hep heq het with h | h | h
    · exact hpq h
    · exact htp h.symm
    · exact htq h.symm
  have hdisAB : Disjoint A B := by
    apply disjoint_left.mpr
    intro x hxA hxB
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxB
    rcases hxA with (hxp | hxq) | hxe
    · exact ht.2.1 (region_eq_of_mem ht.1 hp hxt hxp)
    · exact ht.2.2 (region_eq_of_mem ht.1 hq hxt hxq)
    · exact region_subset ht.1 hxt (H.closure_subset_U he (subset_closure hxe))
  have hcov : (H.deleteEdge e).Uᶜ ⊆ A ∪ B := by
    intro x hx
    by_cases hxH : x ∈ H.U
    · have hxe : x ∈ e := by
        by_contra hxn
        apply hx
        rw [deleteEdge_U H he]
        exact ⟨hxH, hxn⟩
      exact Or.inl (Or.inr hxe)
    · obtain ⟨t, ht, hxt⟩ := exists_region_of_notMem hxH
      by_cases htp : t = p
      · exact Or.inl (Or.inl (Or.inl (htp ▸ hxt)))
      · by_cases htq : t = q
        · exact Or.inl (Or.inl (Or.inr (htq ▸ hxt)))
        · exact Or.inr (mem_iUnion₂.mpr ⟨t, ⟨ht, htp, htq⟩, hxt⟩)
  have hrcov : r ⊆ A ∪ B := fun _ hx => hcov (region_subset hr hx)
  by_cases hmeet : (r ∩ A).Nonempty
  · left
    obtain ⟨x, hxr, hxA⟩ := hmeet
    have hrA : r ⊆ A := (region_isPreconnected hr).subset_left_of_subset_union
      hA.1 hB hdisAB hrcov ⟨x, hxr, hxA⟩
    have hAdis : Disjoint A (H.deleteEdge e).U := by
      apply disjoint_left.mpr
      intro y hyA hyH
      rw [deleteEdge_U H he] at hyH
      rcases hyA with (hyp | hyq) | hye
      · exact region_subset hp hyp hyH.1
      · exact region_subset hq hyq hyH.1
      · exact hyH.2 hye
    exact Subset.antisymm hrA
      (subset_region hr (isPreconnected_of_isOpenDisc hA) hAdis hxA hxr)
  · right
    obtain ⟨x, hxr⟩ := region_nonempty hr
    have hxB : x ∈ B := (hrcov hxr).resolve_left fun hxA => hmeet ⟨x, hxr, hxA⟩
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hxB
    have htnew := hother t ht.1 ht.2.1 ht.2.2
    have hrt : r = t := region_eq_of_mem hr htnew hxr hxt
    exact hrt.symm ▸ ht

/-- Removing an edge between distinct regions preserves the
two-cell property. This supplies the deletion step in the empty-disc
cleanup of XII (7.3), page 261. -/
theorem isTwoCell_deleteEdge_of_distinct_regions
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H : Drawing S}
    (hH : (PaintingOrDrawing.drawing H).IsTwoCell) {e p q : Set S}
    (he : e ∈ H.E) (hp : p ∈ H.R) (hq : q ∈ H.R) (hpq : p ≠ q)
    (hep : e ⊆ closure p) (heq : e ⊆ closure q) :
    (PaintingOrDrawing.drawing (H.deleteEdge e)).IsTwoCell := by
  refine ⟨hH.1, ?_⟩
  intro r hr
  rcases region_deleteEdge_cases hS he hp hq hpq (hH.2 p hp) (hH.2 q hq) hep heq hr with h | h
  · rw [h]
    exact theorem_glue_regions hS he hp hq hpq (hH.2 p hp) (hH.2 q hq) hep heq
  · exact hH.2 r h.1

/-- If one merged region contains no edge of the other drawing,
the deletion preserves the condition that every region contains at
most one such edge. This is the edge invariant in the cleanup of
XII (7.3), page 261. -/
theorem region_edge_unique_deleteEdge
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ H : Drawing S}
    (hH : (PaintingOrDrawing.drawing H).IsTwoCell) {e p q : Set S}
    (he : e ∈ H.E) (hp : p ∈ H.R) (hq : q ∈ H.R) (hpq : p ≠ q)
    (hep : e ⊆ closure p) (heq : e ⊆ closure q)
    (hdis : ∀ g ∈ Γ.E, Disjoint g H.U)
    (hempty : ∀ g ∈ Γ.E, ¬ g ⊆ p)
    (hunique : ∀ r ∈ H.R, ∀ a ∈ Γ.E, ∀ b ∈ Γ.E, a ⊆ r → b ⊆ r → a = b) :
    ∀ r ∈ (H.deleteEdge e).R, ∀ a ∈ Γ.E, ∀ b ∈ Γ.E, a ⊆ r → b ⊆ r → a = b := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  intro r hr a ha b hb har hbr
  rcases region_deleteEdge_cases hS he hp hq hpq (hH.2 p hp) (hH.2 q hq) hep heq hr with hrA | hrOld
  · have hsubq : ∀ g ∈ Γ.E, g ⊆ p ∪ q ∪ e → g ⊆ q := by
      intro g hg hgA
      have hsubpq : g ⊆ p ∪ q := by
        intro x hxg
        rcases hgA hxg with hxpq | hxe
        · exact hxpq
        · exact False.elim (disjoint_left.mp (hdis g hg) hxg
            (H.closure_subset_U he (subset_closure hxe)))
      have hpqd : Disjoint p q := disjoint_left.mpr fun x hxp hxq =>
        hpq (region_eq_of_mem hp hq hxp hxq)
      exact ((hg.2.2.1.isConnected.isPreconnected).subset_or_subset
        (region_isOpen hp) (region_isOpen hq) hpqd hsubpq).resolve_left (hempty g hg)
    exact hunique q hq a ha b hb (hsubq a ha (hrA ▸ har)) (hsubq b hb (hrA ▸ hbr))
  · exact hunique r hrOld.1 a ha b hb har hbr

end GraphMinor.GM12
