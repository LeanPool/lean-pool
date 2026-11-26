/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM10.TangleLemmas

/-!
# The two cuts along a zone boundary

For the planar Menger argument in XVI (8.1), cut along the inner and
outer boundary circles. Vertices on a circle belong to both sides.
Edges on it may be assigned to either side. These cuts let us move an
arbitrary boundary separator into the closed annulus without adding
separator vertices.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- Restriction to a closed set preserves the ends of every retained edge. -/
theorem drawing_closed_inter_le (H : Drawing S) {A : Set S} (hA : IsClosed A) :
    (PaintingOrDrawing.drawing H).inter A ≤ H.toHypergraph := by
  refine ⟨inter_subset_left, fun _ h => h.1, ?_⟩
  intro e he
  ext x
  change (e ∈ H.E ∧ x ∈ H.V ∧ x ∈ closure e) ↔
    (e ∈ H.E ∧ x ∈ H.V ∧ x ∈ closure e) ∧ e ⊆ A ∧ x ∈ A
  constructor
  · intro hx
    exact ⟨hx, he.2, closure_minimal he.2 hA hx.2.2⟩
  · exact fun h => h.1

private theorem separation_of_cover_deleting_edges {α β : Type*}
    {G C D : Hypergraph α β} (hC : C ≤ G) (hD : D ≤ G)
    (hV : C.vertexSet ∪ D.vertexSet = G.vertexSet) (hE : C.edgeSet ∪ D.edgeSet = G.edgeSet) :
    G.IsSeparation C (D.deleteEdges C.edgeSet) := by
  rw [isSeparation_iff_of_le hC ((deleteEdges_le D C.edgeSet).trans hD)]
  refine ⟨hV, ?_, ?_⟩
  · change C.edgeSet ∪ (D.edgeSet \ C.edgeSet) = G.edgeSet
    rw [← hE]
    ext x
    simp only [mem_union, mem_sdiff]
    tauto
  · change C.edgeSet ∩ (D.edgeSet \ C.edgeSet) = ∅
    exact Set.disjoint_iff_inter_eq_empty.mp Set.disjoint_sdiff_right

/-- The cuts along the boundary of a zone, assigning boundary edges
first to the inside and then to the outside. These are the two fixed
cuts used to uncross a separator in XVI (8.1), Claim (10). -/
theorem zone_cut_separations {H : Drawing S} {d : Set S → Set S → ℕ}
    {γ : ℕ} {z Λ : Set S} (hZone : IsLambdaZoneAround H d γ z Λ) :
    H.toHypergraph.IsSeparation
      ((PaintingOrDrawing.drawing H).inter (closure Λ))
      (((PaintingOrDrawing.drawing H).inter (univ \ Λ)).deleteEdges
        ((PaintingOrDrawing.drawing H).inter (closure Λ)).edgeSet) ∧
    H.toHypergraph.IsSeparation
      (((PaintingOrDrawing.drawing H).inter (closure Λ)).deleteEdges
        ((PaintingOrDrawing.drawing H).inter (univ \ Λ)).edgeSet)
      ((PaintingOrDrawing.drawing H).inter (univ \ Λ)) := by
  have hC := drawing_closed_inter_le H (A := closure Λ) isClosed_closure
  have hD := drawing_closed_inter_le H (isClosed_univ.sdiff hZone.isOpenDisc.1)
  have hV : ((PaintingOrDrawing.drawing H).inter (closure Λ)).vertexSet ∪
      ((PaintingOrDrawing.drawing H).inter (univ \ Λ)).vertexSet = H.toHypergraph.vertexSet := by
    ext x
    change (x ∈ H.V ∧ x ∈ closure Λ) ∨ (x ∈ H.V ∧ x ∈ univ \ Λ) ↔ x ∈ H.V
    constructor
    · exact fun h => h.elim And.left And.left
    · intro hx
      by_cases hxΛ : x ∈ Λ
      · exact Or.inl ⟨hx, subset_closure hxΛ⟩
      · exact Or.inr ⟨hx, mem_univ _, hxΛ⟩
  have hE : ((PaintingOrDrawing.drawing H).inter (closure Λ)).edgeSet ∪
      ((PaintingOrDrawing.drawing H).inter (univ \ Λ)).edgeSet = H.toHypergraph.edgeSet := by
    ext e
    change (e ∈ H.E ∧ e ⊆ closure Λ) ∨ (e ∈ H.E ∧ e ⊆ univ \ Λ) ↔ e ∈ H.E
    constructor
    · exact fun h => h.elim And.left And.left
    · intro he
      rcases edge_subset_or_subset_compl_of_zone hZone he with heIn | heOut
      · exact Or.inl ⟨he, heIn.trans subset_closure⟩
      · exact Or.inr ⟨he, heOut⟩
  exact ⟨separation_of_cover_deleting_edges hC hD hV hE,
    (separation_of_cover_deleting_edges hD hC (Set.union_comm _ _ ▸ hV)
      (Set.union_comm _ _ ▸ hE)).symm⟩

end GraphMinor.GM16
