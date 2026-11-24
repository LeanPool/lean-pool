/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.DrawingBoundaryOrders
import LeanPool.GraphMinor.GM11.Walks

/-!
# Point sets of transported subdrawings

The point set of a subgraph in a transported drawing is the image of
its original point set. In particular the nested circuits supplied by
XIV (5.5) give the same nested boundary curves in the plane presentation
used in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11
universe u v
variable {S : Type u} {T : Type v} [TopologicalSpace S] [TopologicalSpace T]

/-- The arc representing an edge is its image under transport. -/
theorem graphDrawingEdgeSet_transport {D : Drawing S}
    (Γ : GraphDrawing D.toGraph T) {f : S → T}
    (he : ∀ e : D.toGraph.edgeSet, (Γ.iso.edgeEquiv e).val = f '' e.val)
    {e : Set S} (heD : e ∈ D.E) : graphDrawingEdgeSet Γ e = f '' e := by
  ext z
  simp only [graphDrawingEdgeSet, mem_iUnion]
  constructor
  · rintro ⟨h, hz⟩
    exact he ⟨e, h⟩ ▸ hz
  · intro hz
    exact ⟨heD, (he ⟨e, heD⟩).symm ▸ hz⟩

/-- Transport preserves the full point set of every subdrawing. -/
theorem graphDrawingSubgraphU_transport {D J : Drawing S}
    (Γ : GraphDrawing D.toGraph T) {f : S → T}
    (hv : ∀ x : D.toGraph.vertexSet, (Γ.iso.vertexEquiv x).val = f x.val)
    (he : ∀ e : D.toGraph.edgeSet, (Γ.iso.edgeEquiv e).val = f '' e.val)
    (hcl : ∀ e ∈ D.E, closure (f '' e) = f '' closure e)
    (hJ : J.IsSubdrawing D) : graphDrawingSubgraphU Γ J.toGraph = f '' J.U := by
  ext z
  change z ∈ (⋃ x ∈ J.V, graphDrawingVertexSet Γ x) ∪
    (⋃ e ∈ J.E, closure (graphDrawingEdgeSet Γ e)) ↔ z ∈ f '' J.U
  simp only [mem_union, mem_iUnion]
  constructor
  · rintro (⟨x, hx, hz⟩ | ⟨e, heJ, hz⟩)
    · rw [graphDrawingVertexSet_transport Γ hv (hJ.1 hx)] at hz
      exact ⟨x, J.V_subset_U hx, (mem_singleton_iff.mp hz).symm⟩
    · rw [graphDrawingEdgeSet_transport Γ he (hJ.2 heJ), hcl e (hJ.2 heJ)] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact ⟨x, J.closure_subset_U heJ hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [J.U_eq] at hx
    rcases hx with hx | hx
    · left
      refine ⟨x, hx, ?_⟩
      rw [graphDrawingVertexSet_transport Γ hv (hJ.1 hx)]
      exact mem_singleton _
    · obtain ⟨e, hxe⟩ := mem_iUnion.mp hx
      obtain ⟨heJ, hxe⟩ := mem_iUnion.mp hxe
      right
      refine ⟨e, heJ, ?_⟩
      rw [graphDrawingEdgeSet_transport Γ he (hJ.2 heJ), hcl e (hJ.2 heJ)]
      exact mem_image_of_mem f hxe

end GraphMinor.GM16
