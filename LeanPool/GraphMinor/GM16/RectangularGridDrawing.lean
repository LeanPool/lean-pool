/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.RectangularGridLines
public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.RectangularGridLinePoints
import LeanPool.GraphMinor.GM16.RectangularGridLineIntersections
import LeanPool.GraphMinor.GM16.EmbeddedLineGraphDrawing

/-!
# The straight-line drawing of a grid subgraph

Place every vertex at its lattice point and use the assigned unit
lines for edges. The endpoint and intersection checks show that the
finite-line construction applies. The resulting graph drawing has
exactly the prescribed vertex map and edge closures. This includes
the alternating-edge wall used in XVI (4.2), page 53.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Topology GraphMinor.Surface
universe u

/-- A grid subgraph drawn in any space containing an embedded coordinate
plane, with both maps specified. -/
theorem exists_rectangularGrid_embedded_drawing {m n : ℕ}
    (H : SimpleGraph (Fin m × Fin n)) (hSub : H ≤ pathGraph m □ pathGraph n)
    {S : Type u} [TopologicalSpace S] [T2Space S] (j : (ℝ × ℝ) → S) (hj : IsEmbedding j) :
    ∃ Γ : GraphDrawing (Graph.ofSimpleGraph H) S,
      Γ.drawing.V = range (j ∘ @rectangularGridPoint m n) ∧
      (∀ v : V(Graph.ofSimpleGraph H), (Γ.iso.vertexEquiv v).val = j (rectangularGridPoint v.val)) ∧
      (∀ e : E(Graph.ofSimpleGraph H), closure (Γ.iso.edgeEquiv e).val
        = j '' rectangularGridLine e.val) := by
  obtain ⟨Γ,hV,hVertices,hEdges⟩ := exists_graphDrawing_of_embedded_lines
    (Graph.ofSimpleGraph H) (Set.toFinite _) (Set.toFinite _)
    rectangularGridPoint (rectangularGridPoint_injective m n).injOn rectangularGridLine
    (fun e v hLoop => by
      have he : e ∈ H.edgeSet := hLoop.2
      rw [hLoop.1] at he
      exact (show H.Adj v v from he).ne rfl)
    (fun e he a b hLink => by
      have hAdj : H.Adj a b := by
        have he' : e ∈ H.edgeSet := he
        rw [hLink.1] at he'
        exact he'
      rw [hLink.1]
      exact rectangularGridLine_isLine (hSub hAdj))
    (fun e he v _ hv => by
      have heH : e ∈ H.edgeSet := he
      have hvEnd := rectangularGridLine_vertex (edgeSet_mono hSub heH) hv
      obtain ⟨w,hEq⟩ := Sym2.mem_iff_exists.mp hvEnd
      exact ⟨w,hEq,heH⟩)
    (fun e he d hd hne x hx => by
      have heH : e ∈ H.edgeSet := he
      have hdH : d ∈ H.edgeSet := hd
      obtain ⟨v,hv⟩ := rectangularGridLine_intersection (edgeSet_mono hSub heH)
        (edgeSet_mono hSub hdH) hne hx
      exact ⟨v,mem_univ _,hv⟩) j hj
  refine ⟨Γ,?_,hVertices,hEdges⟩
  change Γ.drawing.V = (j ∘ rectangularGridPoint) '' Set.univ at hV
  simpa only [image_univ] using hV

/-- A subgraph of a finite rectangular grid has its straight-line
plane drawing, with the vertex and edge maps specified. -/
theorem exists_rectangularGrid_drawing {m n : ℕ}
    (H : SimpleGraph (Fin m × Fin n)) (hSub : H ≤ pathGraph m □ pathGraph n) :
    ∃ Γ : GraphDrawing (Graph.ofSimpleGraph H) (ℝ × ℝ),
      Γ.drawing.V = range (@rectangularGridPoint m n) ∧
      (∀ v : V(Graph.ofSimpleGraph H), (Γ.iso.vertexEquiv v).val = rectangularGridPoint v.val) ∧
      (∀ e : E(Graph.ofSimpleGraph H), closure (Γ.iso.edgeEquiv e).val = rectangularGridLine e.val)
        := by
  simpa only [Function.id_comp,id_eq,Set.image_id,Set.image_id'] using
    exists_rectangularGrid_embedded_drawing H hSub id IsEmbedding.id

end GraphMinor.GM16
