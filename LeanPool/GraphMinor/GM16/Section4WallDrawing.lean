/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4Wall
public import LeanPool.GraphMinor.GM16.RectangularGridLines
public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.GM16.RectangularGridDrawing
import LeanPool.GraphMinor.GM16.SpherePlaneEmbedding

/-!
# Drawing the wall in any sphere

The wall retains all horizontal grid edges and alternate vertical
ones. It is therefore a subgraph of the rectangular grid. Place that
grid's coordinate plane in the sphere and use its unit-line drawing.
The graph isomorphism and all edge closures are kept explicit for the
subdivision and rigidity steps of XVI (4.2), pages 53–54.
-/

public section
namespace GraphMinor.GM16
open Set Graph SimpleGraph Topology GraphMinor.Surface
universe u

/-- The alternating-edge wall is a subgraph of its rectangular grid. -/
theorem sphereWallSimpleGraph_le_rectangular (θ : ℕ) :
    sphereWallSimpleGraph θ ≤ pathGraph (2 * θ + 1) □ pathGraph θ := by
  intro x y h
  rcases h with ⟨hj,hStep⟩ | ⟨hi,hStep⟩
  · exact Or.inl ⟨pathGraph_adj.mpr hStep,hj⟩
  · rcases hStep with ⟨hStep,_⟩ | ⟨hStep,_⟩
    · exact Or.inr ⟨pathGraph_adj.mpr (Or.inl hStep),hi⟩
    · exact Or.inr ⟨pathGraph_adj.mpr (Or.inr hStep),hi⟩

/-- The wall drawing used in XVI (4.2), page 53, with its coordinate
embedding, graph isomorphism, and every edge closure specified. -/
theorem exists_sphereWall_drawing {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsSphere S) (θ : ℕ) :
    ∃ (j : (ℝ × ℝ) → S) (Γ : GraphDrawing (sphereWallGraph θ) S),
      IsEmbedding j ∧ Γ.drawing.V = range (j ∘ @rectangularGridPoint (2 * θ + 1) θ) ∧
      (∀ v : V(sphereWallGraph θ), (Γ.iso.vertexEquiv v).val = j (rectangularGridPoint v.val)) ∧
      (∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val = j '' rectangularGridLine
        e.val) := by
  obtain ⟨j,hj⟩ := exists_plane_embedding_of_isSphere hS
  obtain ⟨Γ,hV,hVertices,hEdges⟩ := exists_rectangularGrid_embedded_drawing
    (sphereWallSimpleGraph θ) (sphereWallSimpleGraph_le_rectangular θ) j hj
  exact ⟨j,Γ,hj,hV,hVertices,hEdges⟩

end GraphMinor.GM16
