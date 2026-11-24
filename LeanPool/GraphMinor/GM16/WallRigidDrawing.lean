/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallRigidity
import LeanPool.GraphMinor.GM16.RectangularGridDrawing
import LeanPool.GraphMinor.GM16.SpherePlaneEmbedding

/-!
# A rigid drawing of the wall in every sphere

Use the open coordinate plane in the sphere and draw the wall
with its retained lattice lines. The face calculations prove
rigidity. The vertex map and edge closures are retained for the
subdivision step at the end of XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM14

/-- The rigid sphere wall drawing asserted in XVI (4.2), page 53,
with explicit coordinates and graph isomorphism. -/
theorem exists_rigid_sphereWall_drawing {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) {θ : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ) :
    ∃ (f : (ℝ × ℝ) → S) (Γ : GraphDrawing (sphereWallGraph θ) S),
      IsOpenEmbedding f ∧ Γ.drawing.V = range (f ∘ @rectangularGridPoint (2*θ+1) θ) ∧
      (∀ v : V(sphereWallGraph θ), (Γ.iso.vertexEquiv v).val = f (rectangularGridPoint v.val)) ∧
      (∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val = f '' rectangularGridLine
        e.val) ∧
      IsRigid Γ.drawing := by
  obtain ⟨f,hf⟩ := exists_plane_openEmbedding_of_isSphere hSphere
  obtain ⟨Γ,hV,hVertices,hEdges⟩ := exists_rectangularGrid_embedded_drawing
    (sphereWallSimpleGraph θ) (sphereWallSimpleGraph_le_rectangular θ) f hf.isEmbedding
  exact ⟨f,Γ,hf,hV,hVertices,hEdges,
    sphereWall_drawing_isRigid hS hSphere hθ hEven f hf Γ hV hEdges⟩

end GraphMinor.GM16
