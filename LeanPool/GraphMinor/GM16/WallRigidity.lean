/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallDrawing
public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM16.RigidDiscFaces
import LeanPool.GraphMinor.GM16.WallFaceDiscs
import LeanPool.GraphMinor.GM16.WallRegions
import LeanPool.GraphMinor.GM16.WallBrickRegion
import LeanPool.GraphMinor.GM16.WallOuterRegion
import LeanPool.GraphMinor.GM16.ConvexFaceLines
import LeanPool.GraphMinor.GM16.EmbeddedBrickOuterLines

/-!
# Rigidity of the sphere wall drawing

All face closures are discs. Common points of two brick closures
are joined by a line in their convex coordinate intersection.
For a brick and the outside face, use the boundary arc calculations.
The disc-face criterion then proves that the even wall drawing is
rigid, supplying the assertion in XVI (4.2), page 53.
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM14

/-- Any two distinct common points of wall face closures are joined
by a line in their common boundary. -/
theorem sphereWall_face_join_lines {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) {θ : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ)
    (f : (ℝ × ℝ) → S) (hf : IsOpenEmbedding f) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val) :
    ∀ r ∈ Γ.drawing.R, ∀ s ∈ Γ.drawing.R, r ≠ s → ∀ a b : S, a ≠ b →
      a ∈ closure r ∩ closure s → b ∈ closure r ∩ closure s →
      ∃ K, IsLineWithEnds K a b ∧ K ⊆ closure r ∩ closure s := by
  intro r hr s hs hne a b hab ha hb
  have hClass (t : Set S) (ht : t ∈ Γ.drawing.R) :=
    sphereWall_regions_classification hS hSphere (by omega : 2≤θ) hEven f hf.isEmbedding Γ hV hE ht
  have hOutCl := (sphereWall_outer_is_region hS hSphere (by omega : 2≤θ) hEven f hf.isEmbedding Γ
    hV hE).2.2
  rcases hClass r hr with hrOut | ⟨i,j,hi,hj,hParity,hrBrick⟩
  · rcases hClass s hs with hsOut | ⟨k,l,hk,hl,hParityS,hsBrick⟩
    · exact (hne (hrOut.trans hsOut.symm)).elim
    · have hBrickCl := (sphereWall_brick_is_region hS f hf.isEmbedding Γ hV hE hk hl hParityS).2
      rw [hrOut,hOutCl,hsBrick,hBrickCl] at ha hb ⊢
      obtain ⟨K,hK,hSub⟩ := exists_line_in_embedded_brick_outer_intersection hS hSphere hf hθ hEven
        hk hl hParityS hab ⟨ha.2,ha.1⟩ ⟨hb.2,hb.1⟩
      exact ⟨K,hK,fun x hx => ⟨(hSub hx).2,(hSub hx).1⟩⟩
  · have hrCl := (sphereWall_brick_is_region hS f hf.isEmbedding Γ hV hE hi hj hParity).2
    rcases hClass s hs with hsOut | ⟨k,l,hk,hl,hParityS,hsBrick⟩
    · rw [hrBrick,hrCl,hsOut,hOutCl] at ha hb ⊢
      exact exists_line_in_embedded_brick_outer_intersection hS hSphere hf hθ hEven hi hj hParity
        hab ha hb
    · have hsCl := (sphereWall_brick_is_region hS f hf.isEmbedding Γ hV hE hk hl hParityS).2
      rw [hrBrick,hrCl,hsBrick,hsCl] at ha hb ⊢
      exact exists_line_in_embedded_rectangles_intersection hf.isEmbedding
        (i : ℝ) ((i : ℝ)+2) (j : ℝ) ((j : ℝ)+1)
        (k : ℝ) ((k : ℝ)+2) (l : ℝ) ((l : ℝ)+1) hab ha hb

/-- The explicit sphere drawing of the even wall is rigid, as used
in Graph Minors XVI (4.2), page 53. The height is at least four,
which is permitted by the paper's initial increase of `θ`. -/
theorem sphereWall_drawing_isRigid {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) {θ : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ)
    (f : (ℝ × ℝ) → S) (hf : IsOpenEmbedding f) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val) :
    IsRigid Γ.drawing := by
  exact isRigid_of_disc_faces hS
    (fun r hr => sphereWall_disc_faces hS hSphere (by omega : 2≤θ) hEven f hf.isEmbedding Γ hV hE
      hr)
    (sphereWall_face_join_lines hS hSphere hθ hEven f hf Γ hV hE)

end GraphMinor.GM16
