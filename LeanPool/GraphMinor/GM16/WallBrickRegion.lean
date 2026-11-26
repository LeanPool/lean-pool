/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallDrawing
import LeanPool.GraphMinor.GM16.WallBrickBoundary
import LeanPool.GraphMinor.GM16.WallBrickInterior
import LeanPool.GraphMinor.GM16.RectangularDisc
import LeanPool.GraphMinor.GM16.EmptyDiscRegion
import Mathlib.Tactic.Linarith

/-!
# The bounded faces of the wall

Each closed brick is a disc. Its boundary lies in the drawing and
its interior misses the drawing, so that interior is a region with
the closed brick as its closure. This supplies the bounded face
closures for the rigidity check in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface

/-- Every brick interior is a region of the sphere wall drawing,
with the prescribed embedded closed rectangle as its closure. -/
theorem sphereWall_brick_is_region {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {θ : ℕ} (f : (ℝ × ℝ) → S) (hf : IsEmbedding f)
    (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val)
    {i j : ℕ} (hi : i + 2 < 2 * θ + 1) (hj : j + 1 < θ) (hEven : Even (i + j)) :
    let C := f '' (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1))
    interior C ∈ Γ.drawing.R ∧ closure (interior C) = C := by
  apply empty_disc_is_region hS
    (isClosedDisc_image_real_rectangle hf (by linarith) (by linarith))
    (sphereWall_brick_disc_boundary_subset_U f hf Γ hE hi hj hEven)
  exact ((sphereWall_drawing_disjoint_open_brick f hf.injective Γ hV hE i j hEven).symm).mono_left
    (interior_image_rectangle_subset hf _ _ _ _)

end GraphMinor.GM16
