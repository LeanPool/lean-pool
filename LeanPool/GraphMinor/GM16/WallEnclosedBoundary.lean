/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallDrawing
public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallBrickCover
import LeanPool.GraphMinor.GM16.WallBrickBoundary
import LeanPool.GraphMinor.GM16.RectangularDisc
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.Surface.Wedge
import Mathlib.Tactic.Linarith

/-!
# The outer boundary of the enclosed wall disc

The closed bricks cover the enclosed disc. A boundary point of
that disc belongs to a brick and cannot be interior to it. It
therefore belongs to the brick boundary, which lies in the wall
drawing. This gives the drawing boundary needed for the outside
face in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface

/-- The intrinsic boundary of the enclosed wall disc lies in the drawing. -/
theorem sphereWall_enclosed_boundary_subset_U {S : Type*}
    [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) {θ : ℕ} (hθ : 2 ≤ θ)
    (f : (ℝ × ℝ) → S) (hf : IsEmbedding f) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val) :
    discBd (f '' wallEnclosedSet θ) ⊆ Γ.drawing.U := by
  have hDisc := isClosedDisc_image_wallEnclosedSet hS hf hθ
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Surface.discBd_subset _ hx
  obtain ⟨i,j,hi,hj,hEven,hpBrick⟩ := wallEnclosedSet_subset_bricks hθ hp
  let B := f '' (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1))
  have hB : IsClosedDisc B := isClosedDisc_image_real_rectangle hf (by linarith) (by linarith)
  have hBBoundary : f p ∈ discBd B := by
    rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hB]
    refine ⟨subset_closure (mem_image_of_mem f hpBrick),?_⟩
    intro hpInt
    have hBSub : B ⊆ f '' wallEnclosedSet θ := image_mono (wall_brick_subset_enclosedSet hi hj
      hEven)
    have hpOuterInt := interior_mono hBSub hpInt
    have hpOuterFr : f p ∈ frontier (f '' wallEnclosedSet θ) :=
      (GM11.IsClosedDisc.frontier_eq_discBd hS hDisc).symm ▸ hx
    exact hpOuterFr.2 hpOuterInt
  exact sphereWall_brick_disc_boundary_subset_U f hf Γ hE hi hj hEven hBBoundary

end GraphMinor.GM16
