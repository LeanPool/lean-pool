/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallDrawing
import LeanPool.GraphMinor.GM16.WallRegions
import LeanPool.GraphMinor.GM16.WallBrickRegion
import LeanPool.GraphMinor.GM16.WallOuterRegion
import LeanPool.GraphMinor.GM16.RectangularDisc
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Section6
import Mathlib.Tactic.Linarith

/-!
# Every wall face has a disc closure

The face classification gives either a brick interior or the
outside disc interior. Each has its stated disc as closure. Since
its interior is a region, any drawing point in that closed disc
lies on the disc boundary. This verifies the disc-face hypothesis
of the rigidity criterion for the wall in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM11

/-- Every region of the even wall is the interior of its disc closure. -/
theorem sphereWall_region_closedDisc {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) {θ : ℕ}
    (hθ : 2 ≤ θ) (hEven : Even θ)
    (f : (ℝ × ℝ) → S) (hf : IsEmbedding f) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val)
    {r : Set S} (hr : r ∈ Γ.drawing.R) :
    IsClosedDisc (closure r) ∧ interior (closure r) = r := by
  rcases sphereWall_regions_classification hS hSphere hθ hEven f hf Γ hV hE hr with hOut | hBrick
  · obtain ⟨hD,_,hCl⟩ := sphereWall_outer_is_region hS hSphere hθ hEven f hf Γ hV hE
    rw [hOut,hCl]
    exact ⟨hD,rfl⟩
  · obtain ⟨i,j,hi,hj,hParity,hrEq⟩ := hBrick
    have hCl := (sphereWall_brick_is_region hS f hf Γ hV hE hi hj hParity).2
    rw [hrEq,hCl]
    exact ⟨isClosedDisc_image_real_rectangle hf (by linarith) (by linarith),rfl⟩

/-- The wall verifies the disc-face and empty-interior conditions of
`isRigid_of_disc_faces`. -/
theorem sphereWall_disc_faces {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) {θ : ℕ}
    (hθ : 2 ≤ θ) (hEven : Even θ)
    (f : (ℝ × ℝ) → S) (hf : IsEmbedding f) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val)
    {r : Set S} (hr : r ∈ Γ.drawing.R) :
    IsClosedDisc (closure r) ∧ closure r ∩ Γ.drawing.U ⊆ discBd (closure r) := by
  obtain ⟨hDisc,hInt⟩ := sphereWall_region_closedDisc hS hSphere hθ hEven f hf Γ hV hE hr
  refine ⟨hDisc,?_⟩
  rintro x ⟨hx,hxU⟩
  rw [← GM11.IsClosedDisc.frontier_eq_discBd hS hDisc]
  refine ⟨subset_closure hx,?_⟩
  intro hxInt
  exact region_subset hr (hInt ▸ hxInt) hxU

end GraphMinor.GM16
