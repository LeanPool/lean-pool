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
import LeanPool.GraphMinor.GM16.WallBrickRegion
import LeanPool.GraphMinor.GM16.WallBrickBoundary
import LeanPool.GraphMinor.GM16.WallOuterRegion
import LeanPool.GraphMinor.GM16.SphereComplementDisc
import LeanPool.GraphMinor.GM16.RectangularDisc
import LeanPool.GraphMinor.GM11.Regions
import LeanPool.GraphMinor.GM11.Section6
import Mathlib.Tactic.Linarith

/-!
# All regions of the sphere wall

Choose a point of a region. If it is in the enclosed disc, the
brick cover places it in a closed brick. It cannot be on a brick
boundary, since those boundaries belong to the drawing. The region
is therefore that brick interior. A point outside the enclosed
disc instead lies in the outside region. This completes the face
classification needed for the rigidity check in XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface GM11

/-- Every wall region is a brick interior or the outside region. -/
theorem sphereWall_regions_classification {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) {θ : ℕ}
    (hθ : 2 ≤ θ) (hEven : Even θ)
    (f : (ℝ × ℝ) → S) (hf : IsEmbedding f) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val)
    {r : Set S} (hr : r ∈ Γ.drawing.R) :
    r = interior (closure (f '' wallEnclosedSet θ)ᶜ) ∨
      ∃ i j : ℕ, i+2 < 2 * θ + 1 ∧ j+1 < θ ∧ Even (i+j) ∧
        r = interior (f '' (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1))) := by
  obtain ⟨x,hxr⟩ := region_nonempty hr
  have hxNot : x ∉ Γ.drawing.U := region_subset hr hxr
  by_cases hxC : x ∈ f '' wallEnclosedSet θ
  · obtain ⟨p,hp,rfl⟩ := hxC
    obtain ⟨i,j,hi,hj,hParity,hpB⟩ := wallEnclosedSet_subset_bricks hθ hp
    let B := f '' (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1))
    have hB : IsClosedDisc B := isClosedDisc_image_real_rectangle hf (by linarith) (by linarith)
    have hxInt : f p ∈ interior B := by
      by_contra hn
      have hxFr : f p ∈ frontier B := ⟨subset_closure (mem_image_of_mem f hpB),hn⟩
      have hxBd := GM11.IsClosedDisc.frontier_eq_discBd hS hB ▸ hxFr
      exact hxNot (sphereWall_brick_disc_boundary_subset_U f hf Γ hE hi hj hParity hxBd)
    have hRegion := (sphereWall_brick_is_region hS f hf Γ hV hE hi hj hParity).1
    exact Or.inr ⟨i,j,hi,hj,hParity,region_eq_of_mem hr hRegion hxr hxInt⟩
  · have hC := isClosedDisc_image_wallEnclosedSet hS hf hθ
    obtain ⟨hD,hBd,hCup,_⟩ := isClosedDisc_closure_compl_of_isSphere hSphere hC
    have hxD : x ∈ closure (f '' wallEnclosedSet θ)ᶜ :=
      (hCup.ge (mem_univ x)).resolve_left hxC
    have hxInt : x ∈ interior (closure (f '' wallEnclosedSet θ)ᶜ) := by
      by_contra hn
      have hxFr : x ∈ frontier (closure (f '' wallEnclosedSet θ)ᶜ) := ⟨subset_closure hxD,hn⟩
      have hxBd := GM11.IsClosedDisc.frontier_eq_discBd hS hD ▸ hxFr
      exact hxC (Surface.discBd_subset _ (hBd ▸ hxBd))
    have hRegion := (sphereWall_outer_is_region hS hSphere hθ hEven f hf Γ hV hE).2.1
    exact Or.inl (region_eq_of_mem hr hRegion hxr hxInt)

end GraphMinor.GM16
