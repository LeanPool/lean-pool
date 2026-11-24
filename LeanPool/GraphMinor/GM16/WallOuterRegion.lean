/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Section4WallDrawing
public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallDrawingEnclosed
import LeanPool.GraphMinor.GM16.WallEnclosedBoundary
import LeanPool.GraphMinor.GM16.SphereComplementDisc
import LeanPool.GraphMinor.GM16.EmptyDiscRegion
import LeanPool.GraphMinor.GM11.Section6

/-!
# The outside region of the even wall

The wall support is inside its enclosed disc, and the boundary of
that disc lies in the support. The sphere's complementary disc
has the same boundary and no drawing in its interior. Its interior
is therefore the outside region, with that disc as its closure.
This supplies the outside disc face in the rigidity check for
XVI (4.2), page 53.
-/

public section
namespace GraphMinor.GM16
open Set Graph Topology Surface

/-- The complementary disc gives the outside region of the sphere wall. -/
theorem sphereWall_outer_is_region {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hSphere : IsSphere S) {θ : ℕ}
    (hθ : 2 ≤ θ) (hEven : Even θ)
    (f : (ℝ × ℝ) → S) (hf : IsEmbedding f) (Γ : GraphDrawing (sphereWallGraph θ) S)
    (hV : Γ.drawing.V = range (f ∘ @rectangularGridPoint (2 * θ + 1) θ))
    (hE : ∀ e : E(sphereWallGraph θ), closure (Γ.iso.edgeEquiv e).val
      = f '' rectangularGridLine e.val) :
    let D := closure (f '' wallEnclosedSet θ)ᶜ
    IsClosedDisc D ∧ interior D ∈ Γ.drawing.R ∧ closure (interior D) = D := by
  have hC := isClosedDisc_image_wallEnclosedSet hS hf hθ
  obtain ⟨hD,hBd,_,hMeet⟩ := isClosedDisc_closure_compl_of_isSphere hSphere hC
  have hDrawing := sphereWall_drawing_subset_enclosed hθ hEven f Γ hV hE
  have hBdU : discBd (closure (f '' wallEnclosedSet θ)ᶜ) ⊆ Γ.drawing.U := by
    rw [hBd]
    exact sphereWall_enclosed_boundary_subset_U hS hθ f hf Γ hE
  have hEmpty : Disjoint (interior (closure (f '' wallEnclosedSet θ)ᶜ)) Γ.drawing.U := by
    apply disjoint_left.mpr
    intro x hxInt hxU
    have hxBd : x ∈ discBd (f '' wallEnclosedSet θ) :=
      hMeet ▸ ⟨hDrawing hxU,interior_subset hxInt⟩
    have hxFr : x ∈ frontier (closure (f '' wallEnclosedSet θ)ᶜ) :=
      (GM11.IsClosedDisc.frontier_eq_discBd hS hD).symm ▸ (hBd.symm ▸ hxBd)
    exact hxFr.2 hxInt
  exact ⟨hD,empty_disc_is_region hS hD hBdU hEmpty⟩

end GraphMinor.GM16
