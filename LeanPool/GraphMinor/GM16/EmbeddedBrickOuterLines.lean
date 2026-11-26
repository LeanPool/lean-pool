/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.GM16.WallBrickOuterLines
import LeanPool.GraphMinor.GM16.WallBrickCover
import LeanPool.GraphMinor.GM16.SphereComplementDisc
import LeanPool.GraphMinor.GM16.LineImageEmbedding
import LeanPool.GraphMinor.GM11.Section6

/-!
# Common brick and outside boundary lines after embedding

A common point lies on the boundary of the enclosed disc. The
open coordinate embedding pulls that boundary back to the
frontier of the enclosed row stack. Use the coordinate common-line
construction there, and carry the resulting line back to the
sphere. This verifies the brick/outside case of the rigidity
criterion for XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- Common points of an embedded brick and the outside disc are
joined by a line contained in both. -/
theorem exists_line_in_embedded_brick_outer_intersection {S : Type*}
    [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) (hSphere : IsSphere S)
    {f : (ℝ × ℝ) → S} (hf : IsOpenEmbedding f) {θ i j : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ) (hi : i + 2 < 2 * θ + 1) (hj : j + 1 < θ) (hParity : Even (i + j))
    {a b : S} (hab : a ≠ b)
    (ha : a ∈ (f '' (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1))) ∩
      closure (f '' wallEnclosedSet θ)ᶜ)
    (hb : b ∈ (f '' (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1))) ∩
      closure (f '' wallEnclosedSet θ)ᶜ) :
    ∃ K, IsLineWithEnds K a b ∧ K ⊆
      (f '' (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1))) ∩
        closure (f '' wallEnclosedSet θ)ᶜ := by
  have hC := isClosedDisc_image_wallEnclosedSet hS hf.isEmbedding (by omega : 2≤θ)
  obtain ⟨_,_,_,hMeet⟩ := isClosedDisc_closure_compl_of_isSphere hSphere hC
  have hPre : f ⁻¹' frontier (f '' wallEnclosedSet θ) = frontier (wallEnclosedSet θ) := by
    rw [hf.isOpenMap.preimage_frontier_eq_frontier_preimage hf.continuous,
      preimage_image_eq _ hf.injective]
  obtain ⟨p,hp,hpa⟩ := ha.1
  obtain ⟨q,hq,hqb⟩ := hb.1
  have hSource (z : ℝ × ℝ)
      (hz : z ∈ Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1))
      (hzOut : f z ∈ closure (f '' wallEnclosedSet θ)ᶜ) : z ∈ frontier (wallEnclosedSet θ) := by
    have hzC : f z ∈ f '' wallEnclosedSet θ :=
      mem_image_of_mem f (wall_brick_subset_enclosedSet hi hj hParity hz)
    have hzBd := hMeet ▸ (show f z ∈ (f '' wallEnclosedSet θ) ∩
      closure (f '' wallEnclosedSet θ)ᶜ from ⟨hzC,hzOut⟩)
    have hzFr : f z ∈ frontier (f '' wallEnclosedSet θ) :=
      (GM11.IsClosedDisc.frontier_eq_discBd hS hC).symm ▸ hzBd
    exact (congrArg (fun A : Set (ℝ × ℝ) => z ∈ A) hPre).mp hzFr
  have hpFr := hSource p hp (hpa.symm ▸ ha.2)
  have hqFr := hSource q hq (hqb.symm ▸ hb.2)
  have hpq : p ≠ q := fun he => hab (hpa.symm.trans ((congrArg f he).trans hqb))
  obtain ⟨L,hL,hSub⟩ := exists_line_in_brick_outer_intersection hθ hEven hi hj hParity hpq
    ⟨hp,hpFr⟩ ⟨hq,hqFr⟩
  refine ⟨f '' L,?_,?_⟩
  · have h := isLineWithEnds_image_embedding hf.isEmbedding hL
    rwa [hpa,hqb] at h
  · rintro x ⟨z,hz,rfl⟩
    have hzSub := hSub hz
    have hzFr : f z ∈ frontier (f '' wallEnclosedSet θ) :=
      (congrArg (fun A : Set (ℝ × ℝ) => z ∈ A) hPre).mpr hzSub.2
    have hzBd := GM11.IsClosedDisc.frontier_eq_discBd hS hC ▸ hzFr
    exact ⟨mem_image_of_mem f hzSub.1,(hMeet.symm ▸ hzBd).2⟩

end GraphMinor.GM16
