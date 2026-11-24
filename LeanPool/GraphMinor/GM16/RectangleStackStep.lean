/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM16.DiscCoordinateBoundary
import LeanPool.GraphMinor.GM16.RectangularDisc
import LeanPool.GraphMinor.GM16.RectangularLines
import LeanPool.GraphMinor.GM16.LineImageEmbedding
import LeanPool.GraphMinor.Surface.DiscUnion

/-!
# Adding a row to a disc made of rectangles

The union of the wall's brick rows is a disc. At each step the new
row meets the previous rows in a horizontal interval at their top
height. Coordinate bounds put this interval on both disc boundaries,
so the disc union theorem applies. This file proves that step for
the coordinate embedding into a closed surface.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- Append a rectangle above a disc when the intersection is one
nondegenerate horizontal side. -/
theorem isClosedDisc_append_rectangle {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {f : (ℝ × ℝ) → S} (hf : IsEmbedding f)
    {A : Set (ℝ × ℝ)} {a b c d l r : ℝ}
    (hA : IsClosedDisc (f '' A)) (hab : a < b) (hcd : c < d) (hlr : l < r)
    (hBound : ∀ p ∈ A, p.2 ≤ c)
    (hMeet : A ∩ (Icc a b ×ˢ Icc c d) = Icc l r ×ˢ {c}) :
    IsClosedDisc (f '' (A ∪ (Icc a b ×ˢ Icc c d))) := by
  let R := Icc a b ×ˢ Icc c d
  let L := Icc l r ×ˢ {c}
  have hR : IsClosedDisc (f '' R) := isClosedDisc_image_real_rectangle hf hab hcd
  have hL := isLineWithEnds_image_embedding hf (horizontal_interval_isLine hlr c)
  have hInter : (f '' A) ∩ (f '' R) = f '' L := by
    rw [← image_inter hf.injective]
    exact congrArg (fun X => f '' X) hMeet
  have hLeft : f '' L ⊆ discBd (f '' A) := by
    rintro x ⟨p,hp,rfl⟩
    have hpA : p ∈ A := (hMeet.symm ▸ (show p ∈ Icc l r ×ˢ {c} from hp)).1
    apply mem_discBd_of_vertical_max hS hA hf.continuous ?_ (mem_image_of_mem f hpA) hp.2
    intro q hq
    obtain ⟨z,hz,hzq⟩ := hq
    exact hf.injective hzq ▸ hBound z hz
  have hRight : f '' L ⊆ discBd (f '' R) := by
    rintro x ⟨p,hp,rfl⟩
    have hpR : p ∈ R := (hMeet.symm ▸ (show p ∈ Icc l r ×ˢ {c} from hp)).2
    apply mem_discBd_of_vertical_min hS hR hf.continuous ?_ (mem_image_of_mem f hpR) hp.2
    intro q hq
    obtain ⟨z,hz,hzq⟩ := hq
    exact hf.injective hzq ▸ hz.2.1
  have hDisc := (disc_union (f '' A) (f '' R) (f '' L)
    (f (l,c)) (f (r,c)) hA hR hL hInter hLeft hRight).1
  rwa [image_union]

end GraphMinor.GM16
