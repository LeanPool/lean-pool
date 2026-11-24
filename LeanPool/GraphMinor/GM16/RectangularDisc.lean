/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.Cap
import LeanPool.GraphMinor.Surface.Wedge
import Mathlib.Analysis.Complex.Basic

/-!
# Closed rectangles as discs

The rectangular faces of the wall are closed discs. Transfer the
rectangle theorem in complex coordinates to real coordinate pairs,
then carry the disc through the embedding used for the sphere
wall drawing. The interior of its image is contained in the image
of the open rectangle, which is the inclusion needed to check
that it misses the drawing.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- A nondegenerate closed rectangle in the real coordinate plane is a disc. -/
theorem isClosedDisc_real_rectangle_with_boundary {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsClosedDisc (Icc a b ×ˢ Icc c d) ∧
      discBd (Icc a b ×ˢ Icc c d) = frontier (Icc a b ×ˢ Icc c d) := by
  let e : ℂ ≃ₜ (ℝ × ℝ) := Complex.equivRealProdCLM.toHomeomorph
  obtain ⟨hD,hDb⟩ := Surface.isClosedDisc_rect hab hcd
  obtain ⟨hImage,hImageB⟩ := isClosedDisc_image_injOn hD hD.isCompact
    e.continuous.continuousOn e.injective.injOn
  have he : e '' (Icc a b ×ℂ Icc c d) = Icc a b ×ˢ Icc c d := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x.1,x.2⟩,hx,rfl⟩
  refine ⟨he ▸ hImage,?_⟩
  rw [← he,hImageB,hDb,e.image_frontier]

/-- A nondegenerate closed rectangle in real coordinates is a disc. -/
theorem isClosedDisc_real_rectangle {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsClosedDisc (Icc a b ×ˢ Icc c d) :=
  (isClosedDisc_real_rectangle_with_boundary hab hcd).1

/-- Carry a closed rectangle through an embedding into a Hausdorff space. -/
theorem isClosedDisc_image_real_rectangle {S : Type*} [TopologicalSpace S] [T2Space S]
    {f : (ℝ × ℝ) → S} (hf : IsEmbedding f)
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    IsClosedDisc (f '' (Icc a b ×ˢ Icc c d)) :=
  (isClosedDisc_image_injOn (isClosedDisc_real_rectangle hab hcd)
    (isCompact_Icc.prod isCompact_Icc) hf.continuous.continuousOn hf.injective.injOn).1

/-- An interior point of an embedded closed rectangle comes from its open
rectangle. Only continuity and injectivity of the embedding are needed. -/
theorem interior_image_rectangle_subset {S : Type*} [TopologicalSpace S]
    {f : (ℝ × ℝ) → S} (hf : IsEmbedding f) (a b c d : ℝ) :
    interior (f '' (Icc a b ×ˢ Icc c d)) ⊆ f '' (Ioo a b ×ˢ Ioo c d) := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := interior_subset hx
  refine ⟨y,?_,rfl⟩
  have hy := preimage_interior_subset_interior_preimage hf.continuous hx
  rw [Set.preimage_image_eq _ hf.injective,interior_prod_eq,interior_Icc,interior_Icc] at hy
  exact hy

end GraphMinor.GM16
