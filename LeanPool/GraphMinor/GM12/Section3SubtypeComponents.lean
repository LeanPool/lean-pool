/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs

/-!
# Edges when a drawing is read in a smaller ambient space

In XII (3.1), page 245, the drawing is read in the surface left after
removing the prescribed discs. Its support remains in that surface.
Path components of a subset do not change when the ambient space is
restricted to a set containing it. This file proves that fact for the
arc-component definition used by drawings.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Arc-components pull back unchanged to an ambient subspace containing
the whole set. This identifies the edges of XII's drawing in Sigma-star. -/
theorem arcComponentsIn_subtype_preimage {S : Type*} [TopologicalSpace S]
    {F C : Set S} (hFC : F ⊆ C) :
    arcComponentsIn ((Subtype.val : C → S) ⁻¹' F) =
      (fun E : Set S => (Subtype.val : C → S) ⁻¹' E) '' arcComponentsIn F := by
  ext D
  constructor
  · rintro ⟨hne, hsub, hpc, hmax⟩
    let E : Set S := Subtype.val '' D
    have hEF : E ⊆ F := by
      rintro x ⟨y, hy, rfl⟩
      exact hsub hy
    refine ⟨E, ⟨hne.image Subtype.val, hEF, hpc.image continuous_subtype_val, ?_⟩, ?_⟩
    · intro E' hE'F hE'pc hEE'
      have hpre : (Subtype.val : C → S) ⁻¹' E' = D := by
        apply hmax
        · exact preimage_mono hE'F
        · exact hE'pc.preimage_coe (hE'F.trans hFC)
        · intro x hx
          exact hEE' ⟨x, hx, rfl⟩
      ext x
      constructor
      · intro hx
        let y : C := ⟨x, hFC (hE'F hx)⟩
        have hy : y ∈ D := hpre ▸ hx
        exact ⟨y, hy, rfl⟩
      · exact fun hx => hEE' hx
    · ext x
      simp only [mem_preimage, E, mem_image]
      constructor
      · rintro ⟨y, hy, heq⟩
        exact (Subtype.ext heq : y = x) ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩
  · rintro ⟨E, ⟨hne, hEF, hpc, hmax⟩, rfl⟩
    refine ⟨?_, preimage_mono hEF, hpc.preimage_coe (hEF.trans hFC), ?_⟩
    · obtain ⟨x, hx⟩ := hne
      exact ⟨⟨x, hFC (hEF hx)⟩, hx⟩
    · intro D' hD'F hD'pc hDD'
      have hEeq : Subtype.val '' D' = E := by
        apply hmax
        · rintro x ⟨y, hy, rfl⟩
          exact hD'F hy
        · exact hD'pc.image continuous_subtype_val
        · intro x hx
          let y : C := ⟨x, hFC (hEF hx)⟩
          exact ⟨y, hDD' hx, rfl⟩
      ext x
      constructor
      · intro hx
        have hm : x.val ∈ Subtype.val '' D' := ⟨x, hx, rfl⟩
        rw [hEeq] at hm
        exact hm
      · exact fun hx => hDD' hx

/-- Arc-components of a set in a subspace map to exactly the
arc-components of its image in the ambient space. This is the reverse
transfer needed after applying VII to the punctured drawing. -/
theorem arcComponentsIn_subtype_image {S : Type*} [TopologicalSpace S]
    {C : Set S} (F : Set C) :
    arcComponentsIn ((Subtype.val : C → S) '' F) =
      (image (Subtype.val : C → S)) '' arcComponentsIn F := by
  have hsub : (Subtype.val : C → S) '' F ⊆ C := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hpre : (Subtype.val : C → S) ⁻¹' ((Subtype.val : C → S) '' F) = F := by
    ext x
    simp
  have htransfer := arcComponentsIn_subtype_preimage hsub
  rw [hpre] at htransfer
  ext E
  constructor
  · intro hE
    have hEC : E ⊆ C := hE.2.1.trans hsub
    have hEpre : (Subtype.val : C → S) ⁻¹' E ∈ arcComponentsIn F := by
      rw [htransfer]
      exact ⟨E, hE, rfl⟩
    refine ⟨(Subtype.val : C → S) ⁻¹' E, hEpre, ?_⟩
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hEC]
  · rintro ⟨E', hE', rfl⟩
    rw [htransfer] at hE'
    obtain ⟨D, hD, hpreD⟩ := hE'
    have hDC : D ⊆ C := hD.2.1.trans hsub
    have himage : (Subtype.val : C → S) '' E' = D := by
      rw [← hpreD, Subtype.image_preimage_coe, inter_eq_right.mpr hDC]
    exact himage.symm ▸ hD

end GraphMinor.GM12
