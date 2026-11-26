/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Connected subsets containing both ends of a line

A preconnected subset of a line that contains both ends contains the
whole line. Pulling the subset back to the unit interval proves this
by the interval property of preconnected sets. This supplies the
point set comparison for paths in the proof of XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- The point set of a line is preconnected. -/
theorem isPreconnected_of_isLineWithEnds {S : Type*} [TopologicalSpace S]
    {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) : IsPreconnected L :=
  GraphMinor.Surface.IsLineWithEnds.isPreconnected hL

/-- A preconnected subset containing both ends of a line is the whole line. -/
theorem eq_line_of_preconnected_subset {S : Type*} [TopologicalSpace S]
    {L T : Set S} {a b : S} (hL : IsLineWithEnds L a b)
    (hTL : T ⊆ L) (hT : IsPreconnected T) (ha : a ∈ T) (hb : b ∈ T) : T = L := by
  obtain ⟨e, he₀, he₁⟩ := hL
  let p : unitInterval → S := fun t => (e t).val
  have hp : IsEmbedding p := IsEmbedding.subtypeVal.comp e.isEmbedding
  let K := p ⁻¹' T
  have himage : p '' K = T := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hz
      refine ⟨e.symm ⟨z, hTL hz⟩, ?_, ?_⟩
      · change (e (e.symm ⟨z, hTL hz⟩)).val ∈ T
        simpa only [e.apply_symm_apply] using hz
      · exact congrArg Subtype.val (e.apply_symm_apply _)
  have hK : IsPreconnected K := hp.isInducing.isPreconnected_image.mp (himage.symm ▸ hT)
  have h₀ : (0 : unitInterval) ∈ K := by
    change (e 0).val ∈ T
    simpa only [he₀] using ha
  have h₁ : (1 : unitInterval) ∈ K := by
    change (e 1).val ∈ T
    simpa only [he₁] using hb
  apply subset_antisymm hTL
  intro z hz
  let t := e.symm ⟨z, hz⟩
  have ht : t ∈ K := hK.Icc_subset h₀ h₁ ⟨bot_le, le_top⟩
  have hpz : p t = z := congrArg Subtype.val (e.apply_symm_apply _)
  exact hpz ▸ ht

end GraphMinor.GM16
