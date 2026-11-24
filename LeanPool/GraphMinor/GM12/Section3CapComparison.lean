/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM12.Section3DiscBoundaryExtension
import LeanPool.GraphMinor.GM12.Section3GlueHomeomorph
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.Surface.PlaneDisc

/-!
# Comparing choices of a cap

For XII (3.1), page 245, near-planarity in the explicitly filled
surface must agree with near-planarity in every cap used by VII.
The identity on the original surface induces a map of cap boundaries.
Extend that map over the discs and glue along the common boundary.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

universe u

/-- Two caps of the same cuff are homeomorphic by a map agreeing with
the identity on the uncapped surface. -/
theorem cappedCuff_homeomorph
    {S S₁ S₂ : Type u} [TopologicalSpace S] [TopologicalSpace S₁] [TopologicalSpace S₂]
    (hS : IsSurface S) {C : Set S} {j₁ : S → S₁} {j₂ : S → S₂}
    {D₁ : Set S₁} {D₂ : Set S₂}
    (h₁ : GM07.IsCappedCuff C S₁ j₁ D₁) (h₂ : GM07.IsCappedCuff C S₂ j₂ D₂) :
    ∃ H : S₁ ≃ₜ S₂, ∀ x : S, H (j₁ x) = j₂ x := by
  let : CompactSpace S := hS.1
  let : CompactSpace S₁ := h₁.isSurface.1
  let : T2Space S₁ := h₁.isSurface.2.1
  let : T2Space S₂ := h₂.isSurface.2.1
  let e₁ := h₁.isEmbedding.toHomeomorph
  let e₂ := h₂.isEmbedding.toHomeomorph
  let f := e₁.symm.trans e₂
  have hf : ∀ x, (f ⟨j₁ x, mem_range_self x⟩).val = j₂ x := by
    intro x
    change j₂ (e₁.symm ⟨j₁ x, mem_range_self x⟩) = j₂ x
    rw [IsEmbedding.toHomeomorph_symm_apply]
  let q₁ : C ≃ₜ discBd D₁ := (h₁.isEmbedding.homeomorphImage C).trans
    (Homeomorph.setCongr h₁.discBd_eq.symm)
  let q₂ : C ≃ₜ discBd D₂ := (h₂.isEmbedding.homeomorphImage C).trans
    (Homeomorph.setCongr h₂.discBd_eq.symm)
  let p := q₁.symm.trans q₂
  obtain ⟨g, hg⟩ := exists_disc_homeomorph_extending_boundary h₁.isClosedDisc h₂.isClosedDisc p
  have hmem₁ : ∀ x, j₁ x ∈ D₁ ↔ x ∈ C := by
    intro x
    constructor
    · intro hx
      have hxI : j₁ x ∈ range j₁ ∩ D₁ := ⟨mem_range_self x, hx⟩
      rw [h₁.inter_eq] at hxI
      obtain ⟨y, hy, he⟩ := hxI
      exact h₁.isEmbedding.injective he ▸ hy
    · intro hx
      apply discBd_subset D₁
      rw [h₁.discBd_eq]
      exact mem_image_of_mem j₁ hx
  have hmem₂ : ∀ x, j₂ x ∈ D₂ ↔ x ∈ C := by
    intro x
    constructor
    · intro hx
      have hxI : j₂ x ∈ range j₂ ∩ D₂ := ⟨mem_range_self x, hx⟩
      rw [h₂.inter_eq] at hxI
      obtain ⟨y, hy, he⟩ := hxI
      exact h₂.isEmbedding.injective he ▸ hy
    · intro hx
      apply discBd_subset D₂
      rw [h₂.discBd_eq]
      exact mem_image_of_mem j₂ hx
  have hcross : ∀ x : range j₁, (f x).val ∈ D₂ ↔ x.val ∈ D₁ := by
    rintro ⟨_, x, rfl⟩
    rw [hf, hmem₁, hmem₂]
  have hagree : ∀ (x : range j₁) (hx : x.val ∈ D₁),
      (f x).val = (g ⟨x.val, hx⟩).val := by
    rintro ⟨_, x, rfl⟩ hx
    have hxC := (hmem₁ x).mp hx
    have hxB : j₁ x ∈ discBd D₁ := h₁.discBd_eq.symm ▸ mem_image_of_mem j₁ hxC
    rw [hf, hg ⟨j₁ x, hxB⟩]
    have hq : q₁.symm ⟨j₁ x, hxB⟩ = ⟨x, hxC⟩ := by
      apply q₁.injective
      rw [q₁.apply_symm_apply]
      exact Subtype.ext rfl
    change j₂ x = j₂ (q₁.symm ⟨j₁ x, hxB⟩).val
    rw [hq]
  obtain ⟨H, hH, _⟩ := exists_homeomorph_of_two_closed_pieces
    (isCompact_range h₁.isEmbedding.continuous).isClosed h₁.isClosedDisc.isCompact.isClosed
    h₁.union_eq h₂.union_eq f g hcross hagree
  exact ⟨H, fun x => (hH ⟨j₁ x, mem_range_self x⟩).trans (hf x)⟩

/-- Planarity in one cap gives planarity in every cap, as required by
VII's definition. The comparison homeomorphism fixes the original
surface pointwise. -/
theorem isPlanarInCappedCuff_of_one_cap
    {S S₁ : Type u} [TopologicalSpace S] [TopologicalSpace S₁]
    (hS : IsSurface S) {C X : Set S} {j₁ : S → S₁} {D₁ : Set S₁}
    (h₁ : GM07.IsCappedCuff C S₁ j₁ D₁) (hX : GM11.IsPlanar (j₁ '' X)) :
    GM07.IsPlanarInCappedCuff C X := by
  refine ⟨h₁.cuff, ⟨S₁, inferInstance, j₁, D₁, h₁, hX⟩, ?_⟩
  intro S₂ _ j₂ D₂ h₂
  obtain ⟨H, hH⟩ := cappedCuff_homeomorph hS h₁ h₂
  obtain ⟨E, hE, hXE⟩ := hX
  have hdisc : IsClosedDisc (H '' E) := by
    obtain ⟨φ⟩ := hE
    exact ⟨φ.trans (H.isEmbedding.homeomorphImage E)⟩
  refine ⟨H '' E, hdisc, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact ⟨j₁ x, hXE (mem_image_of_mem j₁ hx), hH x⟩

end GraphMinor.GM12
