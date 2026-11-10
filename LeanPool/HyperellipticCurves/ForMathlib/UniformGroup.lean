/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Completeness of a uniform additive group from a complete open subgroup

A uniform additive group is complete as soon as one of its open subgroups is
(`AddSubgroup.completeSpace_of_isComplete`): the group is the union of the cosets of the
subgroup, and distinct cosets are uniformly separated by the entourage the subgroup itself
defines. Mathlib has the underlying `isComplete_iUnion_separated` but not this consequence.

The typical application is a valued field that is the union of the cosets of its (complete,
open) ring of integers.
-/

@[expose] public section

open Filter Topology

namespace AddSubgroup

variable {G : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]

/-- A uniform additive group with a complete open subgroup is complete: the group is the
union of the cosets of the subgroup, and these are uniformly separated. -/
theorem completeSpace_of_isComplete (S : AddSubgroup G) (hcomplete : IsComplete (S : Set G))
    (hnhds : (S : Set G) ∈ 𝓝 (0 : G)) :
    CompleteSpace G := by
  set s : (G ⧸ S) → Set G := fun c ↦ QuotientAddGroup.mk ⁻¹' {c} with hs
  have hunion : (⋃ c, s c) = Set.univ := by
    ext x
    simp only [hs, Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨QuotientAddGroup.mk x, rfl⟩
  have hcos c : IsComplete (s c) := by
    obtain ⟨x₀, rfl⟩ := QuotientAddGroup.mk_surjective c
    have hcoset : s (QuotientAddGroup.mk x₀) = (fun t ↦ t + x₀) '' (S : Set G) := by
      ext y
      simp only [hs, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image, SetLike.mem_coe]
      rw [QuotientAddGroup.eq_iff_sub_mem]
      exact ⟨fun h ↦ ⟨y - x₀, h, by simp⟩, fun ⟨t, ht, hty⟩ ↦ by rw [← hty]; simpa using ht⟩
    rw [hcoset]
    exact (isComplete_image_iff
      (isUniformEmbedding_translate_add x₀).isUniformInducing).mpr hcomplete
  set U : Set (G × G) := (fun p : G × G ↦ p.2 - p.1) ⁻¹' (S : Set G) with hU
  have hUmem : U ∈ uniformity G := by
    rw [uniformity_eq_comap_nhds_zero]
    exact Filter.mem_comap.mpr ⟨(S : Set G), hnhds, subset_rfl⟩
  have hsep (c c' : G ⧸ S) x (hx : x ∈ s c) y (hy : y ∈ s c') (hxy : (x, y) ∈ U) : c = c' := by
    simp only [hs, Set.mem_preimage, Set.mem_singleton_iff] at hx hy
    simp only [hU, Set.mem_preimage, SetLike.mem_coe] at hxy
    rw [← hx, ← hy, QuotientAddGroup.eq_iff_sub_mem]
    simpa [neg_sub] using neg_mem hxy
  rw [completeSpace_iff_isComplete_univ, ← hunion]
  exact isComplete_iUnion_separated hcos hUmem hsep

end AddSubgroup

end
