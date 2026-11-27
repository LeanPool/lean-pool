/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceSpace

/-!
# Isometric inclusion of localized source completions

Region inclusion acts on the literal test pairs, preserves their covariance
norm, and therefore extends to an isometry of the real Hilbert completions.
The physical source embeddings intertwine this constructed inclusion.
-/

@[expose] public section

open MeasureTheory ClosedSubmodule

namespace VacuumBellSeparation

variable {m : ℝ} (hm : 0 < m)
  {U V : Set (EuclideanSpace ℝ (Fin 3))} (hUV : U ⊆ V)

/-- Inclusion of localized test pairs with their actual covariance norms. -/
noncomputable def sourceTestInclusion : SourceTestSpace hm U →ₗᵢ[ℝ] SourceTestSpace hm V where
  toFun u := ⟨u.1, localizedTimeZeroSources_mono hUV u.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  norm_map' _ := rfl

/-- The uniquely extended inclusion of real source Hilbert spaces. -/
noncomputable def sourceInclusion : SourceHilbert hm U →ₗᵢ[ℝ] SourceHilbert hm V :=
  ((UniformSpace.Completion.toComplₗᵢ :
    SourceTestSpace hm V →ₗᵢ[ℝ] SourceHilbert hm V).comp
      (sourceTestInclusion hm hUV)).fromCompletion

theorem sourceInclusion_coe (u : SourceTestSpace hm U) :
    sourceInclusion hm hUV (u : SourceHilbert hm U) =
      (sourceTestInclusion hm hUV u : SourceHilbert hm V) :=
  ((UniformSpace.Completion.toComplₗᵢ :
    SourceTestSpace hm V →ₗᵢ[ℝ] SourceHilbert hm V).comp
      (sourceTestInclusion hm hUV)).fromCompletion_apply_coe u

/-- The physical vector is unchanged under the actual localized source inclusion. -/
theorem sourceEmbedding_comp_inclusion :
    (sourceEmbedding hm V).comp (sourceInclusion hm hUV) = sourceEmbedding hm U := by
  apply LinearIsometry.ext
  intro z
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq ((sourceEmbedding hm V).continuous.comp (sourceInclusion hm hUV).continuous)
      (sourceEmbedding hm U).continuous) ?_
  intro u
  change sourceEmbedding hm V (sourceInclusion hm hUV (u : SourceHilbert hm U)) = _
  rw [sourceInclusion_coe, sourceEmbedding_coe, sourceEmbedding_coe]
  rfl

theorem sourceEmbedding_inclusion (z : SourceHilbert hm U) :
    sourceEmbedding hm V (sourceInclusion hm hUV z) = sourceEmbedding hm U z :=
  DFunLike.congr_fun (sourceEmbedding_comp_inclusion hm hUV) z

include hUV in
/-- Isotony of the actual closed real one-particle source subspaces. -/
theorem sourceRealSpace_mono : sourceRealSpace hm U ≤ sourceRealSpace hm V := by
  rintro _ ⟨z, rfl⟩
  exact ⟨sourceInclusion hm hUV z, sourceEmbedding_inclusion hm hUV z⟩

end VacuumBellSeparation
