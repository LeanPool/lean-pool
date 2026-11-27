/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceDefs
public import LeanPool.VacuumBellSeparation.FreeField.SourceInclusion
public import LeanPool.VacuumBellSeparation.Gaussian.SourceGram

/-!
# Actual complexified local source maps and Gram operators

This specializes the constructed Hilbert complexification to the completed
literal local source space. The Gram operator is defined as `κ*κ` and its
normalized commutation formula is proved.
-/

@[expose] public section

open MeasureTheory ClosedSubmodule

namespace VacuumBellSeparation

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem sourceGram_eq_normalized_commutation :
    sourceGram hm U = 1 + (Complex.I / 2) • complexSourceCommutation hm U :=
  Gaussian.sourceMap_adjoint_mul_self (sourceEmbedding hm U)

theorem complexSourceCommutation_mem_skewAdjoint :
    complexSourceCommutation hm U ∈ skewAdjoint
      (ComplexSourceHilbert hm U →L[ℂ] ComplexSourceHilbert hm U) :=
  Gaussian.complexCommutation_mem_skewAdjoint (sourceEmbedding hm U)

theorem norm_complexSourceCommutation_le_two : ‖complexSourceCommutation hm U‖ ≤ 2 :=
  Gaussian.norm_complexCommutation_le_two (sourceEmbedding hm U)

theorem norm_complexSourceMap_le_sqrt_two : ‖complexSourceMap hm U‖ ≤ Real.sqrt 2 :=
  Gaussian.norm_sourceMap_le_sqrt_two (sourceEmbedding hm U)

theorem complexSourceMap_ofReal_test (u : SourceTestSpace hm U) :
    complexSourceMap hm U
      (Gaussian.HilbertComplexification.ofReal (u : SourceHilbert hm U)) = timeZeroL2 hm u.1 := by
  erw [complexSourceMap, Gaussian.sourceMap_ofReal, sourceEmbedding_coe]

variable {U} {V : Set (EuclideanSpace ℝ (Fin 3))} (hUV : U ⊆ V)

/-- The complexification of the actual real source inclusion. -/
noncomputable def complexSourceInclusion :
    ComplexSourceHilbert hm U →ₗᵢ[ℂ] ComplexSourceHilbert hm V :=
  Gaussian.complexifyIsometry (sourceInclusion hm hUV)

theorem complexSourceMap_comp_inclusion :
    (complexSourceMap hm V).comp (complexSourceInclusion hm hUV).toContinuousLinearMap =
      complexSourceMap hm U := by
  unfold complexSourceMap complexSourceInclusion
  erw [Gaussian.sourceMap_comp_complexifyIsometry, sourceEmbedding_comp_inclusion]

/-- The smaller physical Gram operator is the compression of the larger one. -/
theorem sourceGram_compression :
    (complexSourceInclusion hm hUV).toContinuousLinearMap.adjoint.comp
      ((sourceGram hm V).comp (complexSourceInclusion hm hUV).toContinuousLinearMap) =
        sourceGram hm U := by
  have hmap := complexSourceMap_comp_inclusion hm hUV
  unfold sourceGram
  rw [← hmap, ContinuousLinearMap.adjoint_comp]
  simp only [ContinuousLinearMap.comp_assoc]

end VacuumBellSeparation
