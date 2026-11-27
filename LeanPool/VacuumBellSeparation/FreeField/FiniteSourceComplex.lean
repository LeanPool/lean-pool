/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteSourceSpace
public import LeanPool.VacuumBellSeparation.FreeField.CompletedComplexInjectivity

/-!
# Strict finite physical Gram forms

The finite source inclusion into the actual regional completion is an
isometry and intertwines the physical maps. Complex injectivity follows
from the completed compact-support theorem. Thus strictness is proved for
the physical finite system, not postulated as a Gaussian model assumption.
-/

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

namespace VacuumBellSeparation

variable {m : ℝ} (hm : 0 < m) (S : Submodule ℝ TimeZeroSource)
  {U : Set (EuclideanSpace ℝ (Fin 3))} (hSU : S ≤ localizedTimeZeroSources U)

/-- Finite source test inclusion represented by `u.1`. -/
noncomputable def finiteSourceTestInclusion :
    FiniteSourceSpace hm S →ₗᵢ[ℝ] SourceTestSpace hm U where
  toFun u := ⟨u.1, hSU u.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  norm_map' _ := rfl

/-- The canonical inclusion of the genuine finite source space into the completion. -/
noncomputable def finiteSourceInclusion :
    FiniteSourceSpace hm S →ₗᵢ[ℝ] SourceHilbert hm U :=
  (UniformSpace.Completion.toComplₗᵢ :
    SourceTestSpace hm U →ₗᵢ[ℝ] SourceHilbert hm U).comp
      (finiteSourceTestInclusion hm S hSU)

theorem sourceEmbedding_comp_finiteSourceInclusion :
    (sourceEmbedding hm U).comp (finiteSourceInclusion hm S hSU) =
      finiteSourceIsometry hm S := by
  apply LinearIsometry.ext
  intro u
  exact sourceEmbedding_coe hm U (finiteSourceTestInclusion hm S hSU u)

variable [FiniteDimensional ℝ S]

/-- The complex extension of the actual finite physical source map. -/
noncomputable def finiteComplexSourceMap :
    Gaussian.HilbertComplexification (FiniteSourceSpace hm S) →L[ℂ]
      Lp ℂ 2 (oneParticleMeasure m) :=
  Gaussian.sourceMap (finiteSourceIsometry hm S)

omit [FiniteDimensional ℝ ↥S] in
theorem complexSourceMap_comp_finiteSourceInclusion :
    (complexSourceMap hm U).comp
      (Gaussian.complexifyIsometry (finiteSourceInclusion hm S hSU)).toContinuousLinearMap =
        finiteComplexSourceMap hm S := by
  apply ContinuousLinearMap.ext
  intro z
  change sourceEmbedding hm U (finiteSourceInclusion hm S hSU z.re) +
    Complex.I • sourceEmbedding hm U (finiteSourceInclusion hm S hSU z.im) =
    finiteSourceIsometry hm S z.re + Complex.I • finiteSourceIsometry hm S z.im
  have he (u : FiniteSourceSpace hm S) :
      sourceEmbedding hm U (finiteSourceInclusion hm S hSU u) =
        finiteSourceIsometry hm S u :=
    congrArg (fun i : FiniteSourceSpace hm S →ₗᵢ[ℝ] Lp ℂ 2 (oneParticleMeasure m) => i u)
      (sourceEmbedding_comp_finiteSourceInclusion hm S hSU)
  rw [he, he]

include hSU in
omit [FiniteDimensional ℝ ↥S] in
/-- Compact localization rules out a complex relation among the actual finite sources. -/
theorem finiteComplexSourceMap_injective (hU : Bornology.IsBounded U) :
    Function.Injective (finiteComplexSourceMap hm S) := by
  intro z w h
  apply (Gaussian.complexifyIsometry (finiteSourceInclusion hm S hSU)).injective
  apply complexSourceMap_injective hm U hU
  change ((complexSourceMap hm U).comp
      (Gaussian.complexifyIsometry (finiteSourceInclusion hm S hSU)).toContinuousLinearMap) z =
    ((complexSourceMap hm U).comp
      (Gaussian.complexifyIsometry (finiteSourceInclusion hm S hSU)).toContinuousLinearMap) w
  rwa [complexSourceMap_comp_finiteSourceInclusion]

/-- The finite Gram operator is defined through the actual Hilbert adjoint. -/
noncomputable def finiteSourceGram :
    Gaussian.HilbertComplexification (FiniteSourceSpace hm S) →L[ℂ]
      Gaussian.HilbertComplexification (FiniteSourceSpace hm S) :=
  (finiteComplexSourceMap hm S).adjoint.comp (finiteComplexSourceMap hm S)

theorem finiteSourceGram_eq_normalized_commutation :
    finiteSourceGram hm S = 1 + (Complex.I / 2) •
      Gaussian.complexCommutation (finiteSourceIsometry hm S) :=
  Gaussian.sourceMap_adjoint_mul_self (finiteSourceIsometry hm S)

include hSU in
theorem inner_finiteSourceGram_pos (hU : Bornology.IsBounded U)
    (z : Gaussian.HilbertComplexification (FiniteSourceSpace hm S)) (hz : z ≠ 0) :
    0 < (⟪z, finiteSourceGram hm S z⟫_ℂ).re := by
  change 0 < (⟪z, (finiteComplexSourceMap hm S).adjoint (finiteComplexSourceMap hm S z)⟫_ℂ).re
  rw [ContinuousLinearMap.adjoint_inner_right, ← RCLike.re_eq_complex_re]
  apply re_inner_self_pos.mpr
  intro h
  apply hz
  apply finiteComplexSourceMap_injective hm S hSU hU
  simpa only [map_zero] using h

end VacuumBellSeparation
