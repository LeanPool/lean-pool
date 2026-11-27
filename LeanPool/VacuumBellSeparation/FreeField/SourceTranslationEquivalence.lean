/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceUnitaryRangeEquivalence
public import LeanPool.VacuumBellSeparation.FreeField.SourceTranslation

/-!
# Translation of the actual completed sources and reserve powers

Both regional inclusions are discharged directly for the physical
translation by a and its inverse. Test agreement uses the original
translated compact Cauchy data, not an abstract covariance premise.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification

variable {m : ℝ} (hm : 0 < m) (a : EuclideanSpace ℝ (Fin 3))
  {U W : Set (EuclideanSpace ℝ (Fin 3))}
  (hUW : ∀ x ∈ U, x + a ∈ W) (hWU : ∀ x ∈ W, x - a ∈ U)

/-- Translated source test. -/
noncomputable def translatedSourceTest (x : SourceTestSpace hm U) : SourceTestSpace hm W :=
  ⟨timeZeroTranslate a x.1,
    spatialTestTranslate_support_subset hUW x.1.1 x.2.1,
    spatialTestTranslate_support_subset hUW x.1.2 x.2.2⟩

include hUW in
theorem sourceTranslation_forward_range (z : SourceHilbert hm U) :
    oneParticleSpatialTranslation m a (sourceEmbedding hm U z) ∈ sourceRealSpace hm W :=
  oneParticleSpatialTranslation_mem_sourceRealSpace hm a hUW ⟨z, rfl⟩

include hWU in
theorem sourceTranslation_inverse_range (z : SourceHilbert hm W) :
    (oneParticleSpatialTranslation m a).symm (sourceEmbedding hm W z) ∈ sourceRealSpace hm U := by
  rw [oneParticleSpatialTranslation_symm]
  exact oneParticleSpatialTranslation_mem_sourceRealSpace hm (-a)
    (fun x hx => by simpa only [sub_eq_add_neg] using hWU x hx) ⟨z, rfl⟩

/-- Linear isometry equivalence for the source spatial translation, of type `SourceHilbert hm U
≃ₗᵢ[ℝ] SourceHilbert hm W`. -/
noncomputable def sourceSpatialTranslation : SourceHilbert hm U ≃ₗᵢ[ℝ] SourceHilbert hm W :=
  sourceUnitaryRangeEquiv hm (oneParticleSpatialTranslation m a)
    (sourceTranslation_forward_range hm a hUW) (sourceTranslation_inverse_range hm a hWU)

/-- Linear isometry equivalence for the complex source spatial translation, of type
`ComplexSourceHilbert hm U ≃ₗᵢ[ℂ] ComplexSourceHilbert hm W`. -/
noncomputable def complexSourceSpatialTranslation :
    ComplexSourceHilbert hm U ≃ₗᵢ[ℂ] ComplexSourceHilbert hm W :=
  complexSourceUnitaryRangeEquiv hm (oneParticleSpatialTranslation m a)
    (sourceTranslation_forward_range hm a hUW) (sourceTranslation_inverse_range hm a hWU)

theorem sourceSpatialTranslation_coe (x : SourceTestSpace hm U) :
    sourceSpatialTranslation hm a hUW hWU (x : SourceHilbert hm U) =
      (translatedSourceTest hm a hUW x : SourceHilbert hm W) := by
  apply (sourceEmbedding hm W).injective
  rw [sourceSpatialTranslation, sourceEmbedding_unitaryRangeEquiv, sourceEmbedding_coe,
    sourceEmbedding_coe]
  exact (timeZeroL2_translate hm a x.1).symm

theorem complexSourceSpatialTranslation_ofReal (z : SourceHilbert hm U) :
    complexSourceSpatialTranslation hm a hUW hWU (ofReal z) =
      ofReal (sourceSpatialTranslation hm a hUW hWU z) := by
  apply HilbertComplexification.ext <;>
    simp [complexSourceSpatialTranslation, sourceSpatialTranslation,
      complexSourceUnitaryRangeEquiv, complexSourceRangeIsometry, sourceUnitaryRangeEquiv]

theorem complexSourceSpatialTranslation_test (x : SourceTestSpace hm U) :
    complexSourceSpatialTranslation hm a hUW hWU (ofReal (x : SourceHilbert hm U)) =
      ofReal (translatedSourceTest hm a hUW x : SourceHilbert hm W) := by
  rw [complexSourceSpatialTranslation_ofReal, sourceSpatialTranslation_coe]

theorem sourceReserve_rpow_spatialTranslation {b : ℝ} (hb : 0 ≤ b)
    (z : ComplexSourceHilbert hm U) :
    (sourceReserve hm W ^ b) (complexSourceSpatialTranslation hm a hUW hWU z) =
      complexSourceSpatialTranslation hm a hUW hWU ((sourceReserve hm U ^ b) z) :=
  sourceReserve_rpow_unitaryRangeEquiv_apply hm (oneParticleSpatialTranslation m a)
    (sourceTranslation_forward_range hm a hUW) (sourceTranslation_inverse_range hm a hWU) hb z

end VacuumBellSeparation
