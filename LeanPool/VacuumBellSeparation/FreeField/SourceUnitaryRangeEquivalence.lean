/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SourceRangeIsometry
public import LeanPool.VacuumBellSeparation.FreeField.SourceReserve
public import LeanPool.VacuumBellSeparation.Gaussian.UnitaryTrace

/-!
# Actual source and reserve equivalence under a physical unitary

Both actual completed real-range inclusions are required. Surjectivity,
the complex Gram identity and every nonnegative reserve power then follow.
-/

@[expose] public section

namespace VacuumBellSeparation

open Gaussian Gaussian.HilbertComplexification MeasureTheory ContinuousLinearMap

variable {m : ℝ} (hm : 0 < m)
  {U W : Set (EuclideanSpace ℝ (Fin 3))}
  (T : Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m))
  (hT : ∀ z : SourceHilbert hm U, T (sourceEmbedding hm U z) ∈ sourceRealSpace hm W)
  (hTi : ∀ z : SourceHilbert hm W, T.symm (sourceEmbedding hm W z) ∈ sourceRealSpace hm U)

include hTi in
theorem sourceRangeIsometry_surjective : Function.Surjective (sourceRangeIsometry hm T hT) := by
  intro y
  refine ⟨sourceRangeIsometry hm T.symm hTi y, ?_⟩
  apply (sourceEmbedding hm W).injective
  rw [sourceEmbedding_rangeIsometry, sourceEmbedding_rangeIsometry,
    LinearIsometryEquiv.apply_symm_apply]

/-- Source unitary range equivalence of type `SourceHilbert hm U ≃ₗᵢ[ℝ] SourceHilbert hm W`. -/
noncomputable def sourceUnitaryRangeEquiv : SourceHilbert hm U ≃ₗᵢ[ℝ] SourceHilbert hm W :=
  LinearIsometryEquiv.ofSurjective (sourceRangeIsometry hm T hT)
    (sourceRangeIsometry_surjective hm T hT hTi)

theorem sourceEmbedding_unitaryRangeEquiv (z : SourceHilbert hm U) :
    sourceEmbedding hm W (sourceUnitaryRangeEquiv hm T hT hTi z) =
      T (sourceEmbedding hm U z) := sourceEmbedding_rangeIsometry hm T hT z

include hTi in
theorem complexSourceRangeIsometry_surjective :
    Function.Surjective (complexSourceRangeIsometry hm T hT) := by
  intro z
  let e := sourceUnitaryRangeEquiv hm T hT hTi
  refine ⟨mk (e.symm z.re) (e.symm z.im), ?_⟩
  apply HilbertComplexification.ext
  · exact e.apply_symm_apply z.re
  · exact e.apply_symm_apply z.im

/-- Complex source unitary range equivalence of type `ComplexSourceHilbert hm U ≃ₗᵢ[ℂ]
ComplexSourceHilbert hm W`. -/
noncomputable def complexSourceUnitaryRangeEquiv :
    ComplexSourceHilbert hm U ≃ₗᵢ[ℂ] ComplexSourceHilbert hm W :=
  LinearIsometryEquiv.ofSurjective (complexSourceRangeIsometry hm T hT)
    (complexSourceRangeIsometry_surjective hm T hT hTi)

theorem complexSourceMap_unitaryRangeEquiv (z : ComplexSourceHilbert hm U) :
    complexSourceMap hm W (complexSourceUnitaryRangeEquiv hm T hT hTi z) =
      T (complexSourceMap hm U z) := complexSourceMap_rangeIsometry hm T hT z

theorem sourceGram_unitaryRangeEquiv :
    (complexSourceUnitaryRangeEquiv hm T hT hTi).conjStarAlgEquiv (sourceGram hm U) =
      sourceGram hm W := by
  let e := complexSourceUnitaryRangeEquiv hm T hT hTi
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := e.surjective z
  apply ext_inner_left ℂ
  intro w
  obtain ⟨y, rfl⟩ := e.surjective w
  change inner ℂ (e y) (e ((sourceGram hm U) (e.symm (e x)))) =
    inner ℂ (e y) ((sourceGram hm W) (e x))
  rw [e.symm_apply_apply, e.inner_map_map]
  change inner ℂ y ((complexSourceMap hm U).adjoint (complexSourceMap hm U x)) =
    inner ℂ (e y) ((complexSourceMap hm W).adjoint (complexSourceMap hm W (e x)))
  rw [adjoint_inner_right, adjoint_inner_right]
  dsimp only [e]
  rw [complexSourceMap_unitaryRangeEquiv, complexSourceMap_unitaryRangeEquiv, T.inner_map_map]

theorem conjugateSourceGram_unitaryRangeEquiv :
    (complexSourceUnitaryRangeEquiv hm T hT hTi).conjStarAlgEquiv (conjugateSourceGram hm U) =
      conjugateSourceGram hm W := by
  rw [conjugateSourceGram_eq_two_sub, conjugateSourceGram_eq_two_sub,
    map_sub, map_ofNat, sourceGram_unitaryRangeEquiv]

theorem sourceReserve_unitaryRangeEquiv :
    (complexSourceUnitaryRangeEquiv hm T hT hTi).conjStarAlgEquiv (sourceReserve hm U) =
      sourceReserve hm W := by
  rw [sourceReserve, CFC.sqrt_eq_rpow,
    conjStarAlgEquiv_rpow _ (sourceGram_mul_conjugateSourceGram_nonneg hm U)
      (by norm_num : (0 : ℝ) ≤ 1 / 2), map_mul,
    sourceGram_unitaryRangeEquiv, conjugateSourceGram_unitaryRangeEquiv,
    sourceReserve, CFC.sqrt_eq_rpow]

theorem sourceReserve_rpow_unitaryRangeEquiv {b : ℝ} (hb : 0 ≤ b) :
    (complexSourceUnitaryRangeEquiv hm T hT hTi).conjStarAlgEquiv (sourceReserve hm U ^ b) =
      sourceReserve hm W ^ b := by
  rw [conjStarAlgEquiv_rpow _ (sourceReserve_nonneg hm U) hb, sourceReserve_unitaryRangeEquiv]

theorem sourceReserve_rpow_unitaryRangeEquiv_apply {b : ℝ} (hb : 0 ≤ b)
    (z : ComplexSourceHilbert hm U) :
    (sourceReserve hm W ^ b) (complexSourceUnitaryRangeEquiv hm T hT hTi z) =
      complexSourceUnitaryRangeEquiv hm T hT hTi ((sourceReserve hm U ^ b) z) := by
  rw [← sourceReserve_rpow_unitaryRangeEquiv hm T hT hTi hb,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_apply_apply]

end VacuumBellSeparation
