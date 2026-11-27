/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.FiniteSourceComplex
public import LeanPool.VacuumBellSeparation.FreeField.FiniteCanonicalCoordinates
public import LeanPool.VacuumBellSeparation.FreeField.SourceReserve
public import LeanPool.VacuumBellSeparation.Gaussian.WhitenedComplexFamily

/-!
# Actual finite source embeddings in covariance-normalized coordinates

The vectors are the original finite source basis included in the actual
completed regional source space. Their literal Fourier covariance Gram
matrix supplies the inverse-square-root whitening. The resulting complex
isometry compresses the actual completed source commutation operator to
the finite normalized covariance/symplectic matrix. No compression or
Gaussian model identity is a structure assumption.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation

open Gaussian Matrix
open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {m : ℝ} (hm : 0 < m) (S : Submodule ℝ TimeZeroSource)
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (b : Module.Basis ι ℝ (FiniteSourceSpace hm S))
  {U : Set (EuclideanSpace ℝ (Fin 3))} (hSU : S ≤ localizedTimeZeroSources U)

/-- The original finite source family mapped into the joint source space. -/
def includedFiniteSourceFamily : ι → SourceHilbert hm U :=
  fun i => finiteSourceInclusion hm S hSU (b i)

omit [Fintype ι] [DecidableEq ι] in
theorem includedFiniteSourceFamily_linearIndependent :
    LinearIndependent ℝ (includedFiniteSourceFamily hm S b hSU) := by
  exact b.linearIndependent.map' (finiteSourceInclusion hm S hSU).toLinearMap
    (LinearMap.ker_eq_bot.mpr (finiteSourceInclusion hm S hSU).injective)

omit [Fintype ι] [DecidableEq ι] in
theorem includedFiniteSourceFamily_gram :
    realFamilyGram (includedFiniteSourceFamily hm S b hSU) =
      finiteSourceCovarianceMatrix hm S b := by
  ext i j
  change inner ℝ (finiteSourceInclusion hm S hSU (b i))
    (finiteSourceInclusion hm S hSU (b j)) = _
  rw [(finiteSourceInclusion hm S hSU).inner_map_map, finiteSourceSpace_inner]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem includedFiniteSourceFamily_commutation_form :
    realFamilyForm (includedFiniteSourceFamily hm S b hSU) (sourceCommutation hm U) =
      finiteSourceSymplecticMatrix hm S b := by
  ext i j
  exact sourceCommutation_symplectic hm U
    (finiteSourceTestInclusion hm S hSU (b i)) (finiteSourceTestInclusion hm S hSU (b j))

omit [Fintype ι] [DecidableEq ι] in
/-- Strict real covariance follows from the original basis and physical
source inclusion, without a quantum-density premise. -/
theorem finiteSourceCovarianceMatrix_posDef : (finiteSourceCovarianceMatrix hm S b).PosDef := by
  have hg : finiteSourceCovarianceMatrix hm S b = Matrix.gram ℝ b := by
    ext i j
    exact (finiteSourceSpace_inner hm S (b i) (b j)).symm
  rw [hg]
  exact Matrix.posDef_gram_of_linearIndependent b.linearIndependent

/-- The actual source isometry in covariance-normalized coordinates. -/
def finiteSourceCompressionIsometry :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] ComplexSourceHilbert hm U :=
  whitenedComplexFamily (includedFiniteSourceFamily hm S b hSU)
    (includedFiniteSourceFamily_linearIndependent hm S b hSU)

theorem finiteSourceCompressionIsometry_toCLM :
    (finiteSourceCompressionIsometry hm S b hSU).toContinuousLinearMap =
      (complexFamilySynthesis (includedFiniteSourceFamily hm S b hSU)).comp
        (realMatrixOperator ((CFC.sqrt (finiteSourceCovarianceMatrix hm S b))⁻¹)) := by
  rw [finiteSourceCompressionIsometry, whitenedComplexFamily_toCLM, whitenedComplexFamilyMap,
    includedFiniteSourceFamily_gram]

/-- The completed source J is compressed to the literal finite normalized
symplectic form. The i/2 convention is the source Gram convention. -/
theorem finiteSourceCompression_normalized_commutation :
    compression (finiteSourceCompressionIsometry hm S b hSU)
        (normalizedCommutation (complexSourceCommutation hm U)) =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (covarianceCommutationMatrix
        (finiteSourceCovarianceMatrix hm S b)
        (finiteSourceSymplecticMatrix hm S b)) := by
  have h := compression_whitened_normalizedCommutation
    (includedFiniteSourceFamily hm S b hSU)
    (includedFiniteSourceFamily_linearIndependent hm S b hSU) (sourceCommutation hm U)
  rw [includedFiniteSourceFamily_gram, includedFiniteSourceFamily_commutation_form] at h
  exact h

theorem finiteSourceCompression_normalized_commutation_canonical {n : ℕ}
    (c : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
    (hcanonical : finiteSourceSymplecticMatrix hm S c = modeSymplecticForm) :
    compression (finiteSourceCompressionIsometry hm S c hSU)
        (normalizedCommutation (complexSourceCommutation hm U)) =
      (Matrix.toEuclideanCLM (n := Fin n × Fin 2) (𝕜 := ℂ)) (covarianceCommutationMatrix
        (finiteSourceCovarianceMatrix hm S c)
        modeSymplecticForm) := by
  rw [finiteSourceCompression_normalized_commutation, hcanonical]

theorem finiteSourceCompression_thermal_weight {n : ℕ}
    (c : Module.Basis (Fin n × Fin 2) ℝ (FiniteSourceSpace hm S))
    (hcanonical : finiteSourceSymplecticMatrix hm S c = modeSymplecticForm)
    {σ : MultiModeOscillatorSpace n →L[ℂ] MultiModeOscillatorSpace n}
    (hσ : IsFaithfulDensity σ)
    (hG : HasGaussianPhysicalCharacteristic σ (finiteSourceCovarianceMatrix hm S c))
    {τ : ℝ} (hτ : 0 < τ) :
    normalizedThermal τ (compression (finiteSourceCompressionIsometry hm S c hSU)
      (normalizedCommutation (complexSourceCommutation hm U))) =
      realMatrixOperator (relativeCovariancePerturbation (finiteSourceCovarianceMatrix hm S c)
        (gaussianPowerIncrement σ τ)) := by
  rw [finiteSourceCompression_normalized_commutation_canonical hm S hSU c hcanonical]
  exact (gaussian_power_increment_operator_eq_normalizedThermal hσ
    (finiteSourceCovarianceMatrix_posDef hm S c).isHermitian hG hτ).symm

end VacuumBellSeparation
