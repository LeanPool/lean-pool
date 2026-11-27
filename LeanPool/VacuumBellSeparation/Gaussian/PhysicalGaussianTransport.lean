/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianNormalizedPowers

/-!
# Unitary transport by a literal physical symplectic congruence

The label matrix Ωᵀ Sᵀ Ω converts physical covariance transport S V Sᵀ
to the displacement convention of the canonical Weyl family. Unlike a
thermal-only simplification, this formula applies to anisotropic inputs.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {m : ℕ}

/-- Physical congruence label given by `modeSymplecticFormᵀ * Sᵀ * modeSymplecticForm`. -/
def physicalCongruenceLabel (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ :=
  modeSymplecticFormᵀ * Sᵀ * modeSymplecticForm

theorem physicalCongruenceLabel_symplectic
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) :
    (physicalCongruenceLabel S)ᵀ * modeSymplecticForm * physicalCongruenceLabel S =
      modeSymplecticForm := by
  simp only [physicalCongruenceLabel, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = modeSymplecticFormᵀ * S *
        (modeSymplecticForm * modeSymplecticForm * modeSymplecticFormᵀ) *
        Sᵀ * modeSymplecticForm := by noncomm_ring
    _ = modeSymplecticFormᵀ * (S * modeSymplecticForm * Sᵀ) * modeSymplecticForm := by
      rw [Matrix.mul_assoc modeSymplecticForm modeSymplecticForm modeSymplecticFormᵀ,
        modeSymplecticForm_mul_transpose, Matrix.mul_one]
      noncomm_ring
    _ = modeSymplecticForm := by
      rw [hS, modeSymplecticForm_transpose_mul, Matrix.one_mul]

theorem physicalCongruenceLabel_covariance
    (S V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    (physicalCongruenceLabel S)ᵀ * physicalDisplacementCovariance V *
        physicalCongruenceLabel S = physicalDisplacementCovariance (S * V * Sᵀ) := by
  simp only [physicalCongruenceLabel, physicalDisplacementCovariance,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = modeSymplecticFormᵀ * S *
        (modeSymplecticForm * modeSymplecticFormᵀ) * V *
        (modeSymplecticForm * modeSymplecticFormᵀ) * Sᵀ * modeSymplecticForm := by
      noncomm_ring
    _ = _ := by simp only [modeSymplecticForm_mul_transpose, Matrix.mul_one]; noncomm_ring

/-- Linear isometry equivalence for the physical congruence unitary, of type
`MultiModeOscillatorSpace m ≃ₗᵢ[ℂ] MultiModeOscillatorSpace m`. -/
def physicalCongruenceUnitary
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) :
    MultiModeOscillatorSpace m ≃ₗᵢ[ℂ] MultiModeOscillatorSpace m :=
  symplecticWeylImplementer
    (matrixWeylLabelMap_preservesWeylForm _ (physicalCongruenceLabel_symplectic S hS))

/-- Continuous linear map for the physical density pullback, of type `MultiModeOscillatorSpace m
→L[ℂ] MultiModeOscillatorSpace m`. -/
def physicalDensityPullback
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  (physicalCongruenceUnitary S hS).symm.conjStarAlgEquiv A

theorem physicalDensityPullback_eq_matrixDensityPullback
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    physicalDensityPullback S hS A =
      matrixDensityPullback (physicalCongruenceLabel S)
        (physicalCongruenceLabel_symplectic S hS) A := rfl

theorem physicalDensityPullback_isPositiveTraceClass
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) : IsPositiveTraceClass (physicalDensityPullback S hS A) :=
  IsPositiveTraceClass.conjStarAlgEquiv _ hA

theorem physicalDensityPullback_hasGaussianPhysicalCharacteristic
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V) :
    HasGaussianPhysicalCharacteristic (physicalDensityPullback S hS A) (S * V * Sᵀ) := by
  have h := matrixDensityPullback_hasGaussianDisplacementCharacteristic
    (physicalCongruenceLabel S) (physicalCongruenceLabel_symplectic S hS) hA hG
  rw [physicalCongruenceLabel_covariance] at h
  exact h

theorem physicalDensityPullback_covarianceProductDensity
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j) :
    physicalDensityPullback S hS (covarianceProductDensity ν) = physicalWilliamsonDensity S hS ν
      := by
  apply gaussianPhysical_density_unique
    (physicalDensityPullback_isPositiveTraceClass S hS
      (covarianceProductDensity_isPositiveTraceClass hν))
    (physicalWilliamsonDensity_isPositiveTraceClass S hS hν)
  · apply physicalDensityPullback_hasGaussianPhysicalCharacteristic S hS
      (covarianceProductDensity_isPositiveTraceClass hν)
    change HasGaussianDisplacementCharacteristic (covarianceProductDensity ν)
      (physicalDisplacementCovariance (modeDiagonal ν))
    rw [physicalDisplacementCovariance_modeDiagonal]
    exact covarianceProductDensity_hasGaussianDisplacementCharacteristic hν
  · exact physicalWilliamsonDensity_hasGaussianPhysicalCharacteristic S hS hν

end VacuumBellSeparation.Gaussian
