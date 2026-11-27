/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.FixedGaussianExistence

/-!
# Actual Williamson diagonalization of a physical Gaussian density

For a physical covariance factorization V = S D Sᵀ, the label matrix
Sᵀ Ω includes the displacement/physical rotation explicitly. Its
constructed unitary pulls the actual thermal product density back to the
unique physical Gaussian density. Thus an existing density is identified
as an actual unitary conjugate, and its true CFC power trace is available.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix

variable {m : ℕ}

/-- Physical Williamson label given by `Sᵀ * modeSymplecticForm`. -/
def physicalWilliamsonLabel (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ := Sᵀ * modeSymplecticForm

theorem physicalWilliamsonLabel_symplectic
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) :
    (physicalWilliamsonLabel S)ᵀ * modeSymplecticForm * physicalWilliamsonLabel S =
      modeSymplecticForm := by
  rw [physicalWilliamsonLabel, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    _ = modeSymplecticFormᵀ * (S * modeSymplecticForm * Sᵀ) * modeSymplecticForm := by
      noncomm_ring
    _ = _ := by rw [hS, modeSymplecticForm_transpose_mul, Matrix.one_mul]

theorem physicalWilliamsonLabel_covariance
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (D : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    (physicalWilliamsonLabel S)ᵀ * D * physicalWilliamsonLabel S =
      physicalDisplacementCovariance (S * D * Sᵀ) := by
  simp only [physicalWilliamsonLabel, Matrix.transpose_mul, Matrix.transpose_transpose,
    physicalDisplacementCovariance]
  noncomm_ring

/-- Continuous linear map for the physical Williamson density, of type `MultiModeOscillatorSpace m
→L[ℂ] MultiModeOscillatorSpace m`. -/
def physicalWilliamsonDensity
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) (ν : Fin m → ℝ) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  matrixDensityPullback (physicalWilliamsonLabel S) (physicalWilliamsonLabel_symplectic S hS)
    (covarianceProductDensity ν)

theorem physicalWilliamsonDensity_isPositiveTraceClass
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j) :
    IsPositiveTraceClass (physicalWilliamsonDensity S hS ν) :=
  matrixDensityPullback_isPositiveTraceClass _ _ (covarianceProductDensity_isPositiveTraceClass hν)

theorem physicalWilliamsonDensity_hasGaussianPhysicalCharacteristic
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j) :
    HasGaussianPhysicalCharacteristic (physicalWilliamsonDensity S hS ν)
      (S * modeDiagonal ν * Sᵀ) := by
  have h := matrixDensityPullback_hasGaussianDisplacementCharacteristic
    (physicalWilliamsonLabel S) (physicalWilliamsonLabel_symplectic S hS)
    (covarianceProductDensity_isPositiveTraceClass hν)
    (covarianceProductDensity_hasGaussianDisplacementCharacteristic hν)
  rwa [physicalWilliamsonLabel_covariance] at h

/-- An existing actual Gaussian density equals its constructed
Williamson unitary model on the same canonical Hilbert space. -/
theorem gaussianPhysical_eq_physicalWilliamsonDensity
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (hG : HasGaussianPhysicalCharacteristic A (S * modeDiagonal ν * Sᵀ)) :
    A = physicalWilliamsonDensity S hS ν :=
  gaussianPhysical_density_unique hA (physicalWilliamsonDensity_isPositiveTraceClass S hS hν)
    hG (physicalWilliamsonDensity_hasGaussianPhysicalCharacteristic S hS hν)

theorem positiveTrace_physicalWilliamsonDensity_rpow
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j) {r : ℝ} (hr : 0 < r) :
    positiveTrace (physicalWilliamsonDensity S hS ν ^ r) =
      ENNReal.ofReal (∏ j, (1 - covarianceThermalParameter (ν j)) ^ r /
        (1 - covarianceThermalParameter (ν j) ^ r)) := by
  calc
    positiveTrace (physicalWilliamsonDensity S hS ν ^ r) =
        positiveTrace (covarianceProductDensity ν ^ r) := by
      exact positiveTrace_conjStarAlgEquiv_rpow
        (E := MultiModeOscillatorSpace m) (F := MultiModeOscillatorSpace m)
        (symplecticWeylImplementer (matrixWeylLabelMap_preservesWeylForm
          (physicalWilliamsonLabel S) (physicalWilliamsonLabel_symplectic S hS))).symm
        (A := covarianceProductDensity ν) (τ := r)
        (covarianceProductDensity_nonneg hν) hr.le
    _ = _ := positiveTrace_multiModeThermalDensity_rpow
      (fun j => covarianceThermalParameter_nonneg (hν j))
      (fun j => covarianceThermalParameter_lt_one (hν j)) hr

theorem positiveTrace_gaussianPhysical_rpow
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (hG : HasGaussianPhysicalCharacteristic A (S * modeDiagonal ν * Sᵀ))
    {r : ℝ} (hr : 0 < r) :
    positiveTrace (A ^ r) = ENNReal.ofReal
      (∏ j, (1 - covarianceThermalParameter (ν j)) ^ r /
        (1 - covarianceThermalParameter (ν j) ^ r)) := by
  rw [gaussianPhysical_eq_physicalWilliamsonDensity hA S hS hν hG]
  exact positiveTrace_physicalWilliamsonDensity_rpow S hS hν hr

end VacuumBellSeparation.Gaussian
