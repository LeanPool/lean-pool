/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianUnitaryTransport
public import LeanPool.VacuumBellSeparation.Gaussian.StrictQuantumWilliamson
public import LeanPool.VacuumBellSeparation.Gaussian.DensityCharacteristicUniqueness

/-!
# Actual Gaussian density existence and uniqueness in a fixed representation

The proved finite Williamson factorization and the constructed symplectic
implementer transport an actual product thermal density onto the original
canonical Weyl representation. An explicit Ω rotation distinguishes
physical covariance from displacement-label covariance. Strict quantum
uncertainty yields actual injectivity of the resulting density; no bounded
inverse is asserted. Characteristic uniqueness identifies every density
with the same covariance with this construction.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {m : ℕ}

theorem exists_fixed_gaussian_displacement_density
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosSemidef) :
    ∃ A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass A ∧ HasGaussianDisplacementCharacteristic A V := by
  obtain ⟨n, ν, S, T, hcard, hν, hST, hTS, hsymp, hcov⟩ :=
    exists_quantum_williamson_factorization V modeSymplecticForm hV
      transpose_modeSymplecticForm (modeSymplecticForm_isUnit m) hQ
  have hnm : n = m := by
    simp only [Fintype.card_prod, Fintype.card_fin] at hcard
    omega
  subst n
  have hS : Sᵀᵀ * modeSymplecticForm * Sᵀ = modeSymplecticForm := by
    simpa only [Matrix.transpose_transpose] using hsymp
  refine ⟨matrixDensityPullback Sᵀ hS (covarianceProductDensity ν),
    matrixDensityPullback_isPositiveTraceClass Sᵀ hS
      (covarianceProductDensity_isPositiveTraceClass hν), ?_⟩
  have h := williamsonDensity_hasGaussianDisplacementCharacteristic hν S hsymp
  rwa [hcov] at h

theorem exists_fixed_faithful_gaussian_displacement_density
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef) :
    ∃ A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsFaithfulDensity A ∧ HasGaussianDisplacementCharacteristic A V := by
  obtain ⟨n, ν, S, T, hcard, _, hST, hTS, hsymp, hcov⟩ :=
    exists_quantum_williamson_factorization V modeSymplecticForm hV
      transpose_modeSymplecticForm (modeSymplecticForm_isUnit m) hQ.posSemidef
  have hν := strict_quantum_williamson_variances V modeSymplecticForm ν S T hTS hsymp hcov hQ
  have hnm : n = m := by
    simp only [Fintype.card_prod, Fintype.card_fin] at hcard
    omega
  subst n
  have hS : Sᵀᵀ * modeSymplecticForm * Sᵀ = modeSymplecticForm := by
    simpa only [Matrix.transpose_transpose] using hsymp
  refine ⟨matrixDensityPullback Sᵀ hS (covarianceProductDensity ν),
    matrixDensityPullback_isFaithfulDensity Sᵀ hS
      (covarianceProductDensity_isFaithfulDensity hν), ?_⟩
  have h := williamsonDensity_hasGaussianDisplacementCharacteristic (fun j => (hν j).le) S hsymp
  rwa [hcov] at h

theorem quantumCovariance_physical_rotation
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :
    quantumCovariance (physicalDisplacementCovariance V) modeSymplecticForm =
      complexifyMatrix modeSymplecticFormᵀ * quantumCovariance V modeSymplecticForm *
        (complexifyMatrix modeSymplecticFormᵀ)ᴴ := by
  have h := quantumCovariance_congruence V modeSymplecticForm modeSymplecticFormᵀ
  simpa only [Matrix.transpose_transpose, modeSymplecticForm_transpose_mul,
    Matrix.one_mul, physicalDisplacementCovariance] using h

theorem quantumCovariance_physical_rotation_posSemidef
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hQ : (quantumCovariance V modeSymplecticForm).PosSemidef) :
    (quantumCovariance (physicalDisplacementCovariance V) modeSymplecticForm).PosSemidef := by
  rw [quantumCovariance_physical_rotation]
  exact hQ.mul_mul_conjTranspose_same _

theorem quantumCovariance_physical_rotation_posDef
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef) :
    (quantumCovariance (physicalDisplacementCovariance V) modeSymplecticForm).PosDef := by
  have hright : complexifyMatrix (modeSymplecticForm (ι := Fin m))ᵀ *
      complexifyMatrix modeSymplecticForm = 1 := by
    rw [← complexifyMatrix_mul, modeSymplecticForm_transpose_mul]
    ext i j
    by_cases hij : i = j <;> simp [complexifyMatrix, Matrix.one_apply, hij]
  have hinj : Function.Injective (complexifyMatrix (modeSymplecticForm (ι := Fin m))ᵀ).vecMul := by
    intro x y hxy
    have h := congrArg (fun z => z ᵥ* complexifyMatrix (modeSymplecticForm (ι := Fin m))) hxy
    simpa only [Matrix.vecMul_vecMul, hright, Matrix.vecMul_one] using h
  rw [quantumCovariance_physical_rotation]
  exact hQ.mul_mul_conjTranspose_same hinj

/-- Actual positive trace-class Gaussian density on the fixed canonical
Weyl representation for every strictly positive quantum covariance. Pure
modes are included when the uncertainty matrix is only semidefinite. -/
theorem exists_fixed_gaussian_physical_density
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosSemidef) :
    ∃ A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass A ∧ HasGaussianPhysicalCharacteristic A V :=
  exists_fixed_gaussian_displacement_density (physicalDisplacementCovariance V)
    (physicalDisplacementCovariance_posDef hV) (quantumCovariance_physical_rotation_posSemidef hQ)

theorem exists_fixed_faithful_gaussian_physical_density
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef) :
    ∃ A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsFaithfulDensity A ∧ HasGaussianPhysicalCharacteristic A V :=
  exists_fixed_faithful_gaussian_displacement_density (physicalDisplacementCovariance V)
    (physicalDisplacementCovariance_posDef hV) (quantumCovariance_physical_rotation_posDef hQ)

/-- The density is unique on this fixed Hilbert space, not just unique
up to an unproved equivalence of representations. -/
theorem exists_unique_fixed_gaussian_physical_density
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosSemidef) :
    ∃! A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass A ∧ HasGaussianPhysicalCharacteristic A V := by
  obtain ⟨A, hA, hGA⟩ := exists_fixed_gaussian_physical_density V hV hQ
  refine ⟨A, ⟨hA, hGA⟩, ?_⟩
  rintro B ⟨hB, hGB⟩
  exact gaussianPhysical_density_unique hB hA hGB hGA

theorem gaussianPhysical_isFaithfulDensity_of_strict_uncertainty
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef)
    (hG : HasGaussianPhysicalCharacteristic A V) : IsFaithfulDensity A := by
  obtain ⟨B, hB, hGB⟩ := exists_fixed_faithful_gaussian_physical_density V hV hQ
  have he := gaussianPhysical_density_unique hA hB.isPositiveTraceClass hG hGB
  exact he.symm ▸ hB

end VacuumBellSeparation.Gaussian
