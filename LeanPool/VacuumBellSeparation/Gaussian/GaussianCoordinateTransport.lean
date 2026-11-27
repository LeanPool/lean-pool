/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianWilliamsonSandwich
public import LeanPool.VacuumBellSeparation.Gaussian.QuantumRealCovariance
public import LeanPool.VacuumBellSeparation.Gaussian.RelativeCovarianceCongruence
public import LeanPool.VacuumBellSeparation.Gaussian.SymplecticPurityCongruence

/-!
# Actual covariance coordinates for a common canonical Gaussian system

Both the operator norm and the nuclear norm of the normalized covariance
perturbation are invariant under the genuine orthogonal change induced
by a real congruence. Actual inverse symplectic coordinates pull a Gaussian
density back into thermal coordinates, and characteristic uniqueness
recovers the original operator without a metaplectic group-law premise.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_real_orthogonal_conjugate (O A : Matrix ι ι ℝ) (hO : Oᵀ * O = 1) :
    ‖O * A * Oᵀ‖ = ‖A‖ := by
  let U : unitary (Matrix ι ι ℝ) := ⟨O, by
    change Oᵀ * O = 1 ∧ O * Oᵀ = 1
    exact ⟨hO, mul_eq_one_comm.mp hO⟩⟩
  change ‖(U : Matrix ι ι ℝ) * A * ((star U : unitary (Matrix ι ι ℝ)) : Matrix ι ι ℝ)‖ = ‖A‖
  rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

theorem norm_relativeCovariancePerturbation_congruence
    (S : Matrix ι ι ℝ) {V : Matrix ι ι ℝ}
    (hV : V.PosDef) (hW : (S * V * Sᵀ).PosDef) (Δ : Matrix ι ι ℝ) :
    ‖relativeCovariancePerturbation (S * V * Sᵀ) (S * Δ * Sᵀ)‖ =
      ‖relativeCovariancePerturbation V Δ‖ := by
  rw [relativeCovariancePerturbation_congruence S hV hW,
    norm_real_orthogonal_conjugate _ _ (relativeCongruenceOrthogonal_transpose_mul S hV hW)]

variable {m : ℕ}

theorem canonical_symplectic_inv
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) :
    S⁻¹ * modeSymplecticForm * (S⁻¹)ᵀ = modeSymplecticForm := by
  have hiS := S.nonsing_inv_mul ((Matrix.isUnit_iff_isUnit_det S).mp
    (canonical_symplectic_isUnit S hS))
  calc
    _ = S⁻¹ * (S * modeSymplecticForm * Sᵀ) * (S⁻¹)ᵀ := by rw [hS]
    _ = (S⁻¹ * S) * modeSymplecticForm * (S⁻¹ * S)ᵀ := by
      simp only [Matrix.transpose_mul]
      noncomm_ring
    _ = _ := by rw [hiS, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem canonical_congruence_inverse_cancel
    (S V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) :
    S * (S⁻¹ * V * (S⁻¹)ᵀ) * Sᵀ = V := by
  have hSi := S.mul_nonsing_inv ((Matrix.isUnit_iff_isUnit_det S).mp
    (canonical_symplectic_isUnit S hS))
  calc
    _ = (S * S⁻¹) * V * (S * S⁻¹)ᵀ := by
      simp only [Matrix.transpose_mul]
      noncomm_ring
    _ = _ := by rw [hSi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem quantumCovariance_symplectic_congruence_posDef
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef) :
    (quantumCovariance (S * V * Sᵀ) modeSymplecticForm).PosDef := by
  have h := hQ.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit
    (complexifyMatrix_isUnit (canonical_symplectic_isUnit S hS)))
  rwa [← quantumCovariance_congruence, hS] at h

/-- Continuous linear map for the gaussian inverse coordinates, of type `MultiModeOscillatorSpace m
→L[ℂ] MultiModeOscillatorSpace m`. -/
def gaussianInverseCoordinates
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  physicalDensityPullback S⁻¹ (canonical_symplectic_inv S hS) A

theorem gaussianInverseCoordinates_isPositiveTraceClass
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) : IsPositiveTraceClass (gaussianInverseCoordinates S hS A) :=
  physicalDensityPullback_isPositiveTraceClass _ _ hA

theorem gaussianInverseCoordinates_hasGaussianPhysicalCharacteristic
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V) :
    HasGaussianPhysicalCharacteristic (gaussianInverseCoordinates S hS A)
      (S⁻¹ * V * (S⁻¹)ᵀ) :=
  physicalDensityPullback_hasGaussianPhysicalCharacteristic _ _ hA hG

theorem physicalDensityPullback_gaussianInverseCoordinates
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V) :
    physicalDensityPullback S hS (gaussianInverseCoordinates S hS A) = A := by
  have hB := gaussianInverseCoordinates_isPositiveTraceClass S hS hA
  apply gaussianPhysical_density_unique
    (physicalDensityPullback_isPositiveTraceClass S hS hB) hA
  · have h := physicalDensityPullback_hasGaussianPhysicalCharacteristic S hS hB
      (gaussianInverseCoordinates_hasGaussianPhysicalCharacteristic S hS hA hG)
    rwa [canonical_congruence_inverse_cancel S V hS] at h
  · exact hG

end VacuumBellSeparation.Gaussian
