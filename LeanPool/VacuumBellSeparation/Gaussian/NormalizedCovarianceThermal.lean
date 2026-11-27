/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.IntrinsicGaussianRenyiBound
public import LeanPool.VacuumBellSeparation.Gaussian.SymplecticHamiltonianNormalForm
public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCovarianceBridge

/-!
# The actual normalized covariance increment as a thermal CFC

The normalized commutation matrix is literally i V^(-1/2) Ω V^(-1/2)/2.
Its thermal functional calculus is the covariance-normalized difference
between the actual normalized density power covariance and V. The proof
uses genuine Williamson coordinates and their orthogonal normalization;
no covariance power rule is assumed. Pure mode parameters remain allowed
in this identity, although later inverse thermal normalization needs a
faithful reference and an exponent strictly below one.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Covariance commutation matrix given by `(Complex.I / 2) • complexifyMatrix
(relativeCovariancePerturbation V Ω)`. -/
def covarianceCommutationMatrix (V Ω : Matrix ι ι ℝ) : Matrix ι ι ℂ :=
  (Complex.I / 2) • complexifyMatrix (relativeCovariancePerturbation V Ω)

theorem covarianceCommutationMatrix_congruence
    (S Ω : Matrix ι ι ℝ) {V : Matrix ι ι ℝ}
    (hV : V.PosDef) (hW : (S * V * Sᵀ).PosDef) :
    covarianceCommutationMatrix (S * V * Sᵀ) (S * Ω * Sᵀ) =
      complexifyMatrix (relativeCongruenceOrthogonal S V) *
        covarianceCommutationMatrix V Ω *
          (complexifyMatrix (relativeCongruenceOrthogonal S V))ᴴ := by
  rw [covarianceCommutationMatrix,
    relativeCovariancePerturbation_congruence S hV hW Ω,
    complexifyMatrix_mul, complexifyMatrix_mul, complexifyMatrix_transpose,
    covarianceCommutationMatrix, Matrix.mul_smul, Matrix.smul_mul]

variable {m : ℕ}

theorem relativeCovariancePerturbation_mode_diagonal
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j) (d : Fin m → ℝ) :
    relativeCovariancePerturbation (modeDiagonal ν) (modeDiagonal d) =
      modeDiagonal (fun j => d j / ν j) := by
  rw [relativeCovariancePerturbation, modeDiagonal_sqrt (fun j => (hν j).le),
    modeDiagonal_inv (fun j => (Real.sqrt_pos.mpr (hν j)).ne'),
    modeDiagonal_mul, modeDiagonal_mul]
  congr 1
  funext j
  have hs : (Real.sqrt (ν j)) ^ 2 = ν j := Real.sq_sqrt (hν j).le
  calc
    _ = d j / (Real.sqrt (ν j)) ^ 2 := by ring
    _ = _ := by rw [hs]

theorem relativeCovariancePerturbation_mode_symplectic
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j) :
    relativeCovariancePerturbation (modeDiagonal ν) modeSymplecticForm =
      modeDiagonal (fun j => (ν j)⁻¹) * modeSymplecticForm := by
  let R := modeDiagonal (fun j => (Real.sqrt (ν j))⁻¹)
  have hc : Commute R modeSymplecticForm := modeDiagonal_commute_symplectic _
  have hRR : R * R = modeDiagonal (fun j => (ν j)⁻¹) := by
    dsimp only [R]
    rw [modeDiagonal_mul]
    congr 1
    funext j
    rw [← mul_inv, Real.mul_self_sqrt (hν j).le]
  rw [relativeCovariancePerturbation, modeDiagonal_sqrt (fun j => (hν j).le),
    modeDiagonal_inv (fun j => (Real.sqrt_pos.mpr (hν j)).ne')]
  change R * modeSymplecticForm * R = _
  rw [mul_assoc, ← hc.eq, ← mul_assoc, hRR]

theorem covarianceCommutationMatrix_mode_diagonal
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j) :
    covarianceCommutationMatrix (modeDiagonal ν) modeSymplecticForm =
      modeHamiltonian (fun j => (2 * ν j)⁻¹) := by
  rw [covarianceCommutationMatrix, relativeCovariancePerturbation_mode_symplectic hν,
    modeHamiltonian, complexifyMatrix_mul, complexifyMatrix_mul,
    complexifyMatrix_modeDiagonal, complexifyMatrix_modeDiagonal]
  rw [← Matrix.smul_mul, ← Matrix.smul_mul]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq, smul_eq_mul,
      Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_ofNat, _root_.mul_inv_rev]
    ring
  · simp [Matrix.diagonal_apply_ne _ h]

theorem covarianceCommutationMatrix_thermal_coordinates
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    covarianceCommutationMatrix (S * thermalReferenceCovariance q * Sᵀ)
        modeSymplecticForm =
      complexifyMatrix (relativeCongruenceOrthogonal S (thermalReferenceCovariance q)) *
        modeHamiltonian (fun j => thermalCommutationMagnitude (q j)) *
          (complexifyMatrix (relativeCongruenceOrthogonal S (thermalReferenceCovariance q)))ᴴ := by
  have hv (j : Fin m) : 0 < thermalQuadratureVariance (q j) := by
    have h := half_le_thermalQuadratureVariance (hq₀ j) (hq₁ j)
    linarith
  have hD : (thermalReferenceCovariance q).PosDef := modeDiagonal_posDef hv
  have hW := canonical_symplectic_congruence_posDef S hS hD
  rw [← hS, covarianceCommutationMatrix_congruence S modeSymplecticForm hD hW]
  congr 2
  change covarianceCommutationMatrix (modeDiagonal _) modeSymplecticForm = _
  rw [covarianceCommutationMatrix_mode_diagonal hv]
  congr 1
  funext j
  exact (thermalCommutationMagnitude_eq_inv_twice_variance (hq₀ j) (hq₁ j)).symm

theorem relativeCovariancePerturbation_thermal_gap
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    {τ : ℝ} (hτ : 0 < τ) :
    relativeCovariancePerturbation (thermalReferenceCovariance q) (thermalReferenceGap q τ) =
      modeDiagonal (fun j => thermalIncrement τ (thermalCommutationMagnitude (q j))) := by
  have hv (j : Fin m) : 0 < thermalQuadratureVariance (q j) := by
    have h := half_le_thermalQuadratureVariance (hq₀ j) (hq₁ j)
    linarith
  have hg : thermalReferenceGap q τ =
      modeDiagonal (fun j => thermalQuadratureVariance (q j ^ τ) -
        thermalQuadratureVariance (q j)) := Matrix.diagonal_sub _ _
  rw [hg, thermalReferenceCovariance, relativeCovariancePerturbation_mode_diagonal hv]
  congr 1
  funext j
  rw [thermalIncrement_eq_relative_covariance (hq₀ j) (hq₁ j) hτ,
    sub_div, div_self (hv j).ne']

/-- Actual matrix equality before any inverse thermal weight is introduced. -/
theorem transported_thermal_gap_eq_cfc_commutation
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {q : Fin m → ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    {τ : ℝ} (hτ : 0 < τ) :
    complexifyMatrix (relativeCovariancePerturbation
      (S * thermalReferenceCovariance q * Sᵀ) (transportedThermalIncrement S q τ)) =
      cfc (thermalIncrement τ) (CFC.abs
        (covarianceCommutationMatrix (S * thermalReferenceCovariance q * Sᵀ)
          modeSymplecticForm)) := by
  have hv (j : Fin m) : 0 < thermalQuadratureVariance (q j) := by
    have h := half_le_thermalQuadratureVariance (hq₀ j) (hq₁ j)
    linarith
  have hD : (thermalReferenceCovariance q).PosDef := modeDiagonal_posDef hv
  have hW := canonical_symplectic_congruence_posDef S hS hD
  let U := orthogonalComplexUnitary
    (relativeCongruenceOrthogonal S (thermalReferenceCovariance q))
    (relativeCongruenceOrthogonal_transpose_mul S hD hW)
  have hn := covarianceCommutationMatrix_thermal_coordinates S hS hq₀ hq₁
  change covarianceCommutationMatrix (S * thermalReferenceCovariance q * Sᵀ)
    modeSymplecticForm = (U : Matrix _ _ ℂ) *
      modeHamiltonian (fun j => thermalCommutationMagnitude (q j)) * (U : Matrix _ _ ℂ)ᴴ at hn
  have hmag : (complexifyMatrix
      (modeDiagonal (fun j => thermalCommutationMagnitude (q j)))).IsHermitian :=
    (complexifyMatrix_posSemidef (modeDiagonal_posDef
      (fun j => thermalCommutationMagnitude_pos (hq₀ j) (hq₁ j))).posSemidef).isHermitian
  rw [hn, complex_matrix_abs_unitary_conjugate,
    abs_modeHamiltonian (fun j => (thermalCommutationMagnitude_pos (hq₀ j) (hq₁ j)).le),
    cfc_complex_unitary_conjugate U hmag (thermalIncrement τ),
    complexifyMatrix_modeDiagonal, cfc_complex_real_diagonal]
  rw [transportedThermalIncrement, relativeCovariancePerturbation_congruence S hD hW,
    relativeCovariancePerturbation_thermal_gap hq₀ hq₁ hτ,
    complexifyMatrix_mul, complexifyMatrix_mul, complexifyMatrix_transpose,
    complexifyMatrix_modeDiagonal]
  rfl

/-- The thermal matrix is the normalized increment of the actual density
power covariance, with no assumed covariance power rule. -/
theorem gaussian_power_increment_eq_cfc_commutation
    {σ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hσ : IsFaithfulDensity σ)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hV : V.IsHermitian) (hG : HasGaussianPhysicalCharacteristic σ V)
    {τ : ℝ} (hτ : 0 < τ) :
    complexifyMatrix (relativeCovariancePerturbation V (gaussianPowerIncrement σ τ)) =
      cfc (thermalIncrement τ) (CFC.abs (covarianceCommutationMatrix V modeSymplecticForm)) := by
  obtain ⟨q, S, hS, hq₀, hq₁, hcov, _⟩ :=
    exists_gaussian_reference_thermal_coordinates hσ.isPositiveTraceClass
      (actual_faithful_gaussian_quantum_posDef hσ hV hG) hG
  rw [gaussianPowerIncrement_in_coordinates S hS (fun j => (hq₀ j).le) hq₁
    hσ.isPositiveTraceClass hV hG hcov hτ, ← hcov]
  exact transported_thermal_gap_eq_cfc_commutation S hS (fun j => (hq₀ j).le) hq₁ hτ

end VacuumBellSeparation.Gaussian
