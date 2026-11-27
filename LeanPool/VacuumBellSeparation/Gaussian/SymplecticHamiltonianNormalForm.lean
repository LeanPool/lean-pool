/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ModeHamiltonianAbsoluteValue
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianPurityTrace

/-!
# The actual Williamson value identity for Gaussian spectral purity

The real matrix V^(-1/2) S D^(1/2) is genuinely orthogonal. It conjugates
the literal Hermitian Hamiltonian i sqrt(V) Ω sqrt(V) to iDΩ. Its absolute
value and actual even CFC trace therefore give the Williamson mode sums.
The resulting purity functional equals the logarithm of the actual
Gaussian density power trace; no eigenbranch differentiability is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

variable {m : ℕ}

theorem canonical_symplectic_right_inverse
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) :
    S * (-modeSymplecticForm * Sᵀ * modeSymplecticForm) = 1 := by
  calc
    _ = -(S * modeSymplecticForm * Sᵀ) * modeSymplecticForm := by noncomm_ring
    _ = 1 := by rw [hS, Matrix.neg_mul, modeSymplecticForm_mul_self, neg_neg]

theorem canonical_symplectic_isUnit
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) : IsUnit S :=
  IsUnit.of_mul_eq_one _ (canonical_symplectic_right_inverse S hS)

theorem canonical_symplectic_transpose_congruence
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm) :
    Sᵀ * modeSymplecticForm * S = modeSymplecticForm := by
  have hTS : (-modeSymplecticForm * Sᵀ * modeSymplecticForm) * S = 1 :=
    mul_eq_one_comm.mpr (canonical_symplectic_right_inverse S hS)
  calc
    _ = (-(modeSymplecticForm * modeSymplecticForm)) *
        (Sᵀ * modeSymplecticForm * S) := by
      rw [modeSymplecticForm_mul_self, neg_neg, Matrix.one_mul]
    _ = modeSymplecticForm * ((-modeSymplecticForm * Sᵀ * modeSymplecticForm) * S) := by
      noncomm_ring
    _ = _ := by rw [hTS, Matrix.mul_one]

theorem canonical_williamson_covariance_posDef
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j) :
    (S * modeDiagonal ν * Sᵀ).PosDef := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (modeDiagonal_posDef hν).mul_mul_conjTranspose_same
      (Matrix.vecMul_injective_of_isUnit (canonical_symplectic_isUnit S hS))

/-- Williamson Hamiltonian unitary. -/
def williamsonHamiltonianUnitary
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (ν : Fin m → ℝ) (hν : ∀ j, 0 < ν j)
    (hW : (S * modeDiagonal ν * Sᵀ).PosDef) :
    unitary (Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) :=
  orthogonalComplexUnitary (relativeCongruenceOrthogonal S (modeDiagonal ν))
    (relativeCongruenceOrthogonal_transpose_mul S (modeDiagonal_posDef hν) hW)

theorem williamsonHamiltonian_real_normal_form
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j)
    (hW : (S * modeDiagonal ν * Sᵀ).PosDef) :
    (relativeCongruenceOrthogonal S (modeDiagonal ν))ᵀ *
        (CFC.sqrt (S * modeDiagonal ν * Sᵀ) * modeSymplecticForm *
          CFC.sqrt (S * modeDiagonal ν * Sᵀ)) *
        relativeCongruenceOrthogonal S (modeDiagonal ν) =
      modeDiagonal ν * modeSymplecticForm := by
  let R := CFC.sqrt (modeDiagonal ν)
  let Q := CFC.sqrt (S * modeDiagonal ν * Sᵀ)
  have hR := matrix_sqrt_posDef (modeDiagonal_posDef hν)
  have hQ := matrix_sqrt_posDef hW
  have hRt : Rᵀ = R := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hR.isHermitian.eq
  have hQit : (Q⁻¹)ᵀ = Q⁻¹ := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hQ.inv.isHermitian.eq
  have hQdet : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.isUnit
  have hQiQ : Q⁻¹ * Q = 1 := Q.nonsing_inv_mul hQdet
  have hQQi : Q * Q⁻¹ = 1 := Q.mul_nonsing_inv hQdet
  change (Q⁻¹ * S * R)ᵀ * (Q * modeSymplecticForm * Q) * (Q⁻¹ * S * R) = _
  simp only [Matrix.transpose_mul, hRt, hQit]
  calc
    _ = R * Sᵀ * (Q⁻¹ * Q) * modeSymplecticForm * (Q * Q⁻¹) * S * R := by
      noncomm_ring
    _ = R * (Sᵀ * modeSymplecticForm * S) * R := by
      rw [hQiQ, hQQi, Matrix.mul_one, Matrix.mul_one]
      noncomm_ring
    _ = R * modeSymplecticForm * R := by rw [canonical_symplectic_transpose_congruence S hS]
    _ = _ := by
      dsimp only [R]
      rw [modeDiagonal_sqrt (fun j => (hν j).le)]
      exact modeSqrt_symplectic_congruence ν (fun j => (hν j).le)

theorem williamsonHamiltonian_unitary_normal_form
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j)
    (hW : (S * modeDiagonal ν * Sᵀ).PosDef) :
    ((williamsonHamiltonianUnitary S ν hν hW : Matrix _ _ ℂ))ᴴ *
      symplecticHamiltonian modeSymplecticForm (S * modeDiagonal ν * Sᵀ) *
        (williamsonHamiltonianUnitary S ν hν hW : Matrix _ _ ℂ) = modeHamiltonian ν := by
  change (complexifyMatrix (relativeCongruenceOrthogonal S (modeDiagonal ν)))ᴴ * _ *
    complexifyMatrix (relativeCongruenceOrthogonal S (modeDiagonal ν)) = _
  rw [symplecticHamiltonian, Matrix.mul_smul, Matrix.smul_mul,
    ← complexifyMatrix_transpose, ← complexifyMatrix_mul, ← complexifyMatrix_mul,
    williamsonHamiltonian_real_normal_form S hS hν hW]
  rfl

theorem symplecticHamiltonian_eq_williamson_conjugate
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j)
    (hW : (S * modeDiagonal ν * Sᵀ).PosDef) :
    symplecticHamiltonian modeSymplecticForm (S * modeDiagonal ν * Sᵀ) =
      (williamsonHamiltonianUnitary S ν hν hW : Matrix _ _ ℂ) * modeHamiltonian ν *
        (williamsonHamiltonianUnitary S ν hν hW : Matrix _ _ ℂ)ᴴ := by
  let U := williamsonHamiltonianUnitary S ν hν hW
  let H := symplecticHamiltonian modeSymplecticForm (S * modeDiagonal ν * Sᵀ)
  have hn : (U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ)ᴴ * H * (U : Matrix (Fin m × Fin 2)
    (Fin m × Fin 2) ℂ) = modeHamiltonian ν :=
    williamsonHamiltonian_unitary_normal_form S hS hν hW
  have hUU : (U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) * (U : Matrix (Fin m × Fin 2)
    (Fin m × Fin 2) ℂ)ᴴ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self U
  calc
    H = ((U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) * (U : Matrix (Fin m × Fin 2)
      (Fin m × Fin 2) ℂ)ᴴ) * H *
        ((U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) * (U : Matrix (Fin m × Fin 2)
          (Fin m × Fin 2) ℂ)ᴴ) := by
      rw [hUU, Matrix.one_mul, Matrix.mul_one]
    _ = (U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ) * ((U : Matrix (Fin m × Fin 2)
      (Fin m × Fin 2) ℂ)ᴴ * H * (U : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℂ)) * (U : Matrix
        (Fin m × Fin 2) (Fin m × Fin 2) ℂ)ᴴ := by
      noncomm_ring
    _ = _ := by rw [hn]

theorem real_trace_even_symplecticHamiltonian_williamson
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j) (f : ℝ → ℝ) :
    (cfc (fun x : ℝ => f |x|)
      (symplecticHamiltonian modeSymplecticForm (S * modeDiagonal ν * Sᵀ))).trace.re =
        2 * ∑ j, f (ν j) := by
  rw [symplecticHamiltonian_eq_williamson_conjugate S hS hν
      (canonical_williamson_covariance_posDef S hS hν),
    real_trace_cfc_unitary_conjugate _ (modeHamiltonian_isHermitian (fun j => (hν j).le))]
  exact real_trace_even_modeHamiltonian (fun j => (hν j).le) f

/-- Covariance purity trace. -/
def covariancePurityTrace (r : ℝ)
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) : ℝ :=
  -(1 / 2) * (cfc (fun x : ℝ => logPurityFactor r |x|)
    (symplecticHamiltonian modeSymplecticForm V)).trace.re

theorem covariancePurityTrace_williamson
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 0 < ν j) (r : ℝ) :
    covariancePurityTrace r (S * modeDiagonal ν * Sᵀ) = -∑ j, logPurityFactor r (ν j) := by
  rw [covariancePurityTrace, real_trace_even_symplecticHamiltonian_williamson S hS hν]
  ring

/-- Identification with the logarithm of the actual infinite-dimensional
Gaussian density power trace, not a formal covariance partition value. -/
theorem log_positiveTrace_gaussianPhysical_rpow_eq_covariancePurityTrace
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j)
    (hG : HasGaussianPhysicalCharacteristic A (S * modeDiagonal ν * Sᵀ))
    {r : ℝ} (hr : 0 < r) :
    Real.log (positiveTrace (A ^ r)).toReal =
      covariancePurityTrace r (S * modeDiagonal ν * Sᵀ) := by
  rw [log_positiveTrace_gaussianPhysical_rpow hA S hS hν hG hr,
    covariancePurityTrace_williamson S hS (fun j => by linarith [hν j])]

end VacuumBellSeparation.Gaussian
