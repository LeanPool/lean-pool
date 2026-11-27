/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SymplecticPurityCongruence

/-!
# The actual Gaussian purity differential at a faithful covariance

Fixed symplectic congruence transports the proved derivative and the
actual relative matrix trace norm. The final estimate applies to every
symmetric perturbation at a covariance with genuine faithful Williamson
data, without differentiating any Williamson eigenvectors or eigenvalues.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix Filter
open scoped MatrixOrder Matrix.Norms.L2Operator Topology

variable {m : ℕ}

theorem symplecticHamiltonian_gap_congruence
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef)
    (hgap : ∀ x ∈ spectrum ℝ (symplecticHamiltonian modeSymplecticForm V), 1 / 2 < |x|) :
    ∀ x ∈ spectrum ℝ (symplecticHamiltonian modeSymplecticForm (S * V * Sᵀ)),
      1 / 2 < |x| := by
  rw [symplecticHamiltonian_congruence S hS hV, ← Matrix.star_eq_conjTranspose,
    Unitary.spectrum_star_right_conjugate]
  exact hgap

theorem covariancePurityDerivative_symplectic_congruence
    {r : ℝ} (hr : 0 < r)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    (V Δ : RealSymmetricMatrixSpace (Fin m × Fin 2))
    (hV : (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ).PosDef)
    (hgap : ∀ x ∈ spectrum ℝ (symplecticHamiltonian modeSymplecticForm
      (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)), 1 / 2 < |x|) :
    covariancePurityDerivative r (symmetricCongruenceCLM S V)
      (canonical_symplectic_congruence_posDef S hS hV) (symmetricCongruenceCLM S Δ) =
        covariancePurityDerivative r V hV Δ := by
  have hW := canonical_symplectic_congruence_posDef S hS hV
  have hw := hasFDerivAt_covariancePurityTrace_of_spectral_gap hr
    (symmetricCongruenceCLM S V) hW (symplecticHamiltonian_gap_congruence S hS hV hgap)
  have hc := hw.comp V (symmetricCongruenceCLM S).hasFDerivAt
  have he := covariancePurityTrace_symplectic_congruence_eventually r S hS V hV
  have he' :
      (fun X : RealSymmetricMatrixSpace (Fin m × Fin 2) =>
        covariancePurityTrace r (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)) =ᶠ[𝓝 V]
      ((fun X : RealSymmetricMatrixSpace (Fin m × Fin 2) =>
        covariancePurityTrace r (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)) ∘
        symmetricCongruenceCLM S) := by
    filter_upwards [he] with X hX
    exact hX.symm
  have hd := hc.congr_of_eventuallyEq he'
  have hv := hasFDerivAt_covariancePurityTrace_of_spectral_gap hr V hV hgap
  exact DFunLike.congr_fun (hd.unique hv) Δ

theorem symmetricCongruenceCLM_inverse_apply
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (hS : IsUnit S)
    (Δ : RealSymmetricMatrixSpace (Fin m × Fin 2)) :
    symmetricCongruenceCLM S (symmetricCongruenceCLM S⁻¹ Δ) = Δ := by
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hS
  have hSSi : S * S⁻¹ = 1 := S.mul_nonsing_inv hdet
  apply Subtype.ext
  change S * (S⁻¹ * (Δ : Matrix _ _ ℝ) * (S⁻¹)ᵀ) * Sᵀ =
    (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
  calc
    _ = (S * S⁻¹) * (Δ : Matrix _ _ ℝ) * (S * S⁻¹)ᵀ := by
      rw [Matrix.transpose_mul]
      noncomm_ring
    _ = _ := by rw [hSSi, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

/-- The source purity differential estimate for arbitrary symmetric
directions, at a faithful covariance in its actual Williamson form. -/
theorem abs_covariancePurityDerivative_williamson_le
    {r : ℝ} (hr : 1 < r)
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 < ν j)
    (Δ : RealSymmetricMatrixSpace (Fin m × Fin 2)) :
    |covariancePurityDerivative r
      (symmetricCongruenceCLM S (modeCovarianceSpace ν))
      (canonical_williamson_covariance_posDef S hS (fun j => by linarith [hν j])) Δ| ≤
        (r / 2) * matrixTraceNorm
          (relativeCovariancePerturbation (S * modeDiagonal ν * Sᵀ) Δ) := by
  have hν0 (j : Fin m) : 0 < ν j := by linarith [hν j]
  let D := modeCovarianceSpace ν
  let X := symmetricCongruenceCLM S⁻¹ Δ
  have hD : (D : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ).PosDef :=
    modeDiagonal_posDef hν0
  have hW := canonical_symplectic_congruence_posDef S hS hD
  have hundo : symmetricCongruenceCLM S X = Δ :=
    symmetricCongruenceCLM_inverse_apply S (canonical_symplectic_isUnit S hS) Δ
  have hgap : ∀ x ∈ spectrum ℝ (symplecticHamiltonian modeSymplecticForm
      (D : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)),
      1 / 2 < |x| := by
    change ∀ x ∈ spectrum ℝ (symplecticHamiltonian modeSymplecticForm (modeDiagonal ν)),
      1 / 2 < |x|
    simpa only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] using
      faithful_williamson_hamiltonian_gap
        (1 : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (by simp) hν
  have hd := covariancePurityDerivative_symplectic_congruence
    (by linarith : 0 < r) S hS D X hD hgap
  rw [hundo] at hd
  have hnorm := matrixTraceNorm_relativeCovariancePerturbation_congruence S hD hW
    (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
  have hundo' : S * (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) * Sᵀ =
      (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) :=
    congrArg Subtype.val hundo
  rw [hundo'] at hnorm
  change matrixTraceNorm (relativeCovariancePerturbation (S * modeDiagonal ν * Sᵀ)
      (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)) =
    matrixTraceNorm (relativeCovariancePerturbation (modeDiagonal ν)
      (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)) at hnorm
  rw [hd, hnorm]
  exact abs_covariancePurityDerivative_mode_le hr (fun j => (hν j).le) X

end VacuumBellSeparation.Gaussian
