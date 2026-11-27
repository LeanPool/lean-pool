/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianPurityDifferential
public import LeanPool.VacuumBellSeparation.Gaussian.CovarianceSegmentBounds

/-!
# Purity calculus from literal strict quantum uncertainty

The actual finite Williamson theorem turns positivity of V+iΩ/2 into
strict mode variances. This yields the genuine purity derivative and its
relative trace-norm bound without taking Williamson data as input.
Strict quantum uncertainty is also proved along actual affine segments.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator Topology ComplexOrder

variable {m : ℕ}

theorem exists_faithful_canonical_williamson
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef) :
    ∃ (ν : Fin m → ℝ) (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ),
      (∀ j, 1 / 2 < ν j) ∧ S * modeSymplecticForm * Sᵀ = modeSymplecticForm ∧
        S * modeDiagonal ν * Sᵀ = V := by
  obtain ⟨n, ν, S, T, hcard, _, hST, hTS, hsymp, hcov⟩ :=
    exists_quantum_williamson_factorization V modeSymplecticForm hV
      transpose_modeSymplecticForm (modeSymplecticForm_isUnit m) hQ.posSemidef
  have hν := strict_quantum_williamson_variances V modeSymplecticForm ν S T hTS hsymp hcov hQ
  have hnm : n = m := by
    simp only [Fintype.card_prod, Fintype.card_fin] at hcard
    omega
  subst n
  exact ⟨ν, S, hν, hsymp, hcov⟩

theorem strict_quantum_hamiltonian_gap
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef) :
    ∀ x ∈ spectrum ℝ (symplecticHamiltonian modeSymplecticForm V), 1 / 2 < |x| := by
  obtain ⟨ν, S, hν, hS, hcov⟩ := exists_faithful_canonical_williamson V hV hQ
  rw [← hcov]
  exact faithful_williamson_hamiltonian_gap S hS hν

theorem hasFDerivAt_covariancePurityTrace_of_strict_quantum
    {r : ℝ} (hr : 0 < r)
    (V : RealSymmetricMatrixSpace (Fin m × Fin 2))
    (hV : (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ).PosDef)
    (hQ : (quantumCovariance (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
      modeSymplecticForm).PosDef) :
    HasFDerivAt (fun X : RealSymmetricMatrixSpace (Fin m × Fin 2) =>
      covariancePurityTrace r (X : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ))
        (covariancePurityDerivative r V hV) V :=
  hasFDerivAt_covariancePurityTrace_of_spectral_gap hr V hV
    (strict_quantum_hamiltonian_gap
      (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) hV hQ)

theorem abs_covariancePurityDerivative_le_of_strict_quantum
    {r : ℝ} (hr : 1 < r)
    (V Δ : RealSymmetricMatrixSpace (Fin m × Fin 2))
    (hV : (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ).PosDef)
    (hQ : (quantumCovariance (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
      modeSymplecticForm).PosDef) :
    |covariancePurityDerivative r V hV Δ| ≤
      (r / 2) * matrixTraceNorm (relativeCovariancePerturbation
        (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
        (Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)) := by
  obtain ⟨ν, S, hν, hS, hcov⟩ := exists_faithful_canonical_williamson
    (V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) hV hQ
  have he : symmetricCongruenceCLM S (modeCovarianceSpace ν) = V := by
    apply Subtype.ext
    exact hcov
  have h := abs_covariancePurityDerivative_williamson_le hr S hS hν Δ
  simpa only [he, hcov] using h

theorem quantumCovariance_segment
    (V Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ) (t : ℝ) :
    quantumCovariance (covarianceSegment V Δ t) modeSymplecticForm =
      (1 - t) • quantumCovariance V modeSymplecticForm +
        t • quantumCovariance (V + Δ) modeSymplecticForm := by
  have hs : complexifyMatrix (t • Δ) = t • complexifyMatrix Δ :=
    (complexifyMatrixCLM (ι := Fin m × Fin 2)).map_smul t Δ
  rw [quantumCovariance, covarianceSegment, complexifyMatrix_add, hs]
  simp only [quantumCovariance, complexifyMatrix_add]
  module

/-- Strict uncertainty is preserved throughout the full closed segment.
The endpoints are retained explicitly; no mere covariance positivity is
mistaken for the quantum condition. -/
theorem quantumCovariance_segment_posDef
    {V Δ : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hQ₀ : (quantumCovariance V modeSymplecticForm).PosDef)
    (hQ₁ : (quantumCovariance (V + Δ) modeSymplecticForm).PosDef)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) :
    (quantumCovariance (covarianceSegment V Δ t) modeSymplecticForm).PosDef := by
  rw [quantumCovariance_segment]
  by_cases ht : t = 1
  · simpa only [ht, sub_self, zero_smul, one_smul, zero_add] using hQ₁
  · have htlt : t < 1 := by
      rcases lt_or_eq_of_le ht₁ with h | h
      · exact h
      · exact (ht h).elim
    exact (hQ₀.smul (sub_pos.mpr htlt)).add_posSemidef (hQ₁.posSemidef.smul ht₀)

theorem log_positiveTrace_gaussianPhysical_rpow_eq_purity
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ} (hV : V.PosDef)
    (hQ : (quantumCovariance V modeSymplecticForm).PosDef)
    (hG : HasGaussianPhysicalCharacteristic A V) {r : ℝ} (hr : 0 < r) :
    Real.log (positiveTrace (A ^ r)).toReal = covariancePurityTrace r V := by
  obtain ⟨ν, S, hν, hS, hcov⟩ := exists_faithful_canonical_williamson V hV hQ
  rw [← hcov] at hG ⊢
  exact log_positiveTrace_gaussianPhysical_rpow_eq_covariancePurityTrace hA S hS
    (fun j => (hν j).le) hG hr

end VacuumBellSeparation.Gaussian
