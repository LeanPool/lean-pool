/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.QuantumNondegenerateCovariance
public import LeanPool.VacuumBellSeparation.Gaussian.GaussianCoordinateTransport
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeFaithfulness

/-!
# Actual Gaussian faithfulness removes the pure uncertainty boundary

A semidefinite physical covariance has genuine Williamson coordinates and
an actual product thermal density model. A variance equal to 1/2 produces
an explicit kernel vector in that density. Actual injectivity therefore
forces all mode variances strictly above 1/2, and hence strict positivity
of the literal quantum matrix. No bounded density inverse is asserted.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexOrder

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem isFaithfulDensity_conjStarAlgEquiv_iff (e : E ≃ₗᵢ[ℂ] F) {A : E →L[ℂ] E} :
    IsFaithfulDensity (e.conjStarAlgEquiv A) ↔ IsFaithfulDensity A := by
  constructor
  · intro h
    have hi := h.conjStarAlgEquiv e.symm
    simpa only [← LinearIsometryEquiv.symm_conjStarAlgEquiv,
      StarAlgEquiv.symm_apply_apply] using hi
  · exact fun h => h.conjStarAlgEquiv e

variable {m : ℕ}

theorem physicalWilliamsonDensity_isFaithfulDensity_iff
    (S : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ)
    (hS : S * modeSymplecticForm * Sᵀ = modeSymplecticForm)
    {ν : Fin m → ℝ} (hν : ∀ j, 1 / 2 ≤ ν j) :
    IsFaithfulDensity (physicalWilliamsonDensity S hS ν) ↔ ∀ j, 1 / 2 < ν j := by
  rw [← physicalDensityPullback_covarianceProductDensity S hS hν]
  change IsFaithfulDensity
    ((physicalCongruenceUnitary S hS).symm.conjStarAlgEquiv (covarianceProductDensity ν)) ↔ _
  rw [isFaithfulDensity_conjStarAlgEquiv_iff, covarianceProductDensity_isFaithfulDensity_iff hν]

theorem faithful_gaussian_quantum_posDef
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsFaithfulDensity A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V)
    (hQ : (quantumCovariance V modeSymplecticForm).PosSemidef) :
    (quantumCovariance V modeSymplecticForm).PosDef := by
  have hV := real_posDef_of_quantum_posSemidef hQ (modeSymplecticForm_isUnit m)
  obtain ⟨n, ν, S, T, hcard, hν, hST, hTS, hS, hcov⟩ :=
    exists_quantum_williamson_factorization V modeSymplecticForm hV
      transpose_modeSymplecticForm (modeSymplecticForm_isUnit m) hQ
  have hnm : n = m := by
    simp only [Fintype.card_prod, Fintype.card_fin] at hcard
    omega
  subst n
  have hG' : HasGaussianPhysicalCharacteristic A (S * modeDiagonal ν * Sᵀ) := hcov.symm ▸ hG
  have he := gaussianPhysical_eq_physicalWilliamsonDensity hA.isPositiveTraceClass S hS hν hG'
  have hfaith : IsFaithfulDensity (physicalWilliamsonDensity S hS ν) := he ▸ hA
  have hν' := (physicalWilliamsonDensity_isFaithfulDensity_iff S hS hν).mp hfaith
  rw [← hcov]
  exact quantumCovariance_symplectic_congruence_posDef S hS (quantum_mode_posDef hν')

end VacuumBellSeparation.Gaussian
