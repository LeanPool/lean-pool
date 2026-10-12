/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.FourierFactor

/-!
# Exchange of full Fourier energies

Fourier covariance gives equality of exchanged particle energies and the exchange-odd L²
identity.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- All full-space particle Fourier energies of an antisymmetric state agree. -/
theorem particleFourierEnergy_eq {N q : ℕ} (ψ : State N q) (hψ : antisymmetric ψ)
    (i j : Fin N) : particleFourierEnergy ψ i = particleFourierEnergy ψ j := by
  exact particle_marginals_eq (Lp.fourierTransformₗᵢ _ _ ψ)
    (antisymmetric_fourier ψ hψ) i j
    (fun x : Position => ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖x‖₊ : ℝ≥0∞) ^ 2)

/-- The extended kinetic energy is the particle count times any selected
full Fourier energy, including infinite energy. -/
theorem kineticEnergy_eq_mul_particleFourierEnergy {N q : ℕ} (ψ : State N q)
    (hψ : antisymmetric ψ) (i : Fin N) :
    kineticEnergy ψ = (N : ℝ≥0∞) * particleFourierEnergy ψ i := by
  rw [kineticEnergy_eq_sum_particleFourierEnergy]
  simp only [particleFourierEnergy_eq ψ hψ _ i, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A transposition of distinct particles acts by negation on an antisymmetric
L² state. This is an equality of classes, not only of representative values. -/
theorem simultaneousPermutation_swap_eq_neg {N q : ℕ} (ψ : State N q)
    (hψ : antisymmetric ψ) (i j : Fin N) (hij : i ≠ j) :
    simultaneousPermutation (Equiv.swap i j) ψ = -ψ := by
  rw [simultaneousPermutation_eq_sign_smul _ ψ hψ]
  simp [Equiv.Perm.sign_swap hij]

end LiebThirring

end
