/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.PauliLiftProjections
public import LeanPool.LiebThirring.Kinetic.PauliStateConditional

/-!
# The Pauli occupation bound

The double coordinate projection is unchanged by exchanging its input coordinates. This holds on
every state and for every one-particle vector.

Pauli occupation: the occupation of any spatial-and-spin one-particle vector is at most one in
an antisymmetric state, with the state norm kept explicit.
-/

public section

open MeasureTheory

namespace LiebThirring

/-- The double coordinate projection is unchanged by exchanging its input
coordinates. This holds on every state and for every one-particle vector. -/
theorem oneParticleProjection_double_exchange {N q : ℕ} (i j : Fin N)
    (hij : i ≠ j)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position))
    (φ : State N q) :
    oneParticleProjection i f (oneParticleProjection j f
        (simultaneousPermutation (Equiv.swap i j) φ)) =
      oneParticleProjection i f (oneParticleProjection j f φ) := by
  let D := doubleParticleInsertion i j hij f
  let U := statePermutationLinearIsometryEquiv (q := q) (Equiv.swap i j)
  have hU : U.toContinuousLinearEquiv.toContinuousLinearMap.comp D = D := by
    apply ContinuousLinearMap.ext
    intro v
    exact simultaneousPermutation_doubleParticleInsertion i j hij f v
  have h := operator_projection_comp_eq_of_comp_eq D U hU
  rw [← oneParticleProjection_comp_oneParticleProjection i j hij f] at h
  exact congrArg (fun T : State N q →L[ℂ] State N q => T φ) h

/-- Pauli occupation: the occupation of any spatial-and-spin one-particle vector is at most
one in an antisymmetric state, with the state norm kept explicit. -/
theorem oneParticleContraction_pauli {N q : ℕ} (i : Fin N)
    (ψ : State N q) (hψ : antisymmetric ψ)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    (N : ℝ) * ‖oneParticleContraction i f ψ‖ ^ 2 ≤ ‖f‖ ^ 2 * ‖ψ‖ ^ 2 := by
  exact oneParticleContraction_pauli_of_double_exchange i ψ hψ
    (fun g _ k l hkl φ => oneParticleProjection_double_exchange k l hkl g φ) f

/-- The normalized Pauli occupation estimate consumed by the low-momentum bound. -/
theorem oneParticleContraction_pauli_of_norm_eq_one {N q : ℕ} (i : Fin N)
    (ψ : State N q) (hψ : antisymmetric ψ) (hnorm : ‖ψ‖ = 1)
    (f : Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure Position)) :
    (N : ℝ) * ‖oneParticleContraction i f ψ‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  simpa only [hnorm, one_pow, mul_one] using oneParticleContraction_pauli i ψ hψ f

end LiebThirring

end
