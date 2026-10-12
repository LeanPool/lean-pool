/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.KineticEnergy
public import LeanPool.LiebThirring.Kinetic.DensityBasic
public import LeanPool.LiebThirring.Fourier.Covariance
public import LeanPool.LiebThirring.Kinetic.Permutation
public import LeanPool.LiebThirring.Kinetic.CurryingTransport

/-!
# Particle Fourier energies

The Fourier kinetic energy associated with particle `i` (Fourier factorization).

Full kinetic energy is the sum of the particle energies, including at infinity.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring

/-- The Fourier kinetic energy associated with particle `i` (Fourier factorization). -/
@[expose] noncomputable def particleFourierEnergy {N q : ℕ} (ψ : State N q)
    (i : Fin N) : ℝ≥0∞ :=
  ∫⁻ ξ : Configuration N,
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖particlePosition ξ i‖₊ : ℝ≥0∞) ^ 2 *
      (‖(Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) ψ) ξ‖₊ : ℝ≥0∞) ^ 2

/-- Full kinetic energy is the sum of the particle energies, including at infinity. -/
theorem kineticEnergy_eq_sum_particleFourierEnergy {N q : ℕ} (ψ : State N q) :
    kineticEnergy ψ = ∑ i : Fin N, particleFourierEnergy ψ i := by
  have hnorm (ξ : Configuration N) :
      (‖ξ‖₊ : ℝ≥0∞) ^ 2 = ∑ i : Fin N, (‖particlePosition ξ i‖₊ : ℝ≥0∞) ^ 2 := by
    have hp (i : Fin N) : (‖particlePosition ξ i‖₊ : ℝ≥0∞) ^ 2 =
        ∑ a : Fin 3, ENNReal.ofReal (ξ (i, a) ^ 2) := by
      change ‖particlePosition ξ i‖ₑ ^ 2 = _
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        EuclideanSpace.real_norm_sq_eq,
        ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      rfl
    change ‖ξ‖ₑ ^ 2 = _
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
      EuclideanSpace.real_norm_sq_eq,
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _), Fintype.sum_prod_type]
    exact Finset.sum_congr rfl (fun i _ => (hp i).symm)
  unfold kineticEnergy particleFourierEnergy
  simp_rw [hnorm, Finset.mul_sum, Finset.sum_mul]
  rw [lintegral_finsetSum]
  intro i _
  exact ((measurable_const.mul
    ((measurable_particlePosition i).nnnorm.coe_nnreal_ennreal.pow_const 2)).mul
    (measurable_state_norm_sq (Lp.fourierTransformₗᵢ _ _ ψ)))

/-- Simultaneous particle permutation packaged as a unitary on `State`. -/
@[expose] noncomputable def statePermutationLinearIsometryEquiv {N q : ℕ}
    (σ : Equiv.Perm (Fin N)) : State N q ≃ₗᵢ[ℂ] State N q :=
  (l2PullbackEquiv (permutationLinearIsometryEquiv σ).toHomeomorph.toMeasurableEquiv
    (permutationLinearIsometryEquiv σ).measurePreserving).trans
      (l2TargetEquiv (volume : Measure (Configuration N)) (spinPermutationLinearIsometryEquiv σ))

/-- The L² simultaneous spatial and spin permutation from the formulas. -/
@[expose] noncomputable def simultaneousPermutation {N q : ℕ}
    (σ : Equiv.Perm (Fin N)) (ψ : State N q) : State N q :=
  statePermutationLinearIsometryEquiv σ ψ

@[simp] theorem statePermutationLinearIsometryEquiv_apply {N q : ℕ}
    (σ : Equiv.Perm (Fin N)) (ψ : State N q) :
    statePermutationLinearIsometryEquiv σ ψ = simultaneousPermutation σ ψ := rfl

/-- The permutation operator has exactly the simultaneous representative. -/
theorem simultaneousPermutation_apply_ae {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (ψ : State N q) :
    ∀ᵐ x ∂(volume : Measure (Configuration N)),
      ∀ s : SpinLabels N q, simultaneousPermutation σ ψ x s =
        ψ (permutePositions σ x) (permuteSpins σ s) := by
  filter_upwards [
    (spinPermutationLinearIsometryEquiv (q := q)
      σ).toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp
      (Lp.compMeasurePreserving (permutationLinearIsometryEquiv σ)
        (permutationLinearIsometryEquiv σ).measurePreserving ψ),
    Lp.coeFn_compMeasurePreserving ψ (permutationLinearIsometryEquiv σ).measurePreserving]
    with x hx hy
  intro s
  change simultaneousPermutation σ ψ x =
    spinPermutationLinearIsometryEquiv σ
      (Lp.compMeasurePreserving (permutationLinearIsometryEquiv σ)
        (permutationLinearIsometryEquiv σ).measurePreserving ψ x) at hx
  rw [hx, hy]
  rfl

/-- The full L² Fourier transform intertwines every simultaneous particle permutation. -/
theorem fourier_simultaneousPermutation {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (ψ : State N q) :
    𝓕 (simultaneousPermutation σ ψ) = simultaneousPermutation σ (𝓕 ψ) := by
  unfold simultaneousPermutation statePermutationLinearIsometryEquiv
  change 𝓕
    ((spinPermutationLinearIsometryEquiv σ).toContinuousLinearEquiv.toContinuousLinearMap.compLp
      (Lp.compMeasurePreserving (permutationLinearIsometryEquiv σ)
        (permutationLinearIsometryEquiv σ).measurePreserving ψ)) = _
  rw [Fourier.fourier_compLp, Fourier.fourier_compMeasurePreserving]
  rfl

/-- An antisymmetric state is an eigenvector of each simultaneous permutation. -/
theorem simultaneousPermutation_eq_sign_smul {N q : ℕ} (σ : Equiv.Perm (Fin N))
    (ψ : State N q) (hψ : antisymmetric ψ) :
    simultaneousPermutation σ ψ = ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) • ψ := by
  apply Lp.ext
  filter_upwards [simultaneousPermutation_apply_ae σ ψ, hψ σ,
    Lp.coeFn_smul ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) ψ] with x hx ha hs
  rw [hs]
  ext s
  exact (hx s).trans (ha s)

/-- Full Fourier transformation preserves the antisymmetry condition. -/
theorem antisymmetric_fourier {N q : ℕ} (ψ : State N q) (hψ : antisymmetric ψ) :
    antisymmetric (𝓕 ψ) := by
  intro σ
  have heq : simultaneousPermutation σ (𝓕 ψ) =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) • 𝓕 ψ := by
    rw [← fourier_simultaneousPermutation, simultaneousPermutation_eq_sign_smul σ ψ hψ,
      FourierTransform.fourier_smul]
  filter_upwards [simultaneousPermutation_apply_ae σ (𝓕 ψ),
    Lp.coeFn_smul ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)) (𝓕 ψ)] with x hx hs
  intro s
  rw [← hx s, heq, hs]
  rfl

end LiebThirring
end
