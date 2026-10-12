/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.FourierFactorIdentity

/-!
# Exact density-field Fourier energy

Extended multiplier in the same factorization as the energy.

Fourier of the scaled density field has exactly N times the squared norm.
-/

public section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace LiebThirring

/-- Extended multiplier in the same factorization as the energy. -/
theorem ofReal_fourierKineticMultiplier (ξ : Position) :
    ENNReal.ofReal ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) =
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * ‖ξ‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Fourier of the scaled density field has exactly N times the squared norm. -/
theorem densityField_fourier_enorm_sq_ae {N q : ℕ} (i : Fin N) (ψ : State N q) :
    ∀ᵐ ξ : Position,
      ‖(Lp.fourierTransformₗᵢ Position (OneParticleFiber i q) (densityField i ψ)) ξ‖ₑ ^ 2 =
        (N : ℝ≥0∞) *
          ‖(Lp.fourierTransformₗᵢ Position (OneParticleFiber i q) (oneParticleCurrying i ψ)) ξ‖ₑ ^
            2 := by
  have hft : Lp.fourierTransformₗᵢ Position (OneParticleFiber i q) (densityField i ψ) =
      (Real.sqrt N : ℂ) • Lp.fourierTransformₗᵢ Position (OneParticleFiber i q)
        (oneParticleCurrying i ψ) :=
    map_smul _ _ _
  have hc : ‖(Real.sqrt N : ℂ)‖ₑ ^ 2 = (N : ℝ≥0∞) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg N),
      ENNReal.ofReal_natCast]
  rw [hft]
  filter_upwards [Lp.coeFn_smul (Real.sqrt N : ℂ)
    (Lp.fourierTransformₗᵢ Position (OneParticleFiber i q) (oneParticleCurrying i ψ))] with ξ hξ
  rw [hξ, Pi.smul_apply, enorm_smul, mul_pow, hc]

/-- The literal density-field Fourier energy is the full kinetic energy. -/
theorem kineticEnergy_eq_densityField_fourier {N q : ℕ} (i : Fin N)
    (ψ : State N q) (hψ : antisymmetric ψ) :
    kineticEnergy ψ = ∫⁻ ξ : Position,
      ENNReal.ofReal ((2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) *
        ‖(Lp.fourierTransformₗᵢ Position (OneParticleFiber i q) (densityField i ψ)) ξ‖ₑ ^ 2 := by
  rw [kineticEnergy_eq_mul_particleFourierEnergy ψ hψ i,
    particleFourierEnergy_eq_partialFourier]
  rw [← lintegral_const_mul' _ _ (by simp)]
  apply lintegral_congr_ae
  filter_upwards [densityField_fourier_enorm_sq_ae i ψ] with ξ hξ
  rw [hξ, ofReal_fourierKineticMultiplier]
  change (N : ℝ≥0∞) * (ENNReal.ofReal ((2 * Real.pi) ^ 2) * ‖ξ‖ₑ ^ 2 *
    ‖(Lp.fourierTransformₗᵢ Position (OneParticleFiber i q) (oneParticleCurrying i ψ)) ξ‖ₑ ^ 2) = _
  ring

end LiebThirring
end
