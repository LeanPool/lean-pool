/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.FourierFactor
public import LeanPool.LiebThirring.Kinetic.CurryingDensity

/-!
# Fiber Fourier transform and weighted currying

Fourier transform on every remaining-spin Hilbert component.

The full Fourier particle integral equals the weighted norm of its curried full Fourier
transform, without any finite-energy assumption.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal FourierTransform

namespace LiebThirring

/-- Fourier transform on every remaining-spin Hilbert component. -/
@[expose] noncomputable def restFourierLinearIsometryEquiv {N q : ℕ} (i : Fin N) :
    OneParticleFiber i q ≃ₗᵢ[ℂ] OneParticleFiber i q :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin q =>
    Lp.fourierTransformₗᵢ (OtherConfiguration i) (EuclideanSpace ℂ (OtherSpinLabels i q)))

/-- The full Fourier particle integral equals the weighted norm of its curried
full Fourier transform, without any finite-energy assumption. -/
theorem particleFourierEnergy_eq_currying_fullFourier {N q : ℕ} (i : Fin N) (ψ : State N q) :
    particleFourierEnergy ψ i = ∫⁻ ξ : Position,
      ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
        (‖oneParticleCurrying i (𝓕 ψ) ξ‖₊ : ℝ≥0∞) ^ 2 := by
  let w : Position → ℝ≥0∞ := fun x =>
    ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖x‖₊ : ℝ≥0∞) ^ 2
  have hw : Measurable w :=
    measurable_const.mul (measurable_id.nnnorm.coe_nnreal_ennreal.pow_const 2)
  change (∫⁻ X : Configuration N, w (particlePosition X i) *
    (‖(Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) ψ) X‖₊ : ℝ≥0∞) ^ 2) = _
  calc
    _ = ∫⁻ ξ : Position, w ξ * ∫⁻ y : OtherConfiguration i,
        (‖(Lp.fourierTransformₗᵢ (Configuration N) (SpinAmplitudes N q) ψ)
          (insertParticle i ξ y)‖₊ : ℝ≥0∞) ^ 2 :=
      (particle_marginal_testing (Lp.fourierTransformₗᵢ _ _ ψ) i w hw).symm
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [particle_marginal_eq_currying_norm_sq_ae i (𝓕 ψ)] with ξ hξ
      exact congrArg (fun a : ℝ≥0∞ => w ξ * a) hξ

end LiebThirring
end
