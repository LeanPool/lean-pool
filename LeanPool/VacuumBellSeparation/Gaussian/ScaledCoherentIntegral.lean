/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.CoherentRotationAveraging
public import LeanPool.VacuumBellSeparation.Gaussian.TorusPositiveDiagonal

/-!
# Full pre-extension coherent integral and weighted positive diagonal

Probability rotation averaging and actual angular Parseval give the
weighted number-state diagonal. The scalar integrals of the proved
Bargmann monomials supply the exact normalization, without polar
coordinates. The resulting extended integral identity allows infinity
and assumes only an actual bounded positive A, not a bounded extension
of its inverse sandwich or trace class of that extension.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate ENNReal

/-- Measure-space instance for `UnitAddCircle`. -/
local instance scaledCoherentIntegralMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance scaledCoherentIntegralProbabilityMeasure : IsProbabilityMeasure
  (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Occupation scale given by `∏ j, ‖t j‖ ^ (2 * k j)`. -/
def occupationScale {m : ℕ} (t : Fin m → ℂ) (k : Fin m → ℕ) : ℝ :=
  ∏ j, ‖t j‖ ^ (2 * k j)

theorem occupationScale_nonneg {m : ℕ} (t : Fin m → ℂ) (k : Fin m → ℕ) :
    0 ≤ occupationScale t k := Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _

theorem multiCoherentCoefficient_mul_norm_sq {m : ℕ}
    (t z : Fin m → ℂ) (k : Fin m → ℕ) :
    ‖multiCoherentCoefficient (fun j => t j * z j) k‖ ^ 2 =
      occupationScale t k * ‖multiCoherentCoefficient z k‖ ^ 2 := by
  simp only [multiCoherentCoefficient, norm_prod, ← Finset.prod_pow,
    occupationScale, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [coherentCoefficient_norm_sq, coherentCoefficient_norm_sq, norm_mul, mul_pow,
    mul_pow, ← pow_mul]
  ring

/-- Scaled coherent Gaussian diagonal. -/
def scaledCoherentGaussianDiagonal {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (t z : Fin m → ℂ) : ℝ :=
  ‖multiBargmannPrefactor z‖ ^ 2 *
    (inner ℂ (multiExponentialVector (fun j => conj (t j * z j)))
      (A (multiExponentialVector (fun j => conj (t j * z j))))).re

theorem continuous_scaledCoherentGaussianDiagonal {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) (t : Fin m → ℂ) :
    Continuous (scaledCoherentGaussianDiagonal A t) := by
  have hv : Continuous (fun z : Fin m → ℂ =>
      multiExponentialVector (fun j => conj (t j * z j))) :=
    (continuous_multiExponentialVector m).comp (by fun_prop)
  have hp : Continuous (multiBargmannPrefactor (m := m)) := by
    unfold multiBargmannPrefactor
    fun_prop
  unfold scaledCoherentGaussianDiagonal
  fun_prop

theorem scaledCoherentGaussianDiagonal_nonneg {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (t z : Fin m → ℂ) : 0 ≤ scaledCoherentGaussianDiagonal A t z :=
  mul_nonneg (sq_nonneg _)
    ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).re_inner_nonneg_right _)

theorem multiBargmannPrefactor_torusLabel {m : ℕ} (z : Fin m → ℂ)
    (θ : UnitAddTorus (Fin m)) :
    multiBargmannPrefactor (torusCoherentLabel z θ) = multiBargmannPrefactor z := by
  have hnorm (j : Fin m) : ‖fourier 1 (θ j)‖ = 1 := by
    rw [fourier_one]
    exact Circle.norm_coe _
  simp only [multiBargmannPrefactor, torusCoherentLabel, norm_mul, hnorm, mul_one]

theorem scaledCoherentGaussianDiagonal_rotation {m : ℕ}
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (t z : Fin m → ℂ) (θ : UnitAddTorus (Fin m)) :
    scaledCoherentGaussianDiagonal A t (torusCoherentLabel z θ) =
      ‖multiBargmannPrefactor z‖ ^ 2 *
        positiveTorusCoherentDiagonal A (fun j => t j * z j) θ := by
  rw [scaledCoherentGaussianDiagonal, multiBargmannPrefactor_torusLabel]
  have heq : (fun j => conj (t j * torusCoherentLabel z θ j)) =
      fun j => conj (torusCoherentLabel (fun j => t j * z j) θ j) := by
    funext j
    simp only [torusCoherentLabel, mul_assoc]
  rw [heq]
  rfl

theorem lintegral_multiBargmannMonomial_norm_sq {m : ℕ} (k : Fin m → ℕ) :
    (∫⁻ z : Fin m → ℂ, ENNReal.ofReal (‖multiBargmannMonomial k z‖ ^ 2)) = 1 := by
  have hint := (memLp_two_iff_integrable_sq_norm
    (memLp_multiBargmannMonomial k).aestronglyMeasurable).mp (memLp_multiBargmannMonomial k)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]
  have hc := integral_inner_multiBargmannMonomial k k
  have hi : Integrable (fun z : Fin m → ℂ =>
      inner ℂ (multiBargmannMonomial k z) (multiBargmannMonomial k z)) := by
    simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] using
      (hint.ofReal (𝕜 := ℂ))
  have hr := congrArg (RCLike.re : ℂ → ℝ) hc
  rw [← integral_re hi] at hr
  simp only [inner_self_eq_norm_sq] at hr
  rw [hr]
  simp only [ite_true, RCLike.one_re, ENNReal.ofReal_one]

theorem lintegral_scaledCoherentGaussianDiagonal_rotation {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (t z : Fin m → ℂ) :
    (∫⁻ θ : UnitAddTorus (Fin m),
      ENNReal.ofReal (scaledCoherentGaussianDiagonal A t (torusCoherentLabel z θ))) =
        ∑' k, ENNReal.ofReal (‖multiBargmannMonomial k z‖ ^ 2 * occupationScale t k *
          (inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k))).re) := by
  simp_rw [scaledCoherentGaussianDiagonal_rotation,
    ENNReal.ofReal_mul (sq_nonneg _)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_positiveTorusCoherentDiagonal hA, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [← ENNReal.ofReal_mul (sq_nonneg _), multiCoherentCoefficient_mul_norm_sq,
    multiBargmannMonomial_eq_coherentCoefficient, norm_mul, mul_pow]
  congr 1
  ring

/-- The pre-extension weighted trace identity. It is valid with infinite
values and uses no summability or bounded-sandwich hypothesis. -/
theorem lintegral_scaledCoherentGaussianDiagonal {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (t : Fin m → ℂ) :
    (∫⁻ z : Fin m → ℂ, ENNReal.ofReal (scaledCoherentGaussianDiagonal A t z)) =
      ∑' k, ENNReal.ofReal (occupationScale t k *
        (inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k))).re) := by
  rw [lintegral_eq_rotation_average _
    (continuous_scaledCoherentGaussianDiagonal A t).measurable.ennreal_ofReal]
  simp_rw [lintegral_scaledCoherentGaussianDiagonal_rotation hA t]
  have hmeas (k : Fin m → ℕ) : Measurable (fun z : Fin m → ℂ =>
      ENNReal.ofReal (‖multiBargmannMonomial k z‖ ^ 2 * occupationScale t k *
        (inner ℂ (multiModeNumberBasis m k) (A (multiModeNumberBasis m k))).re)) := by
    unfold multiBargmannMonomial bargmannMonomial
    fun_prop
  rw [lintegral_tsum (fun k => (hmeas k).aemeasurable)]
  apply tsum_congr
  intro k
  simp_rw [mul_assoc, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
    lintegral_multiBargmannMonomial_norm_sq, one_mul]

end VacuumBellSeparation.Gaussian
