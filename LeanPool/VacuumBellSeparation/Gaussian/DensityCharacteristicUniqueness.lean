/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.GaussianBargmannKernel

/-!
# Actual density operators are determined by their Weyl characteristic

The proved integrable Bargmann inversion and the dense span of the actual
exponential vectors separate bounded positive trace-class operators.
Consequently the physical Gaussian characteristic determines at most one
density in this fixed oscillator representation. No equivalence between
different CCR representations or symplectic implementer is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Matrix
open scoped ComplexConjugate

theorem continuousLinearMap_eq_of_multiBargmannKernel {m : ℕ}
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (h : ∀ z w : Fin m → ℂ, multiBargmannKernel A z w = multiBargmannKernel B z w) :
    A = B := by
  apply continuousLinearMap_eq_of_dense_span (multiExponentialVector (m := m))
    (multiExponentialVector_dense_span m)
  intro w
  apply (innerSL_inj (𝕜 := ℂ)).mp
  apply continuousLinearMap_eq_of_dense_span (multiExponentialVector (m := m))
    (multiExponentialVector_dense_span m)
  intro z
  simpa only [multiBargmannKernel, innerSL_apply_apply, inner_conj_symm] using
    congrArg conj (h z w)

/-- Weyl characteristic uniqueness for actual positive trace-class
operators in the fixed full multi-mode oscillator space. -/
theorem positiveTraceClass_eq_of_weyl_characteristic {m : ℕ}
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (hB : IsPositiveTraceClass B)
    (h : ∀ z : Fin m → ℂ,
      densityExpectation (multiModeNumberBasis m) A (multiOscillatorWeyl (WithLp.toLp 2 z)) =
        densityExpectation (multiModeNumberBasis m) B (multiOscillatorWeyl (WithLp.toLp 2 z))) :
    A = B := by
  apply continuousLinearMap_eq_of_multiBargmannKernel
  intro z w
  have hAi := integral_densityBargmannInversion hA (WithLp.toLp 2 z) (WithLp.toLp 2 w)
  have hBi := integral_densityBargmannInversion hB (WithLp.toLp 2 z) (WithLp.toLp 2 w)
  simp_rw [h] at hAi
  have hp : (Real.pi : ℂ) ^ m ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  exact mul_left_cancel₀ hp (hAi.symm.trans hBi)

theorem gaussianDisplacement_density_unique {m : ℕ}
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (hB : IsPositiveTraceClass B)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hGA : HasGaussianDisplacementCharacteristic A V)
    (hGB : HasGaussianDisplacementCharacteristic B V) : A = B := by
  apply positiveTraceClass_eq_of_weyl_characteristic hA hB
  intro z
  exact (hGA z).trans (hGB z).symm

theorem gaussianPhysical_density_unique {m : ℕ}
    {A B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A) (hB : IsPositiveTraceClass B)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hGA : HasGaussianPhysicalCharacteristic A V)
    (hGB : HasGaussianPhysicalCharacteristic B V) : A = B :=
  gaussianDisplacement_density_unique hA hB hGA hGB

theorem gaussianDisplacement_positiveTrace_eq_one {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianDisplacementCharacteristic A V) : positiveTrace A = 1 := by
  have hz : complexRealCoordinates m (0 : Fin m → ℂ) = 0 := by
    ext ⟨j, k⟩
    fin_cases k <;> simp
  have h := hG 0
  rw [hz, Matrix.mulVec_zero, dotProduct_zero, neg_zero, Complex.ofReal_zero,
    Complex.exp_zero, WithLp.toLp_zero, multiOscillatorWeyl_zero,
    densityExpectation_one (multiModeNumberBasis m) hA] at h
  exact (ENNReal.toReal_eq_one_iff _).mp (Complex.ofReal_injective (by simpa using h))

theorem gaussianPhysical_positiveTrace_eq_one {m : ℕ}
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m}
    (hA : IsPositiveTraceClass A)
    {V : Matrix (Fin m × Fin 2) (Fin m × Fin 2) ℝ}
    (hG : HasGaussianPhysicalCharacteristic A V) : positiveTrace A = 1 :=
  gaussianDisplacement_positiveTrace_eq_one hA hG

end VacuumBellSeparation.Gaussian
