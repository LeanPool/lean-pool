/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ScaledCoherentIntegral
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeInverseBargmann
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeSandwichCriterion
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeCoherentResolution

/-!
# Actual inverse thermal form: coherent integral and extension criterion

The form is evaluated on normalized coherent vectors in the actual range
domain of the thermal half power. Rotation averaging identifies its
extended integral with the weighted diagonal before any bounded extension
is assumed. Finiteness is exactly the existence criterion for a positive
trace-class extension, including noncommuting positive inputs.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory
open scoped ComplexConjugate ENNReal

theorem multiBargmannPrefactor_norm_sq {m : ℕ} (z : Fin m → ℂ) :
    ‖multiBargmannPrefactor z‖ ^ 2 =
      (Real.pi ^ m)⁻¹ * Real.exp (-(∑ j, ‖z j‖ ^ 2)) := by
  rw [multiBargmannPrefactor_eq, norm_div, Complex.norm_exp_ofReal, norm_pow,
    Complex.norm_of_nonneg (Real.sqrt_nonneg _), div_pow,
    ← pow_mul, Nat.mul_comm m 2, pow_mul, Real.sq_sqrt Real.pi_pos.le,
    pow_two, ← Real.exp_add]
  have he : -(∑ j, ‖z j‖ ^ 2) / 2 + -(∑ j, ‖z j‖ ^ 2) / 2 =
      -(∑ j, ‖z j‖ ^ 2) := by ring
  rw [he]
  ring

theorem thermal_occupationScale {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (τ : ℝ) (k : Fin m → ℕ) :
    (∏ j, (1 - q j)) ^ (-τ) *
      occupationScale (fun j => ((q j ^ (-(τ / 2)) : ℝ) : ℂ)) k =
        multiModeThermalWeight q k ^ (-τ) := by
  rw [← Real.finsetProd_rpow Finset.univ (fun j => 1 - q j)
    (fun j _ => sub_nonneg.mpr (hq₁ j).le), occupationScale,
    multiModeThermalWeight_rpow (fun j => (hq₀ j).le) hq₁,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [Complex.norm_of_nonneg (Real.rpow_nonneg (hq₀ j).le _),
    thermalWeight_rpow (hq₀ j).le (hq₁ j)]
  congr 1
  rw [pow_mul, pow_two, ← Real.rpow_add (hq₀ j)]
  congr 2
  ring

/-- Multi thermal sandwich coherent diagonal. -/
def multiThermalSandwichCoherentDiagonal {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (z : Fin m → ℂ) : ℝ :=
  (Real.pi ^ m)⁻¹ *
    (multiThermalSandwichForm hq₀ hq₁ hτ A
      (multiDomainCoherentVector hq₀ hq₁ (half_pos hτ) (WithLp.toLp 2 z))
      (multiDomainCoherentVector hq₀ hq₁ (half_pos hτ) (WithLp.toLp 2 z))).re

theorem multiThermalSandwichCoherentDiagonal_conj {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m)
    (z : Fin m → ℂ) :
    multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A (multiConjugation m z) =
      (∏ j, (1 - q j)) ^ (-τ) * scaledCoherentGaussianDiagonal A
        (fun j => ((q j ^ (-(τ / 2)) : ℝ) : ℂ)) z := by
  have hl : multiModeInversePowerLabel q (τ / 2)
      (fun j => (WithLp.toLp 2 (multiConjugation m z) : MultiModePhaseSpace m) j) =
        fun j => conj (((q j ^ (-(τ / 2)) : ℝ) : ℂ) * z j) := by
    funext j
    simp only [multiModeInversePowerLabel, multiConjugation_apply,
      map_mul, Complex.conj_ofReal]
  have hn : ‖(WithLp.toLp 2 (multiConjugation m z) : MultiModePhaseSpace m)‖ ^ 2 =
      ∑ j, ‖z j‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, multiConjugation_apply,
      Complex.norm_conj]
  rw [multiThermalSandwichCoherentDiagonal,
    multiThermalSandwichForm_coherent_diagonal hq₀ hq₁ hτ, hn, hl,
    ← Complex.ofReal_exp, scaledCoherentGaussianDiagonal, multiBargmannPrefactor_norm_sq]
  simp only [multiBargmannKernel, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  ring

theorem multiThermalSandwichCoherentDiagonal_nonneg {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (z : Fin m → ℂ) : 0 ≤ multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z := by
  unfold multiThermalSandwichCoherentDiagonal multiThermalSandwichForm
  exact mul_nonneg (inv_nonneg.mpr (pow_nonneg Real.pi_pos.le _))
    ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).re_inner_nonneg_right _)

theorem multiInverseThermalDiagonal_nonneg {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (τ : ℝ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A)
    (k : Fin m → ℕ) : 0 ≤ multiInverseThermalDiagonal q τ A k :=
  mul_nonneg (Real.rpow_nonneg (multiModeThermalWeight_pos hq₀ hq₁ k).le _)
    ((ContinuousLinearMap.nonneg_iff_isPositive.mp hA).re_inner_nonneg_right _)

/-- A pre-extension identity on the actual inverse domain; either side
may be infinite. In particular, finiteness is not a premise. -/
theorem lintegral_multiThermalSandwichCoherentDiagonal {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A) :
    (∫⁻ z : Fin m → ℂ,
      ENNReal.ofReal (multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z)) =
        ∑' k, ENNReal.ofReal (multiInverseThermalDiagonal q τ A k) := by
  have hZ : 0 ≤ (∏ j, (1 - q j)) ^ (-τ) :=
    Real.rpow_nonneg (Finset.prod_nonneg fun j _ => sub_nonneg.mpr (hq₁ j).le) _
  rw [← (multiConjugation_measurePreserving m).lintegral_comp_emb
    (multiConjugation m).measurableEmbedding
    (fun z => ENNReal.ofReal (multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z))]
  simp_rw [multiThermalSandwichCoherentDiagonal_conj hq₀ hq₁ hτ,
    ENNReal.ofReal_mul hZ]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_scaledCoherentGaussianDiagonal hA, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [← ENNReal.ofReal_mul hZ, ← mul_assoc, thermal_occupationScale hq₀ hq₁]
  rfl

/-- The literal inverse-coherent integral is finite exactly when the
weighted number-state diagonal is summable. -/
theorem lintegral_multiThermalSandwichCoherentDiagonal_lt_top_iff {m : ℕ}
    {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A) :
    (∫⁻ z : Fin m → ℂ,
      ENNReal.ofReal (multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z)) < ⊤ ↔
        Summable (multiInverseThermalDiagonal q τ A) := by
  rw [lintegral_multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ hA]
  have hn := multiInverseThermalDiagonal_nonneg hq₀ hq₁ τ hA
  constructor
  · intro h
    simpa only [ENNReal.toReal_ofReal (hn _)] using ENNReal.summable_toReal h.ne
  · intro hs
    rw [← ENNReal.ofReal_tsum_of_nonneg hn hs]
    exact ENNReal.ofReal_lt_top

/-- Noncommuting positive trace-class sandwich existence, decided by the
actual inverse-domain coherent integral with its full π normalization. -/
theorem exists_positiveTraceClass_multiThermal_factorization_iff_coherentIntegral
    {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    {A : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m} (hA : 0 ≤ A) :
    (∃ Θ : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m,
      IsPositiveTraceClass Θ ∧
      (multiModeThermalDensity q ^ (τ / 2)) * Θ *
        (multiModeThermalDensity q ^ (τ / 2)) = A) ↔
      (∫⁻ z : Fin m → ℂ,
        ENNReal.ofReal (multiThermalSandwichCoherentDiagonal hq₀ hq₁ hτ A z)) < ⊤ := by
  rw [exists_positiveTraceClass_multiThermal_factorization_iff hq₀ hq₁ hτ hA,
    lintegral_multiThermalSandwichCoherentDiagonal_lt_top_iff hq₀ hq₁ hτ hA]

end VacuumBellSeparation.Gaussian
