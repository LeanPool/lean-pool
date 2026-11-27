/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PhysicalGaussianHusimi
public import LeanPool.VacuumBellSeparation.Gaussian.MultiModeThermalCharacteristic
public import LeanPool.VacuumBellSeparation.Gaussian.CommutingAppendixA

/-!
# Thermal states are the actual density expectations in fixed Weyl labels

The true square root of the diagonal density identifies the two previously
constructed complex expectations on every bounded operator. The product
thermal density consequently satisfies the actual physical Gaussian
characteristic predicate. The reference sandwich at ρ=σ is an equality
of actual CFC powers on the full oscillator space.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix ContinuousLinearMap
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem densityExpectation_indexedDiagonalOperator {ι E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (b : HilbertBasis ι ℂ E) {w : ι → ℝ} (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k)
    (B : E →L[ℂ] E) :
    densityExpectation b (indexedDiagonalOperator b w) B = indexedDiagonalExpectation b w B := by
  apply tsum_congr
  intro k
  change inner ℂ (CFC.sqrt (indexedDiagonalOperator b w) (b k))
    (B (CFC.sqrt (indexedDiagonalOperator b w) (b k))) =
      (w k : ℂ) * inner ℂ (b k) (B (b k))
  rw [sqrt_indexedDiagonalOperator_apply_basis b hw hw₀,
    map_smul_of_tower, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
  simp only [Algebra.smul_def, Complex.coe_algebraMap]
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (hw₀ k)]

theorem densityExpectation_multiModeThermalDensity {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1)
    (B : MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :
    densityExpectation (multiModeNumberBasis m) (multiModeThermalDensity q) B =
      multiThermalState hq₀ hq₁ B :=
  densityExpectation_indexedDiagonalOperator (multiModeNumberBasis m)
    (hasSum_multiModeThermalWeight hq₀ hq₁).summable
    (multiModeThermalWeight_nonneg hq₀ hq₁) B

theorem physicalDisplacementCovariance_modeDiagonal {m : ℕ} (d : Fin m → ℝ) :
    physicalDisplacementCovariance (modeDiagonal d) = modeDiagonal d := by
  rw [physicalDisplacementCovariance, mul_assoc, (modeDiagonal_commute_symplectic d).eq,
    ← mul_assoc, modeSymplecticForm_transpose_mul, one_mul]

theorem multiModeThermalDensity_hasGaussianPhysicalCharacteristic {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    HasGaussianPhysicalCharacteristic (multiModeThermalDensity q)
      (modeDiagonal (fun j => thermalQuadratureVariance (q j))) := by
  intro z
  rw [densityExpectation_multiModeThermalDensity hq₀ hq₁,
    multiThermalState_oscillatorWeyl hq₀ hq₁,
    physicalDisplacementCovariance_modeDiagonal, dotProduct_modeDiagonal]
  simp only [complexRealCoordinates_apply,
    complexRealCoordinates_apply_one]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two]

theorem multiModeThermalDensity_reference_factorization {m : ℕ}
    {q : Fin m → ℝ} {τ : ℝ} (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1)
    (hτ₀ : 0 < τ) (hτ₁ : τ < 1) :
    (multiModeThermalDensity q ^ (τ / 2)) *
      (multiModeThermalDensity q ^ (1 - τ)) *
        (multiModeThermalDensity q ^ (τ / 2)) = multiModeThermalDensity q := by
  apply continuousLinearMap_eq_of_dense_span (multiModeNumberBasis _)
    (multiModeNumberBasis _).dense_span
  intro k
  simp only [mul_apply_eq_comp]
  rw [multiModeThermalDensity_rpow_apply_numberBasis (fun j => (hq₀ j).le) hq₁ (half_pos hτ₀),
    map_smul_of_tower,
    multiModeThermalDensity_rpow_apply_numberBasis (fun j => (hq₀ j).le) hq₁ (sub_pos.mpr hτ₁),
    map_smul_of_tower, map_smul_of_tower,
    multiModeThermalDensity_rpow_apply_numberBasis (fun j => (hq₀ j).le) hq₁ (half_pos hτ₀),
    multiModeThermalDensity_apply_numberBasis (fun j => (hq₀ j).le) hq₁,
    smul_smul, smul_smul]
  congr 1
  rw [← Real.rpow_add (multiModeThermalWeight_pos hq₀ hq₁ k),
    ← Real.rpow_add (multiModeThermalWeight_pos hq₀ hq₁ k),
    show τ / 2 + (1 - τ) + τ / 2 = 1 by ring, Real.rpow_one]

end VacuumBellSeparation.Gaussian
