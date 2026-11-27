/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalPowers
public import LeanPool.VacuumBellSeparation.Gaussian.WeylCoherentRepresentation

/-!
# Coherent kernels of actual thermal operator powers

The number-basis eigenvector theorem for the genuine CFC power implies
its action on every exponential vector and hence the normalized coherent
kernel. All formulas include the pure endpoint `q=0` at positive exponent.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ComplexConjugate

theorem thermalDensity_rpow_apply_coordinate {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) (x : OscillatorSpace) (n : ℕ) :
    (thermalDensity q ^ τ) x n = (thermalWeight q n ^ τ : ℝ) * x n := by
  have hA : IsSelfAdjoint (thermalDensity q ^ τ) := CFC.rpow_nonneg.isSelfAdjoint
  have h := ((thermalDensity q ^ τ).adjoint_inner_left x (numberBasis n)).symm
  simpa only [hA.adjoint_eq, thermalDensity_rpow_apply_numberBasis hq₀ hq₁ hτ,
    inner_smul_left_eq_smul, Algebra.smul_def, Complex.coe_algebraMap, numberBasis_inner] using h

theorem thermalDensity_rpow_apply_exponentialVector {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) (z : ℂ) :
    (thermalDensity q ^ τ) (exponentialVector z) =
      ((1 - q) ^ τ : ℝ) • exponentialVector ((q ^ τ : ℝ) * z) := by
  apply lp.ext
  funext n
  rw [thermalDensity_rpow_apply_coordinate hq₀ hq₁ hτ,
    thermalWeight_rpow hq₀ hq₁]
  change (((1 - q) ^ τ * (q ^ τ) ^ n : ℝ) : ℂ) * coherentCoefficient z n =
    ((1 - q) ^ τ : ℝ) • coherentCoefficient ((q ^ τ : ℝ) * z) n
  simp only [coherentCoefficient, Complex.ofReal_mul, Complex.ofReal_pow,
    RCLike.real_smul_eq_coe_mul, RCLike.ofReal_eq_complex_ofReal, mul_pow, div_eq_mul_inv]
  simp only [mul_assoc, mul_left_comm, mul_comm]

theorem thermalDensity_rpow_exponential_kernel {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) (z w : ℂ) :
    inner ℂ (exponentialVector z) ((thermalDensity q ^ τ) (exponentialVector w)) =
      ((1 - q) ^ τ : ℝ) * Complex.exp ((q ^ τ : ℝ) * (conj z * w)) := by
  rw [thermalDensity_rpow_apply_exponentialVector hq₀ hq₁ hτ w,
    inner_smul_right_eq_smul, inner_exponentialVector z ((q ^ τ : ℝ) * w),
    RCLike.real_smul_eq_coe_mul]
  congr 2
  ring

theorem thermalDensity_rpow_coherent_kernel {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) (z w : ℂ) :
    inner ℂ (coherentVector z) ((thermalDensity q ^ τ) (coherentVector w)) =
      ((1 - q) ^ τ : ℝ) * Complex.exp
        (((-(‖z‖ ^ 2 / 2) - ‖w‖ ^ 2 / 2 : ℝ) : ℂ) +
          (q ^ τ : ℝ) * (conj z * w)) := by
  dsimp only [coherentVector]
  rw [map_smul, inner_smul_left, inner_smul_right,
    thermalDensity_rpow_exponential_kernel hq₀ hq₁ hτ,
    ← Complex.exp_conj, Complex.conj_ofReal]
  calc
    _ = ((1 - q) ^ τ : ℝ) *
        (Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) *
          Complex.exp ((-(‖w‖ ^ 2 / 2) : ℝ) : ℂ) *
          Complex.exp ((q ^ τ : ℝ) * (conj z * w))) := by ring
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem thermalDensity_rpow_coherent_diagonal {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) (z : ℂ) :
    inner ℂ (coherentVector z) ((thermalDensity q ^ τ) (coherentVector z)) =
      (((1 - q) ^ τ * Real.exp (-(1 - q ^ τ) * ‖z‖ ^ 2) : ℝ) : ℂ) := by
  rw [thermalDensity_rpow_coherent_kernel hq₀ hq₁ hτ, Complex.conj_mul',
    Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

end VacuumBellSeparation.Gaussian
