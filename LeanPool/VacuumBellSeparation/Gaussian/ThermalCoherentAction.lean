/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalCoherentPowers

/-!
# Actual normalized coherent action of thermal powers

The coefficient is derived from the actual CFC action on exponential
vectors and the coherent normalization. In particular no formal inverse
or diagonalization assumption occurs in the square-root action.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

theorem thermalDensity_rpow_apply_coherentVector {q τ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (hτ : 0 < τ) (z : ℂ) :
    (thermalDensity q ^ τ) (coherentVector z) =
      ((((1 - q) ^ τ : ℝ) : ℂ) *
        Complex.exp ((((q ^ τ) ^ 2 - 1) * ‖z‖ ^ 2 / 2 : ℝ) : ℂ)) •
          coherentVector ((q ^ τ : ℝ) * z) := by
  have hq : 0 ≤ q ^ τ := Real.rpow_nonneg hq₀ _
  have hn : ‖((q ^ τ : ℝ) : ℂ) * z‖ ^ 2 = (q ^ τ) ^ 2 * ‖z‖ ^ 2 := by
    rw [norm_mul, Complex.norm_of_nonneg hq, mul_pow]
  rw [coherentVector, map_smul,
    thermalDensity_rpow_apply_exponentialVector hq₀ hq₁ hτ,
    RCLike.real_smul_eq_coe_smul (K := ℂ), coherentVector, smul_smul, smul_smul, hn]
  simp only [RCLike.ofReal_eq_complex_ofReal]
  congr 1
  calc
    _ = (((1 - q) ^ τ : ℝ) : ℂ) * Complex.exp ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) :=
      mul_comm _ _
    _ = _ := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem sqrt_thermalDensity_apply_coherentVector {q : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (z : ℂ) :
    CFC.sqrt (thermalDensity q) (coherentVector z) =
      (((Real.sqrt (1 - q) * Real.exp (-(1 - q) * ‖z‖ ^ 2 / 2) : ℝ) : ℂ)) •
        coherentVector ((Real.sqrt q : ℝ) * z) := by
  rw [CFC.sqrt_eq_rpow,
    thermalDensity_rpow_apply_coherentVector hq₀ hq₁ (by norm_num),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hq₀]
  congr 1
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

end VacuumBellSeparation.Gaussian
