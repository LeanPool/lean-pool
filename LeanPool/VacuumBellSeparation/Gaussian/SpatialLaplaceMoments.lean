/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselRationalBounds
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Actual Laplace moments for the spatial kernel majorants

All integrals use real Lebesgue measure on the open positive half-line.
Convergence is established separately from the Gamma evaluations.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Set

theorem integrableOn_laplace_rpow {x q : ℝ} (hx : 0 < x) (hq : -1 < q) :
    IntegrableOn (fun v : ℝ => v ^ q * Real.exp (-x * v)) (Ioi 0) := by
  simpa only [Real.rpow_one] using
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) hq zero_lt_one hx

theorem integral_laplace_rpow {x q : ℝ} (hx : 0 < x) (hq : -1 < q) :
    (∫ v in Ioi (0 : ℝ), v ^ q * Real.exp (-x * v)) =
      x ^ (-(q + 1)) * Real.Gamma (q + 1) := by
  simpa only [Real.rpow_one, div_one, one_div_one, mul_one] using
    integral_rpow_mul_exp_neg_mul_rpow (p := 1) zero_lt_one hq hx

theorem integrableOn_laplace_constant {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v : ℝ => Real.exp (-x * v)) (Ioi 0) := by
  simpa only [Real.rpow_zero, one_mul] using integrableOn_laplace_rpow hx (q := 0) (by norm_num)

theorem integral_laplace_constant {x : ℝ} (hx : 0 < x) :
    (∫ v in Ioi (0 : ℝ), Real.exp (-x * v)) = x⁻¹ := by
  simpa only [Real.rpow_zero, one_mul, zero_add, Real.Gamma_one, mul_one,
    Real.rpow_neg_one] using integral_laplace_rpow hx (q := 0) (by norm_num)

theorem integrableOn_laplace_linear {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v : ℝ => v * Real.exp (-x * v)) (Ioi 0) := by
  simpa only [Real.rpow_one] using integrableOn_laplace_rpow hx (q := 1) (by norm_num)

theorem integral_laplace_linear {x : ℝ} (hx : 0 < x) :
    (∫ v in Ioi (0 : ℝ), v * Real.exp (-x * v)) = (x ^ 2)⁻¹ := by
  have h := integral_laplace_rpow hx (q := 1) (by norm_num)
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    simp
  norm_num only [one_add_one_eq_two, Real.rpow_one, hg, mul_one] at h
  rw [Real.rpow_neg hx.le, Real.rpow_two] at h
  exact h

theorem inverse_sqrt_two_mul_eq_rpow {v : ℝ} (hv : 0 ≤ v) :
    (Real.sqrt (2 * v))⁻¹ = (Real.sqrt 2)⁻¹ * v ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_mul (by norm_num), mul_inv_rev, Real.rpow_neg hv,
    ← Real.sqrt_eq_rpow]
  ring

theorem integrableOn_laplace_inverse_sqrt {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun v : ℝ => (Real.sqrt (2 * v))⁻¹ * Real.exp (-x * v))
      (Ioi 0) := by
  have h := (integrableOn_laplace_rpow hx (q := -(1 / 2 : ℝ)) (by norm_num)).const_mul
    (Real.sqrt 2)⁻¹
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  change (Real.sqrt 2)⁻¹ * (v ^ (-(1 / 2 : ℝ)) * Real.exp (-x * v)) =
    (Real.sqrt (2 * v))⁻¹ * Real.exp (-x * v)
  rw [inverse_sqrt_two_mul_eq_rpow hv.le]
  ring

theorem integral_laplace_inverse_sqrt {x : ℝ} (hx : 0 < x) :
    (∫ v in Ioi (0 : ℝ), (Real.sqrt (2 * v))⁻¹ * Real.exp (-x * v)) =
      Real.sqrt (Real.pi / (2 * x)) := by
  calc
    _ = (Real.sqrt 2)⁻¹ *
        ∫ v in Ioi (0 : ℝ), v ^ (-(1 / 2 : ℝ)) * Real.exp (-x * v) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro v hv
      dsimp only
      rw [inverse_sqrt_two_mul_eq_rpow hv.le]
      ring
    _ = (Real.sqrt 2)⁻¹ * (x ^ (-(1 / 2 : ℝ)) * Real.sqrt Real.pi) := by
      rw [integral_laplace_rpow hx (by norm_num)]
      norm_num only [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
        Real.Gamma_one_half_eq]
    _ = Real.sqrt (Real.pi / (2 * x)) := by
      rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow,
        Real.sqrt_div Real.pi_pos.le, Real.sqrt_mul (by norm_num)]
      ring

end VacuumBellSeparation.Gaussian
