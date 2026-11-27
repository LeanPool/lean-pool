/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SpatialBesselCompatibility

/-!
# The actual full-line exponential representation of K

This is the intermediate integral needed for the heat-parameter
substitution. Gaussian domination from the existing Bessel module proves
absolute convergence before the reflection and symmetrization steps.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open MeasureTheory Set

theorem cosh_mul_abs (ν u : ℝ) : Real.cosh (ν * |u|) = Real.cosh (ν * u) := by
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
  · rw [abs_of_neg hu, mul_neg, Real.cosh_neg]

theorem integrable_bessel_cosh_fullLine (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun u : ℝ => Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) := by
  have hg : Integrable (fun u : ℝ =>
      Real.exp (-x + ν ^ 2 / x) * Real.exp (-(x / 4) * u ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < x / 4)).const_mul _
  apply hg.mono' (Continuous.aestronglyMeasurable (by fun_prop))
  exact Filter.Eventually.of_forall (fun u => by
    simpa only [Real.cosh_abs, cosh_mul_abs, sq_abs, neg_mul] using
      BesselK.norm_integrand_le_gaussian ν hx (abs_nonneg u))

theorem exp_neg_le_two_cosh (v : ℝ) : Real.exp (-v) ≤ 2 * Real.cosh v := by
  rw [Real.cosh_eq]
  linarith [Real.exp_pos v]

theorem integrable_bessel_exp_fullLine (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    Integrable (fun u : ℝ => Real.exp (-ν * u) * Real.exp (-x * Real.cosh u)) := by
  apply ((integrable_bessel_cosh_fullLine ν hx).const_mul 2).mono'
    (Continuous.aestronglyMeasurable (by fun_prop))
  refine Filter.Eventually.of_forall (fun u => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have h := mul_le_mul_of_nonneg_right (exp_neg_le_two_cosh (ν * u)) (Real.exp_pos
    (-x * Real.cosh u)).le
  calc
    Real.exp (-ν * u) * Real.exp (-x * Real.cosh u) =
        Real.exp (-(ν * u)) * Real.exp (-x * Real.cosh u) := by rw [neg_mul ν u]
    _ ≤ (2 * Real.cosh (ν * u)) * Real.exp (-x * Real.cosh u) := h
    _ = 2 * (Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) := by ring

theorem integral_bessel_cosh_fullLine (ν : ℝ) (x : ℝ) :
    (∫ u : ℝ, Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) =
      2 * besselKReal ν x := by
  have h := integral_comp_abs (f := fun u : ℝ =>
    Real.exp (-x * Real.cosh u) * Real.cosh (ν * u))
  simpa only [Real.cosh_abs, cosh_mul_abs, besselKReal, neg_mul] using h

theorem integral_bessel_exp_fullLine (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ, Real.exp (-ν * u) * Real.exp (-x * Real.cosh u)) =
      2 * besselKReal ν x := by
  have hm := integrable_bessel_exp_fullLine ν hx
  have hp : Integrable (fun u : ℝ => Real.exp (ν * u) * Real.exp (-x * Real.cosh u)) := by
    simpa only [neg_neg] using integrable_bessel_exp_fullLine (-ν) hx
  have href : (∫ u : ℝ, Real.exp (ν * u) * Real.exp (-x * Real.cosh u)) =
      ∫ u : ℝ, Real.exp (-ν * u) * Real.exp (-x * Real.cosh u) := by
    simpa only [neg_mul, mul_neg, neg_neg, Real.cosh_neg] using
      integral_neg_eq_self (fun u : ℝ => Real.exp (-ν * u) *
        Real.exp (-x * Real.cosh u)) volume
  have hsum : (∫ u : ℝ, Real.exp (-ν * u) * Real.exp (-x * Real.cosh u)) +
      (∫ u : ℝ, Real.exp (ν * u) * Real.exp (-x * Real.cosh u)) =
      2 * (2 * besselKReal ν x) := by
    rw [← integral_add hm hp]
    calc
      _ = ∫ u : ℝ, 2 * (Real.exp (-x * Real.cosh u) * Real.cosh (ν * u)) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun u => ?_)
        change Real.exp (-ν * u) * Real.exp (-x * Real.cosh u) +
          Real.exp (ν * u) * Real.exp (-x * Real.cosh u) =
            2 * (Real.exp (-x * Real.cosh u) * Real.cosh (ν * u))
        rw [Real.cosh_eq (ν * u), neg_mul]
        ring
      _ = _ := by rw [integral_const_mul, integral_bessel_cosh_fullLine]
  rw [href] at hsum
  linarith

end VacuumBellSeparation.Gaussian
