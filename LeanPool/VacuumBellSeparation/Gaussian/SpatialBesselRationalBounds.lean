/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Positivity

/-!
# Rational densities in the shifted Bessel-Laplace integrals

After the literal change of variable v=cosh(u)-1, the K1 and K2 integral
densities are (v+1)/sqrt(v(v+2)) and (2v²+4v+1)/sqrt(v(v+2)).
This module proves the exact pointwise majorants used by the manuscript.
It does not identify a Fourier kernel or assume the integral substitution.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

/-- Shifted Bessel density one given by `(v + 1) / Real.sqrt (v * (v + 2))`. -/
noncomputable def shiftedBesselDensityOne (v : ℝ) : ℝ :=
  (v + 1) / Real.sqrt (v * (v + 2))

/-- Shifted Bessel density two given by `(2 * v ^ 2 + 4 * v + 1) / Real.sqrt (v * (v + 2))`. -/
noncomputable def shiftedBesselDensityTwo (v : ℝ) : ℝ :=
  (2 * v ^ 2 + 4 * v + 1) / Real.sqrt (v * (v + 2))

theorem shiftedBessel_denominator_pos {v : ℝ} (hv : 0 < v) :
    0 < Real.sqrt (v * (v + 2)) := Real.sqrt_pos.mpr (mul_pos hv (by linarith))

theorem le_shiftedBessel_denominator {v : ℝ} (hv : 0 ≤ v) :
    v ≤ Real.sqrt (v * (v + 2)) := by
  have hs := Real.sq_sqrt (show 0 ≤ v * (v + 2) by positivity)
  have hn := Real.sqrt_nonneg (v * (v + 2))
  nlinarith

theorem sqrt_two_mul_le_shiftedBessel_denominator {v : ℝ} (hv : 0 ≤ v) :
    Real.sqrt (2 * v) ≤ Real.sqrt (v * (v + 2)) := by
  apply Real.sqrt_le_sqrt
  nlinarith

theorem shiftedBesselDensityOne_nonneg {v : ℝ} (hv : 0 < v) :
    0 ≤ shiftedBesselDensityOne v := by
  unfold shiftedBesselDensityOne
  positivity

theorem shiftedBesselDensityTwo_nonneg {v : ℝ} (hv : 0 < v) :
    0 ≤ shiftedBesselDensityTwo v := by
  unfold shiftedBesselDensityTwo
  positivity

theorem shiftedBesselDensityOne_le {v : ℝ} (hv : 0 < v) :
    shiftedBesselDensityOne v ≤ 1 + (Real.sqrt (2 * v))⁻¹ := by
  have hd := shiftedBessel_denominator_pos hv
  have hfirst : v / Real.sqrt (v * (v + 2)) ≤ 1 :=
    (div_le_one hd).mpr (le_shiftedBessel_denominator hv.le)
  have hsecond : 1 / Real.sqrt (v * (v + 2)) ≤ 1 / Real.sqrt (2 * v) :=
    div_le_div_of_nonneg_left zero_le_one (Real.sqrt_pos.mpr (by positivity))
      (sqrt_two_mul_le_shiftedBessel_denominator hv.le)
  simpa only [shiftedBesselDensityOne, add_div, one_div] using add_le_add hfirst hsecond

theorem shiftedBesselDensityTwo_le {v : ℝ} (hv : 0 < v) :
    shiftedBesselDensityTwo v ≤ 2 * v + 4 + (Real.sqrt (2 * v))⁻¹ := by
  have hd := shiftedBessel_denominator_pos hv
  have hfirst : v / Real.sqrt (v * (v + 2)) ≤ 1 :=
    (div_le_one hd).mpr (le_shiftedBessel_denominator hv.le)
  have hsecond : 1 / Real.sqrt (v * (v + 2)) ≤ 1 / Real.sqrt (2 * v) :=
    div_le_div_of_nonneg_left zero_le_one (Real.sqrt_pos.mpr (by positivity))
      (sqrt_two_mul_le_shiftedBessel_denominator hv.le)
  have hpoly := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ 2 * v + 4 by positivity)
  calc
    shiftedBesselDensityTwo v = (2 * v + 4) * (v / Real.sqrt (v * (v + 2))) +
        1 / Real.sqrt (v * (v + 2)) := by
      unfold shiftedBesselDensityTwo
      ring
    _ ≤ (2 * v + 4) * 1 + 1 / Real.sqrt (2 * v) := add_le_add hpoly hsecond
    _ = _ := by rw [mul_one, one_div]

end VacuumBellSeparation.Gaussian
