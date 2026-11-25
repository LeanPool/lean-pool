/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RadialPoissonCertificate

/-!
# The radial Poisson slope

This file records the one-variable quotient that solves the radial Poisson
equation away from the origin.  The construction is kept local to the
positive half-line; no regularity at the origin is asserted here.
-/

@[expose] public section

namespace SGPT.Foundations.Analysis.Pending.RadialPoissonSlope

open RadialPoissonCertificate

/-- The slope in the squared-radius variable for the radial Poisson
primitive. -/
noncomputable def radialPoissonSlope
    (n : ℕ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  radialWeightedCumulative n g s / (4 * s ^ n)

/-- On the positive half-line, the radial Poisson slope has the derivative
given by the quotient-rule formula in ODE form. -/
theorem radialPoissonSlope_hasDerivAt
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (radialPoissonSlope n g)
      (g s / (4 * s) - (n : ℝ) * radialPoissonSlope n g s / s) s := by
  have hC := radialWeightedCumulative_hasDerivAt (n := n) hg s
  have hD : HasDerivAt (fun t : ℝ => 4 * t ^ n)
      (4 * ((n : ℝ) * s ^ (n - 1))) s := by
    have hfun : (fun y : ℝ => 4 * (id ^ n) y) =
        (fun t : ℝ => 4 * t ^ n) := by
      funext t
      rfl
    have hraw := hasDerivAt_iff_tendsto_slope.mp
      ((hasDerivAt_id s).pow n |>.const_mul 4)
    rw [hasDerivAt_iff_tendsto_slope, ← hfun]
    simpa only [id_eq, mul_one, mul_assoc] using hraw
  have hquot := hC.div hD
    (mul_ne_zero (by norm_num) (pow_ne_zero n hs.ne'))
  apply hquot.congr_deriv
  rw [radialPoissonSlope]
  have hn' : n = n - 1 + 1 := by omega
  have hsn : s ^ n = s ^ (n - 1) * s :=
    (congrArg (fun k : ℕ => s ^ k) hn').trans (pow_succ _ _)
  field_simp [hs.ne', pow_ne_zero n hs.ne']
  rw [hsn]
  ring

/-- The defining first-order radial Poisson equation on the positive
half-line. -/
theorem radialPoissonSlope_ode
    {n : ℕ} (hn : 0 < n) {g : ℝ → ℝ} (hg : Continuous g)
    {s : ℝ} (hs : 0 < s) :
    4 * (s * deriv (radialPoissonSlope n g) s +
      (n : ℝ) * radialPoissonSlope n g s) = g s := by
  rw [(radialPoissonSlope_hasDerivAt hn hg hs).deriv]
  field_simp
  ring

/-- A nonpositive weighted cumulative term gives a nonpositive Poisson slope
at every positive squared radius. -/
theorem radialPoissonSlope_nonpos
    {n : ℕ} {g : ℝ → ℝ} {s : ℝ} (hs : 0 < s)
    (hC : radialWeightedCumulative n g s ≤ 0) :
    radialPoissonSlope n g s ≤ 0 := by
  rw [radialPoissonSlope]
  exact div_nonpos_of_nonpos_of_nonneg hC
    (mul_nonneg (by norm_num) (pow_nonneg hs.le n))

end SGPT.Foundations.Analysis.Pending.RadialPoissonSlope
