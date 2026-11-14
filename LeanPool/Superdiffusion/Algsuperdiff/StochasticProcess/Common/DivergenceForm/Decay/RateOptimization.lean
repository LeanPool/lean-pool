/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.BallAverage

/-!
# RateOptimization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Balancing an averaged term against a Hölder term

The interior pointwise estimate bounds a value by an `L²` average on a ball of
radius `rho` plus a Hölder modulus of order `rho ^ alpha`.  When the `L²` term
already carries an exponential factor `exp (-(kappa * s))`, choosing
`rho = R * exp (-(kappa * s) / (alpha + d / 2))` balances the two and produces
the reduced exponential rate `kappa * alpha / (alpha + d / 2)`.

The cap `R` on the admissible radii is a parameter, so the statement is scale
free: it may be as small as the consumer's ball allows, and the constant is
simply the two-term bound evaluated at `R`.  Because the balancing radius is
`R` times a factor at most one, it is always admissible, so there is no case
distinction and no lost constant factor.

## Main results

- `DivergenceFormProcess.Decay.sqrt_exp_eq`
- `DivergenceFormProcess.Decay.le_mul_exp_of_two_term_bound`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

/-- The square root of an exponential. -/
theorem sqrt_exp_eq (y : ℝ) :
    Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  have hsq : Real.exp (y / 2) ^ 2 = Real.exp y := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [← hsq, Real.sqrt_sq (Real.exp_nonneg _)]

/-- Balancing the averaged term against the Hölder term.  A bound valid for
every radius up to `R` yields an exponential bound at the reduced rate, with
the constant read off at the radius `R`. -/
theorem le_mul_exp_of_two_term_bound {d : ℕ} {A B kappa alpha s R F : ℝ}
    (hR : 0 < R) (halpha0 : 0 < alpha) (hkappa : 0 ≤ kappa) (hs : 0 ≤ s)
    (hF : ∀ rho : ℝ, 0 < rho → rho ≤ R →
      F ≤ A * Real.exp (-(kappa * s)) / Real.sqrt (rho ^ d) +
        B * rho ^ alpha) :
    F ≤ (A / Real.sqrt (R ^ d) + B * R ^ alpha) *
      Real.exp (-(kappa * alpha / (alpha + (d : ℝ) / 2) * s)) := by
  have hden : 0 < alpha + (d : ℝ) / 2 := by positivity
  set t : ℝ := kappa * s / (alpha + (d : ℝ) / 2) with hT
  have ht0 : 0 ≤ t := by
    rw [hT]
    exact div_nonneg (mul_nonneg hkappa hs) hden.le
  have hks : kappa * s = (alpha + (d : ℝ) / 2) * t := by
    rw [hT]
    field_simp
  have hrate : kappa * alpha / (alpha + (d : ℝ) / 2) * s = alpha * t := by
    rw [hT]
    field_simp
  have hexple : Real.exp (-t) ≤ 1 := by
    have hstep := Real.exp_le_exp.2 (neg_nonpos.2 ht0)
    rwa [Real.exp_zero] at hstep
  have hrhopos : 0 < R * Real.exp (-t) := mul_pos hR (Real.exp_pos _)
  have hrhoR : R * Real.exp (-t) ≤ R := mul_le_of_le_one_right hR.le hexple
  have hbound := hF (R * Real.exp (-t)) hrhopos hrhoR
  have hS : Real.sqrt (R ^ d) ≠ 0 := (Real.sqrt_pos.2 (pow_pos hR d)).ne'
  have hY : Real.exp ((d : ℝ) * (-t) / 2) ≠ 0 := (Real.exp_pos _).ne'
  have hsqrtsplit : Real.sqrt ((R * Real.exp (-t)) ^ d) =
      Real.sqrt (R ^ d) * Real.exp ((d : ℝ) * (-t) / 2) := by
    rw [mul_pow, ← Real.exp_nat_mul, Real.sqrt_mul (pow_nonneg hR.le d),
      sqrt_exp_eq]
  have hexpsplit : Real.exp (-(kappa * s)) =
      Real.exp (-(alpha * t)) * Real.exp ((d : ℝ) * (-t) / 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hks]
    ring
  have hterm1 : A * Real.exp (-(kappa * s)) /
      Real.sqrt ((R * Real.exp (-t)) ^ d) =
      A / Real.sqrt (R ^ d) * Real.exp (-(alpha * t)) := by
    rw [hsqrtsplit, hexpsplit]
    field_simp
  have hterm2 : B * (R * Real.exp (-t)) ^ alpha =
      B * R ^ alpha * Real.exp (-(alpha * t)) := by
    rw [Real.mul_rpow hR.le (Real.exp_nonneg _), ← Real.exp_mul,
      show -t * alpha = -(alpha * t) by ring]
    ring
  rw [hrate]
  calc
    F ≤ A * Real.exp (-(kappa * s)) / Real.sqrt ((R * Real.exp (-t)) ^ d) +
        B * (R * Real.exp (-t)) ^ alpha := hbound
    _ = (A / Real.sqrt (R ^ d) + B * R ^ alpha) *
        Real.exp (-(alpha * t)) := by
      rw [hterm1, hterm2]
      ring

end DivergenceFormProcess.Decay
