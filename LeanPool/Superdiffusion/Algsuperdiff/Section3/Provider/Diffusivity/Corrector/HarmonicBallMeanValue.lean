/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicMeanValue
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicGauge

/-!
# HarmonicBallMeanValue

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Ball and radial-moment bookkeeping for the mean value property on `Vec d`

`HarmonicMeanValue` proves the mean value property in *kernel* form: the pairing
of a harmonic function against a continuous radial density supported in an
annulus `[a, b]` of positive radial moment reproduces `u z` times the mass of the
density.  That statement avoids surface measure, the coarea formula and polar
decomposition entirely, and it is stated for a weight rather than for the
normalized indicator of a ball.

This module collects the two elementary facts a caller of that kernel form
needs before it can be read at an explicit Euclidean ball: the ball has finite
Lebesgue measure, and a density that is merely *positive on a subinterval* of
its support already has positive radial moment, which is the shape in which the
kernel hypothesis is usually verified.

No coarea formula, no surface measure and no polar decomposition is used, and
no `EuclideanSpace` transfer appears anywhere: everything stays on `Vec d` with
the explicit Euclidean balls.

## Contents

* `volume_euclideanBall_ne_top` -- an explicit Euclidean ball has finite
  Lebesgue measure.
* `radialMoment_pos_of_pos_on` -- positivity of a radial moment from positivity
  on a subinterval.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Explicit Euclidean balls have finite Lebesgue measure. -/
theorem volume_euclideanBall_ne_top (z : Vec d) (ρ : ℝ) :
    volume (euclideanBall z ρ) ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (measure_mono (euclideanBall_subset_euclideanClosedBall_abs z ρ))
    (isCompact_euclideanClosedBall z (abs_nonneg ρ)).measure_lt_top)

/-- Positivity of the radial moment from positivity on a subinterval. -/
theorem radialMoment_pos_of_pos_on {m : ℕ} {k : ℝ → ℝ} (hk : Continuous k)
    (hknn : ∀ t : ℝ, 0 ≤ k t) {p q b : ℝ} (hp : 0 < p) (hpq : p < q) (hqb : q ≤ b)
    (hpos : ∀ t : ℝ, p < t → t < q → 0 < k t) : 0 < radialMoment m k b := by
  have hcont : Continuous fun s : ℝ => s ^ m * k s := (continuous_pow m).mul hk
  have hsplit₁ := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (f := fun s : ℝ => s ^ m * k s) (a := 0) (b := p) (c := q)
    (hcont.intervalIntegrable 0 p) (hcont.intervalIntegrable p q)
  have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals
    (μ := volume) (f := fun s : ℝ => s ^ m * k s) (a := 0) (b := q) (c := b)
    (hcont.intervalIntegrable 0 q) (hcont.intervalIntegrable q b)
  have h1 : (0 : ℝ) ≤ ∫ s in (0 : ℝ)..p, s ^ m * k s :=
    intervalIntegral.integral_nonneg hp.le fun s hs =>
      mul_nonneg (pow_nonneg hs.1 m) (hknn s)
  have h2 : (0 : ℝ) < ∫ s in p..q, s ^ m * k s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable p q)
      (fun s hs => mul_pos (pow_pos (hp.trans hs.1) m) (hpos s hs.1 hs.2)) hpq
  have h3 : (0 : ℝ) ≤ ∫ s in q..b, s ^ m * k s :=
    intervalIntegral.integral_nonneg hqb fun s hs =>
      mul_nonneg (pow_nonneg (le_trans (le_of_lt (hp.trans hpq)) hs.1) m) (hknn s)
  rw [radialMoment, ← hsplit₂, ← hsplit₁]
  linarith

variable {m : ℕ}

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
