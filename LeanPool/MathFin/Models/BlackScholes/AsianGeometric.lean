/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.BlackScholes.AsianGeometricN

/-!
# The geometric-average Asian option: the two-date effective variance

`Models/BlackScholes/AsianInequality.lean` bounds the geometric-average Asian payoff above by the
arithmetic one (AM–GM). This file supplies the distributional content that turns the
geometric average into a *priceable* lognormal: for a Black–Scholes GBM
`S_u = S₀·exp((r − σ²/2)u + σ B_u)` sampled at two dates `s ≤ t`, the geometric average
`√(S_s·S_t)` is lognormal, because its log-driver — the **average of the Brownian values**
`(B_s + B_t)/2` — is Gaussian with the covariance-sum variance

  `Var((B_s + B_t)/2) = (s + 2·min(s,t) + t)/4 = (3s + t)/4`   (for `s ≤ t`).

The law is the two-date case of the `n`-date driver `geomAsianN_driver_hasLaw`
(`Models/BlackScholes/AsianGeometricN.lean`), which reads the average of Brownian values as a Wiener
integral of a step kernel; here the dates are `![s, t]` and the covariance sum is `3s + t`.

## Main results

* `asianGeom_driver_hasLaw` — `(B_s + B_t)/2 ~ N(0, (3s+t)/4)` for `s ≤ t`.

## Tags

geometric Asian option, average price option, Wiener integral, lognormal, Gaussian average,
effective variance, MSC 91G20, MSC 60J65, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **The two-date geometric-Asian log-driver is Gaussian.** For a pre-Brownian motion `B`
and sampling dates `s ≤ t ≤ T`, the average of the Brownian values `(B_s + B_t)/2` — the
Gaussian part of the log geometric average `log √(S_s·S_t)` — has the centred Gaussian law
`N(0, (3s+t)/4)`, the variance coming from the Brownian covariance `∫ B_s·B_t = min(s,t)`. -/
theorem asianGeom_driver_hasLaw (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    {s t : ℝ≥0} (hst : s ≤ t) (hsT : s ≤ T) (htT : t ≤ T) :
    HasLaw (fun ω ↦ (B s ω + B t ω) / 2)
      (gaussianReal 0 ((3 * (s : ℝ) + t) / 4).toNNReal) μ := by
  have h := geomAsianN_driver_hasLaw hB T (n := 2) two_pos ![s, t]
    (fun i ↦ by fin_cases i <;> simpa)
  have hst' : (s : ℝ) ≤ t := hst
  have hf : (fun ω ↦ (∑ i, B (![s, t] i) ω) / ((2 : ℕ) : ℝ)) = fun ω ↦ (B s ω + B t ω) / 2 := by
    funext ω; simp [Fin.sum_univ_two]
  have hv : (∑ i, ∑ j, min ((![s, t] i : ℝ≥0) : ℝ) ((![s, t] j : ℝ≥0) : ℝ)) / ((2 : ℕ) : ℝ) ^ 2
      = (3 * (s : ℝ) + t) / 4 := by
    simp [Fin.sum_univ_two, min_eq_left hst', min_eq_right hst']; ring
  rw [hf, hv] at h
  exact h

end MathFin
