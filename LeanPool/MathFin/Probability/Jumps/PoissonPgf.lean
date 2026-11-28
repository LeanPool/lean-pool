/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# The Poisson probability generating function

Mathlib's `poissonMeasure` (the Poisson distribution over `ℕ`) ships the
normalisation `hasSum_one_poissonMeasure` but no generating function: there
is no lemma computing `E[x^N]` for `N ∼ Poisson(r)`. This file proves it:

  `∫ n, x ^ n ∂(poissonMeasure r) = exp (r · (x − 1))`   for every `x : ℝ`,

together with the underlying `HasSum`/`tsum` forms of the weighted series
`∑ₙ e^{−r} rⁿ/n! · xⁿ = e^{r(x−1)}`. The proof is the exponential series at
`r·x` rescaled by `e^{−r}` — the same `NormedSpace.expSeries_div_hasSum_exp`
route Mathlib itself uses for the normalisation, so the identity holds for
*all* real `x` (absolute convergence everywhere), not just `|x| ≤ 1`.

The pgf is the engine behind compensation ("recombination") identities for
Poisson mixtures: in `Models/Jumps/MertonJumpDiffusion.lean` it is what makes
the jump-compensated conditional spots average back to the true spot
(`E[S₀ e^{−kΛ}(1+k)^N] = S₀`) — Merton's risk-neutral consistency condition.

## Main results

* `PoissonPgf.hasSum_poisson_weights_mul_pow` — the `HasSum` form.
* `PoissonPgf.tsum_poisson_weights_mul_pow` — the `tsum` form.
* `PoissonPgf.integral_pow_poissonMeasure` — the pgf `E[x^N] = e^{r(x−1)}`.
* `PoissonPgf.integrable_pow_poissonMeasure` — `n ↦ xⁿ` is integrable against `Poisson(r)`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Ch 3

## Tags

probability generating function, Poisson distribution, Poisson mixture, jump compensation,
Merton jump diffusion, MSC 60E10, MSC 60G55
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

namespace PoissonPgf

/-- **Weighted Poisson series** (`HasSum` form): for every `x : ℝ`,
`∑ₙ e^{−r} rⁿ/n! · xⁿ = e^{r(x−1)}` — absolute convergence included, this
being the exponential series at `r·x` rescaled by `e^{−r}`. -/
lemma hasSum_poisson_weights_mul_pow (r : ℝ≥0) (x : ℝ) :
    HasSum (fun n : ℕ ↦ rexp (-(r : ℝ)) * (r : ℝ) ^ n / n ! * x ^ n)
      (rexp ((r : ℝ) * (x - 1))) := by
  convert (NormedSpace.expSeries_div_hasSum_exp ((r : ℝ) * x)).mul_left
    (rexp (-(r : ℝ))) using 1 <;>
    first
      | (funext n; rw [mul_pow]; ring)
      | (rw [← exp_eq_exp_ℝ, ← Real.exp_add]; congr 1; ring)

/-- **Weighted Poisson series** (`tsum` form). -/
lemma tsum_poisson_weights_mul_pow (r : ℝ≥0) (x : ℝ) :
    ∑' n : ℕ, rexp (-(r : ℝ)) * (r : ℝ) ^ n / n ! * x ^ n
      = rexp ((r : ℝ) * (x - 1)) :=
  (hasSum_poisson_weights_mul_pow r x).tsum_eq

/-- **Poisson probability generating function**: `E[x^N] = e^{r(x−1)}` for
`N ∼ Poisson(r)` and every `x : ℝ`. Stated as an honest expectation against
`poissonMeasure`; no integrability hypothesis is needed since the codomain
is finite-dimensional (`integral_poissonMeasure`). -/
theorem integral_pow_poissonMeasure (r : ℝ≥0) (x : ℝ) :
    ∫ n, x ^ n ∂(poissonMeasure r) = rexp ((r : ℝ) * (x - 1)) := by
  rw [integral_poissonMeasure r (fun n ↦ x ^ n)]
  simp_rw [smul_eq_mul]
  exact tsum_poisson_weights_mul_pow r x

/-- `n ↦ xⁿ` is integrable against `Poisson(r)` for every `x : ℝ`: the weighted absolute values
`∑ₙ e^{−r} rⁿ/n! · |x|ⁿ` sum to `e^{r(|x|−1)}`. -/
lemma integrable_pow_poissonMeasure (r : ℝ≥0) (x : ℝ) :
    Integrable (fun n : ℕ ↦ x ^ n) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  simp_rw [norm_pow, Real.norm_eq_abs]
  exact (hasSum_poisson_weights_mul_pow r |x|).summable

end PoissonPgf

end MathFin
