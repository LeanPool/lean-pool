/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Tactic.Positivity.Basic  -- shake: keep (positivity extensions)
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring.RingNF

/-!
# Black-Litterman one-dimensional Bayesian update

In the Black-Litterman framework, expected returns `μ` are updated from a
prior `μ ~ N(π, τΣ)` by combining with views `P μ = Q + ε`, `ε ~ N(0, Ω)`. The
posterior is a precision-weighted Gaussian. In one dimension (single asset,
single view directly on `μ`) this reduces to the classical
Gaussian-conjugate update:

  `posterior_mean = (s1sq π + s0sq Q) / (s0sq + s1sq)`,
  `posterior_var  = s0sq s1sq / (s0sq + s1sq)`,

where `s0sq` is the prior variance and `s1sq` the view's observation noise. The
result is the harmonic mean of variances; equivalently, the precision
(`1/σ²`) is additive. Both extreme limits behave correctly:

* `s1sq → 0` (perfect view): posterior_mean → `Q`,
* `s1sq → ∞` (uninformative view): posterior_mean → `π`.

## Main definitions

* `posteriorMean1d`: the one-dimensional Black-Litterman posterior mean
  `(s1sq·π + s0sq·Q) / (s0sq + s1sq)`.
* `posteriorVariance1d`: the posterior variance `s0sq·s1sq / (s0sq + s1sq)`.

## Main results

* `blackLitterman_mean_eq_precision_weighted`: for positive variances, equivalence of the
  precision-weighted form with the symmetric form.
* `blackLitterman_var_eq_inv_sum_precision`: for positive variances, equivalence with the
  inverse-sum-of-precisions form.

## References

* [Black and Litterman, *Global portfolio optimization*][BlackLitterman1992]

## Tags

Black-Litterman model, Bayesian update, posterior mean, investor views, precision weighting,
Gaussian conjugate, MSC 91G10, MSC 62F10, JEL G11
-/

@[expose] public section

namespace MathFin

/-- One-dimensional Black-Litterman posterior mean. -/
noncomputable def posteriorMean1d (π Q s0sq s1sq : ℝ) : ℝ :=
  (s1sq * π + s0sq * Q) / (s0sq + s1sq)

/-- One-dimensional Black-Litterman posterior variance. -/
noncomputable def posteriorVariance1d (s0sq s1sq : ℝ) : ℝ :=
  s0sq * s1sq / (s0sq + s1sq)

/-- **Posterior mean is precision-weighted**: equivalence of the symmetric
form `(s1sqπ + s0sqQ)/(s0sq + s1sq)` with the standard precision-weighted form
`(π/s0sq + Q/s1sq)/(1/s0sq + 1/s1sq)`. -/
theorem blackLitterman_mean_eq_precision_weighted
    (π Q s0sq s1sq : ℝ) (h₀ : 0 < s0sq) (h₁ : 0 < s1sq) :
    posteriorMean1d π Q s0sq s1sq =
      (π / s0sq + Q / s1sq) / (1 / s0sq + 1 / s1sq) := by
  unfold posteriorMean1d
  have h₀_ne : s0sq ≠ 0 := h₀.ne'
  have h₁_ne : s1sq ≠ 0 := h₁.ne'
  have hsum : s0sq + s1sq ≠ 0 := by positivity
  field_simp
  ring

/-- **Posterior variance is harmonic combination of inputs**: equivalence
`s0sqs1sq/(s0sq+s1sq) = 1/(1/s0sq + 1/s1sq)`, i.e. precision is additive. -/
theorem blackLitterman_var_eq_inv_sum_precision
    (s0sq s1sq : ℝ) (h₀ : 0 < s0sq) (h₁ : 0 < s1sq) :
    posteriorVariance1d s0sq s1sq = 1 / (1 / s0sq + 1 / s1sq) := by
  unfold posteriorVariance1d
  have h₀_ne : s0sq ≠ 0 := h₀.ne'
  have h₁_ne : s1sq ≠ 0 := h₁.ne'
  field_simp
  ring

/-- **Convex combination form**: posterior mean lies between the prior `π`
and the view `Q`, with weights `λ := s0sq/(s0sq+s1sq)` and `1−λ`. -/
theorem blackLitterman_mean_convex_combination
    (π Q s0sq s1sq : ℝ) (h_sum : s0sq + s1sq ≠ 0) :
    posteriorMean1d π Q s0sq s1sq =
      (1 - s0sq / (s0sq + s1sq)) * π + (s0sq / (s0sq + s1sq)) * Q := by
  unfold posteriorMean1d
  field_simp
  ring

end MathFin
