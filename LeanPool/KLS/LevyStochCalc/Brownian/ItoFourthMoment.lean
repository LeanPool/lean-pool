/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFourthMomentIncrements
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFourthMomentPartialSums
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFourthMomentLintegral

/-!
# Fourth moment of the elementary Brownian integral

The moments of a Brownian increment, and the fourth-moment bound they give for the elementary
integral of a uniformly bounded simple integrand. The bound comes from a recursion over the
partial sums: the odd-power cross terms drop out because a coefficient measurable before an
increment is independent of it, and the surviving terms are controlled by the second moment of
the partial sums, itself bounded by the same recursion.

## Main statements

* `integral_pow_gaussianReal_zero` — the moments of a centred real Gaussian scale with the
  standard deviation.
* `integral_pow_gaussianReal_odd` — the odd moments of the standard real Gaussian vanish.
* `integral_increment_sq`, `integral_increment_pow_four` — the second and fourth moments of a
  Brownian increment.
* `integral_mul_increment_pow` — a random variable measurable before `a` factors out of the
  integral against a power of the increment over `(a, b]`.
* `memLp_increment`, `memLp_mul_increment` — a Brownian increment, and a bounded random
  variable times one, have moments of every order.
* `SimplePredictable.partialSum` — the partial sums of the elementary integral.
* `SimplePredictable.integral_partialSum_sq_le`,
  `SimplePredictable.integral_partialSum_pow_four_le` — the second and fourth moments of the
  partial sums.
* `SimplePredictable.integral_simpleIntegral_pow_four_le_horizon` —
  `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·C⁴·T²` for a simple integrand bounded by `C`, where `c` is the
  fourth moment of the standard Gaussian.
* `SimplePredictable.varClock` — the variance budget `∑_{j<k} c_j² (τ_{j+1} − τ_j)` of a
  per-tile coefficient bound `c`, with
  `SimplePredictable.integral_simpleIntegral_pow_four_le_varClock`:
  `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·(∑_j c_j² Δ_j)²`, which for a coefficient vanishing off a
  subinterval sees only that subinterval's length.
* `SimplePredictable.truncate` — the coefficients of a simple integrand clamped to `[-C, C]`,
  with `abs_clamp_sub_le`: clamping moves a value no further from a target already in `[-C, C]`,
  so a truncated approximant is still an approximant.
* `lintegral_stochasticIntegralBrownian_pow_four_le` — the same bound for the `L²` Itô integral
  of any integrand bounded by `C`, by Fatou along an almost-everywhere convergent subsequence of
  truncated simple approximants.

The material is split over three files, all re-exported here:

* `LevyStochCalc.Brownian.ItoFourthMomentIncrements` — the Gaussian and Brownian increment
  moments, the partial sums of the elementary integral and the variance budget `varClock`;
* `LevyStochCalc.Brownian.ItoFourthMomentPartialSums` — the second- and fourth-moment recursions
  for the partial sums and the resulting bounds for the elementary integral;
* `LevyStochCalc.Brownian.ItoFourthMomentLintegral` — truncation of a simple integrand and the
  `lintegral` form of the bound, up to the `L²` Itô integral.
-/
